mod mime;

use std::{
    convert::Infallible,
    env::current_dir,
    fmt::{Display, Formatter},
    fs::File,
    io::{sink, BufRead, BufReader, ErrorKind, Read, Seek, SeekFrom, Write},
    net::{Ipv4Addr, SocketAddr, TcpListener, TcpStream},
    path::{Component, Path, PathBuf}
};
use mime::path_to_mime_type;

fn relative_path_components(path: &Path) -> impl Iterator<Item = impl AsRef<Path> + '_> {
    path.components().flat_map(|comp| if let Component::Normal(r) = comp {
        Some(r)
    } else {
        None
    })
}

pub type Result<T = (), E = std::io::Error> = std::result::Result<T, E>;
const OK: Result = Ok(());

/// Server for serving files locally
pub struct Server {
    root: PathBuf,
    listener: TcpListener,
}

/// The result of a request.
/// This doesn't report IO errors, since in a case of such error no request is registered.
#[derive(Debug, Clone)]
pub enum RequestResult {
    /// Everything went normally and the client received a 200 response
    Ok(Box<Path>),
    /// Unsupported or invalid HTTP method was provided in the request;
    /// This crate only supports GET requests.
    InvalidHttpMethod,
    /// The request used something other than "\r\n" as a newline separator
    InvalidNewline,
    /// No path was provided in the request
    NoRequestedPath,
    /// Unsupported HTTP version provided in the request; this crate only;
    /// This crate only supports HTTP/1.1
    InvalidHttpVersion,
    /// Request file does not exist or is outside the root of the server.
    FileNotFound(Box<Path>),
}

impl Display for RequestResult {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        use RequestResult::*;
        match self {
            Ok(path) => write!(f, "requested file {path:?} successfully provided"),
            InvalidHttpMethod => write!(f, "unsupported/invalid HTTP method encountered"),
            InvalidNewline => write!(f, "invalid newline encountered"),
            NoRequestedPath => write!(f, "no path provided in the request"),
            InvalidHttpVersion => write!(f, "unsupported/invalid HTTP version encountered"),
            FileNotFound(path) => write!(f, "requested file {path:?} not found"),
        }
    }
}

impl Server {
    /// Chosen by fair dice roll;
    /// Guaranteed to be random.
    pub const DEFAULT_PORT: u16 = 6969;

    /// Create a new server for listening to HTTP connections at port [`Server::DEFAULT_PORT`]
    /// and serving files from the current directory.
    /// <br /> If a custom port needs to be provided, use [`Server::new_at`];
    /// <br /> If a custom root needs to be provided, use [`Server::new`].
    pub fn current_dir() -> Result<Self> {
        Self::_new(current_dir()?, Self::DEFAULT_PORT)
    }

    /// Create a new server for listening to HTTP connections at port [`Server::DEFAULT_PORT`]
    /// and serving files from `root`.
    /// <br /> If a custom port needs to be provided, use [`Server::new_at`];
    /// <br /> If `root` is only ever supposed to be the current directory, use [`Server::current_dir`].
    pub fn new(root: impl AsRef<Path>) -> Result<Self> {
        Self::_new(root.as_ref().canonicalize()?, Self::DEFAULT_PORT)
    }

    /// Create a new server for listening to HTTP connections at port `port`
    /// and serving files from the current directory.
    /// <br /> If it doesn't matter what port is used, use [`Server::current_dir`];
    /// <br /> If a custom root needs to be provided, use [`Server::new_at`].
    pub fn current_dir_at(port: u16) -> Result<Self> {
        Self::_new(current_dir()?, port)
    }

    /// Create a new server for listening to HTTP connections at `addr`
    /// and serving files from `root`.
    /// <br /> If it doesn't matter what port is used, use [`Server::new`];
    /// <br /> If `root` is only ever supposed to be the current directory, use [`Server::current_dir_at`]
    pub fn new_at(root: impl AsRef<Path>, port: u16) -> Result<Self> {
        Self::_new(root.as_ref().canonicalize()?, port)
    }

    fn _new(root: PathBuf, port: u16) -> Result<Self> {
        Ok(Self { root, listener: TcpListener::bind((Ipv4Addr::LOCALHOST, port))? })
    }

    fn read_http_line(reader: &mut impl BufRead, dst: &mut String) -> Result<bool> {
        dst.clear();
        reader.read_line(dst)?;
        Ok(dst.pop().zip(dst.pop()) == Some(('\n', '\r')))
    }

    /// `content` is assumed to be in its starting position
    fn send_200(
        mut dst: impl Write,
        mut content: impl Read + Seek,
        content_type: impl Display,
    ) -> Result {
        let content_length = content.seek(SeekFrom::End(0))?;
        content.rewind()?;
        write!(dst, "HTTP/1.1 200 OK\r\n\
                     Connection: keep-alive\r\n\
                     Content-Type: {content_type}\r\n\
                     Content-Length: {content_length}\r\n\
                     \r\n")?;
        std::io::copy(&mut content, &mut dst)?;
        OK
    }

    fn send_404(mut dst: impl Write) -> Result {
        dst.write_all(b"HTTP/1.1 404 Not Found\r\n\
                        Connection: keep-alive\r\n\
                        Content-Type: text/html\r\n\
                        Content-Length: 18\r\n\
                        \r\n\
                        <h1>Not Found</h1>")
    }

    fn send_501(mut dst: impl Write) -> Result {
        dst.write_all(b"HTTP/1.1 501 Not Implemented\r\n")
    }

    /// This method only consumes the request-line.
    /// `line_buf` & `misc_buf` must be empty.
    fn respond(
        &mut self,
        conn: &mut BufReader<TcpStream>,
        line_buf: &mut String,
        misc_buf: &mut String,
    ) -> Result<RequestResult> {
        if !Self::read_http_line(conn, line_buf)? {
            std::io::copy(conn, &mut sink())?;
            return Ok(RequestResult::InvalidNewline)
        }
        loop {
            misc_buf.clear();
            if !Self::read_http_line(conn, misc_buf)? {
                std::io::copy(conn, &mut sink())?;
                return Ok(RequestResult::InvalidNewline)
            }
            if misc_buf.is_empty() {
                break;
            }
        }

        let Some(path_and_version) = line_buf.strip_prefix("GET ") else {
            Self::send_501(conn.get_mut())?;
            return Ok(RequestResult::InvalidHttpMethod)
        };
        let Some((path, http_version)) = path_and_version.split_once(' ') else {
            return Ok(RequestResult::NoRequestedPath)
        };
        if http_version != "HTTP/1.1" {
            return Ok(RequestResult::InvalidHttpVersion)
        }
        let path = if path == "/" {
            Path::new("index.html")
        } else {
            Path::new(path)
        };

        let mut n_comps = 0usize;
        self.root.extend(relative_path_components(path).inspect(|_| n_comps += 1));
        let actual_path = self.root.canonicalize().ok();
        for _ in 0 .. n_comps {
            self.root.pop();
        }
        let Some(actual_path) = actual_path.filter(|p| p.starts_with(&self.root)) else {
            Self::send_404(conn.get_mut())?;
            return Ok(RequestResult::FileNotFound(Box::from(path)))
        };

        let file = File::open(&actual_path)?;
        Self::send_200(conn.get_mut(), file, path_to_mime_type(&actual_path))?;

        Ok(RequestResult::Ok(actual_path.into()))
    }

    /// Handles exactly 1 connection, regardless of how many pending connections there currently
    /// are
    fn handle_conn(
        &mut self,
        mut on_new_conn: impl FnMut(&SocketAddr),
        mut on_request: impl FnMut(&SocketAddr, RequestResult),
        mut on_conn_close: impl FnMut(&SocketAddr),
    ) -> Result {
        let (conn, addr) = self.listener.accept()?;
        on_new_conn(&addr);
        let mut conn = BufReader::new(conn);
        let mut line_buf = String::new();
        let mut misc_buf = String::new();
        loop {
            match self.respond(&mut conn, &mut line_buf, &mut misc_buf) {
                Ok(result) => on_request(&addr, result),
                Err(err) if err.kind() == ErrorKind::ConnectionReset => break,
                Err(err) => return Err(err),
            }
        }
        on_conn_close(&addr);
        OK
    }

    /// Serve all connections sequentially & indefinitely, returning only on an error, calling:
    /// - `on_new_conn` when a new connection is established;
    /// - `on_request` when a new request has been processed;
    /// - `on_conn_close` when a connection has been closed by the client.
    /// If no observation of connections/requests is needed, consider using [`Server::serve`]
    pub fn serve_with_callback(
        &mut self,
        mut on_new_conn: impl FnMut(&SocketAddr),
        mut on_request: impl FnMut(&SocketAddr, RequestResult),
        mut on_conn_close: impl FnMut(&SocketAddr),
    ) -> Result<Infallible> {
        loop {
            self.handle_conn(&mut on_new_conn, &mut on_request, &mut on_conn_close)?
        }
    }

    /// Serve all connections sequentially & indefinitely, returning only on an error. <br />
    /// If connections/requests need to be observed (e.g. logged), use
    /// [`Server::serve_with_callback`]
    pub fn serve(&mut self) -> Result<Infallible> {
        self.serve_with_callback(|_| (), |_, _| (), |_| ())
    }
}

/// Serve files from the current directory at port [`Server::DEFAULT_PORT`]
/// If a custom port needs to be provided, use [`serve_current_dir_at`];
/// If a custom root needs to be provided, use [`serve`].
pub fn serve_current_dir() -> Result<Infallible> {
    Server::current_dir()?.serve()
}

/// Serve files from `root` at port [`Server::DEFAULT_PORT`]
/// If a custom port needs to be provided, use [`serve_at`];
/// If `root` is only ever supposed to be the current directory, use [`serve_current_dir`].
pub fn serve(root: impl AsRef<Path>) -> Result<Infallible> {
    Server::new(root)?.serve()
}

/// Serve files from `root` at port [`Server::DEFAULT_PORT`]
/// If it doesn't matter what port is used, use [`serve_current_dir`];
/// If a custom root needs to be provided, use [`serve_at`].
pub fn serve_current_dir_at(port: u16) -> Result<Infallible> {
    Server::current_dir_at(port)?.serve()
}

/// Serve files from `root` at `addr`.
/// If it doesn't matter what port is used, use [`serve`];
/// If `root` is only ever supposed to be the current directory, use [`serve_current_dir_at`]
pub fn serve_at(root: impl AsRef<Path>, port: u16) -> Result<Infallible> {
    Server::new_at(root, port)?.serve()
}
