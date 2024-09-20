//! Zero-dependency simple synchronous localhost server.
//! The 2 ways to use the library are:
//! - [`serve_current_dir`], [`serve`], [`serve_current_dir_at`], [`serve_at`] functions, the simpler approach.
//! - [`Server`] struct, the more complex approach.
//!
//! If inspecting incoming connections & requests is needed (e.g. for logging), the 2nd approach
//! will be better, otherwise the 1st one will be easier.

mod mime;

use std::{
    convert::Infallible,
    env::current_dir,
    fmt::{Display, Formatter},
    fs::File,
    io::{BufRead, BufReader, Cursor, Error, ErrorKind, Read, Seek, SeekFrom, Write},
    net::{Ipv4Addr, SocketAddr, TcpListener, TcpStream},
    path::{Component, Path, PathBuf},
    time::UNIX_EPOCH,
};
use mime::path_to_mime_type;

fn relative_path_components(path: &Path) -> impl Iterator<Item = impl AsRef<Path> + '_> {
    path.components().filter_map(|comp| if let Component::Normal(r) = comp {
        Some(r)
    } else {
        None
    })
}

type Result<T = (), E = std::io::Error> = std::result::Result<T, E>;

/// Data associated with a successful request.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Request {
    /// Data that was sent to the client.
    pub sent: Response,
    /// Value of the `If-None-Match` header
    etag: Option<u64>,
}

impl Request {
    /// Returns a boolean indicating whether the client relied on their own cached version of the
    /// file;
    ///
    /// `true` means that the client provided an ETag that matched the current version of the file,
    /// and expectedly received a 304 "Not Modified" response without the contents of the file.
    pub fn client_cache_reused(&self) -> bool {
        self.etag.is_some()
    }
}

/// Server's response to a request.
///
/// To be emitted by a function provided to [`Server::serve_with_callback`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Response {
    /// Path to a local file to be sent.
    Path(PathBuf),
    /// Literal data to be sent.
    ///
    /// The MIME type of the data is assumed to be the same data as that of the file requested by
    /// the client.
    Data(Vec<u8>),
}

/// Made from [`Response`] to be sent to the client. Implements [`Read`].
enum ResponseReader<'response> {
    Path(File),
    Data(Cursor<&'response [u8]>),
}

macro_rules! fwd {
    { $(fn $name:ident (&mut $self:ident $(,)? $($arg:ident: $argty:ty),*) -> $ret:ty;)+ } => {
        $(
            fn $name(&mut $self, $($arg: $argty),*) -> $ret {
                match $self {
                    ResponseReader::Path(file) => file.$name($($arg),*),
                    ResponseReader::Data(file) => file.$name($($arg),*),
                }
            }
        )+
    }
}

impl Read for ResponseReader<'_> {
    fwd! {
        fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize>;
        fn read_exact(&mut self, buf: &mut [u8]) -> std::io::Result<()>;
        fn read_to_end(&mut self, buf: &mut Vec<u8>) -> std::io::Result<usize>;
        fn read_vectored(&mut self, bufs: &mut [std::io::IoSliceMut<'_>]) -> std::io::Result<usize>;
    }
}

impl Seek for ResponseReader<'_> {
    fwd! {
        fn seek(&mut self, pos: SeekFrom) -> std::io::Result<u64>;
        fn rewind(&mut self) -> std::io::Result<()>;
        fn seek_relative(&mut self, offset: i64) -> std::io::Result<()>;
        fn stream_position(&mut self) -> std::io::Result<u64>;
    }
}

impl From<PathBuf> for Response {
    fn from(value: PathBuf) -> Self {
        Self::Path(value)
    }
}

impl Response {
    /// Return a Displayable version of the response.
    ///
    /// If response data was fetched from the filesystem, the path is printed via
    /// [`Path::display`].
    ///
    /// Otherwise, "&lt;in-memory&gt;" is printed.
    pub fn display(&self) -> impl Display + '_ {
        struct ResponseDisplay<'path>(Option<std::path::Display<'path>>);

        impl Display for ResponseDisplay<'_> {
            fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
                match &self.0 {
                    Some(display) => write!(f, "{display}"),
                    None => f.write_str("<in-memory>"),
                }
            }
        }

        ResponseDisplay(match self {
            Response::Path(path) => Some(path.display()),
            Response::Data(_) => None,
        })
    }

    fn etag(&self) -> Result<Option<u64>> {
        Ok(match self {
            Self::Path(path) => path.metadata()?.modified()?
                .duration_since(UNIX_EPOCH)
                .map_err(|_| Error::other(format!("mtime of {path:?} is before the Unix epoch")))?
                .as_secs()
                .into(),
            Self::Data(_) => None,
        })
    }

    fn to_reader(&self) -> Result<ResponseReader<'_>> {
        Ok(match self {
            Self::Path(path) => ResponseReader::Path(File::open(path)?),
            Self::Data(vec) => ResponseReader::Data(Cursor::new(vec)),
        })
    }
}

/// The result of a request.
/// This doesn't report IO errors, since in a case of such error no request is registered.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RequestResult {
    /// Everything went normally and the client received a 200 response
    Ok(Request),
    /// Unsupported or invalid HTTP method was provided in the request.
    ///
    /// This crate only supports GET requests.
    InvalidHttpMethod,
    /// No path was provided in the request.
    NoRequestedPath,
    /// Unsupported HTTP version provided in the request.
    ///
    /// This crate only supports HTTP/1.1
    InvalidHttpVersion,
    /// One of the headers in the request was invalid.
    ///
    /// At the moment, this only triggers on an invalid `If-None-Match` header, the server ignores
    /// all other headers.
    InvalidHeader,
    /// Request file does not exist or is outside the root of the server.
    /// 
    /// Contained is the path as requested by the client ("/" is replaced with "/index.html")
    FileNotFound(Box<str>),
}

/// Error returned by [`Server::try_serve_with_callback`] that differentiates between an IO error from
/// within the server and an error propagated from a callback.
#[derive(Debug)]
pub enum ServerError<E> {
    Io(std::io::Error),
    Callback(E),
}

impl<E: Display> Display for ServerError<E> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            ServerError::Io(err) => write!(f, "IO error: {err}"),
            ServerError::Callback(err) => Display::fmt(err, f),
        }
    }
}

impl<E> From<std::io::Error> for ServerError<E> {
    fn from(value: std::io::Error) -> Self {
        Self::Io(value)
    }
}

impl<E: std::error::Error> std::error::Error for ServerError<E> {}

/// Server for serving files locally
pub struct Server {
    root: PathBuf,
    listener: TcpListener,
    line_buf: String,
    misc_buf: String,
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
        Ok(Self {
            root,
            listener: TcpListener::bind((Ipv4Addr::LOCALHOST, port))?,
            line_buf: String::new(),
            misc_buf: String::new(),
        })
    }

    fn read_http_line(reader: &mut impl BufRead, dst: &mut String) -> Result<()> {
        dst.clear();
        reader.read_line(dst)?;
        if dst.pop() == Some('\n') && dst.ends_with('\r') {
            dst.pop();
        }
        Ok(())
    }

    /// The boolean indicates whether the file was actually sent or if the client already has 
    /// the current version of the file in their cache
    fn send_file(
        &self,
        mut dst: impl Write,
        data: &Response,
        content_type: &'static str,
        etag_to_match: Option<u64>,
    ) -> Result<bool> {
        let etag = data.etag()?;
        if let Some(etag) = etag.filter(|&x| Some(x) == etag_to_match) {
            write!(dst, "HTTP/1.1 304 Not Modified\r\n\
                                Connection: close\r\n\
                                ETag: \"{etag:x}\"\r\n\
                                Cache-Control: public; must-revalidate\r\n\
                                \r\n")?;
            return Ok(false)
        }
        let mut file = data.to_reader()?;
        let content_length = file.seek(SeekFrom::End(0))?;
        file.rewind()?;
        write!(dst, "HTTP/1.1 200 OK\r\n\
                     Connection: close\r\n\
                     Content-Type: {content_type}\r\n\
                     Content-Length: {content_length}\r\n\
                     Cache-Control: public; must-revalidate\r\n")?;
        if let Some(etag) = etag {
            write!(dst, "ETag: \"{etag:x}\"\r\n")?;
        }
        write!(dst, "\r\n")?;
        std::io::copy(&mut file, &mut dst)?;
        Ok(true)
    }

    fn send_400(mut dst: impl Write) -> Result {
        write!(dst, "HTTP/1.1 400 Bad Request\r\n\
                     Connection: close\r\n\
                     \r\n")
    }

    fn send_404(mut dst: impl Write) -> Result {
        write!(dst, "HTTP/1.1 404 Not Found\r\n\
                     Connection: close\r\n\
                     Content-Type: text/html\r\n\
                     Content-Length: 18\r\n\
                     \r\n\
                     <h1>Not Found</h1>")
    }

    /// This method only consumes the request-line.
    fn respond<E>(
        &mut self,
        conn: &mut BufReader<TcpStream>,
    ) -> Result<RequestResult, ServerError<E>> {
        Self::read_http_line(conn, &mut self.line_buf)?;
        let mut etag = None;
        loop {
            Self::read_http_line(conn, &mut self.misc_buf)?;
            if let Some(etag_raw) = self.misc_buf.strip_prefix("If-None-Match: ") {
                etag = match u64::from_str_radix(etag_raw.trim_matches('"'), 16) {
                    Ok(x) => Some(x),
                    Err(_) => return Ok(RequestResult::InvalidHeader),
                }
            } else if self.misc_buf.is_empty() {
                break;
            }
        }

        let Some(path_and_version) = self.line_buf.strip_prefix("GET ") else {
            return Ok(RequestResult::InvalidHttpMethod)
        };
        let Some((path, http_version)) = path_and_version.split_once(' ') else {
            return Ok(RequestResult::NoRequestedPath)
        };
        if http_version != "HTTP/1.1" {
            return Ok(RequestResult::InvalidHttpVersion)
        }
        if path.contains("..") {
            return Ok(RequestResult::FileNotFound(Box::from(path)))
        }


        let path = match path.split_once('?').map_or(path, |(path, _query)| path) {
            "/" => "/index.html",
            _ => path,
        };
        let mut n_comps = 0usize;
        self.root.extend(relative_path_components(path.as_ref()).inspect(|_| n_comps += 1));
        let actual_path = self.root.canonicalize();
        for _ in 0 .. n_comps {
            self.root.pop();
        }
        let Ok(actual_path) = actual_path else {
            return Ok(RequestResult::FileNotFound(Box::from(path)))
        };

        Ok(RequestResult::Ok(Request { sent: Response::Path(actual_path), etag }))
    }

    fn handle_conn<E>(
        &mut self,
        conn: TcpStream,
        addr: &SocketAddr,
        mut on_pending_request: impl FnMut(&SocketAddr, PathBuf) -> Result<Response, E>,
        mut on_request: impl FnMut(&SocketAddr, RequestResult) -> Result<(), E>,
    ) -> Result<(), ServerError<E>> {
        let mut conn = BufReader::new(conn);

        while match conn.get_ref().peek(&mut [0; 4]) {
            Ok(n) => n > 0,
            Err(err) => match err.kind() {
                ErrorKind::ConnectionReset | ErrorKind::BrokenPipe => false,
                _ => return Err(err.into()),
            }
        } {
            let res = match self.respond(&mut conn) {
                Ok(RequestResult::Ok(Request { sent, mut etag })) => {
                    let Response::Path(path) = sent else {
                        unreachable!("Server::respond returned in-memory data instead of path");
                    };
                    let content_type = path_to_mime_type(&path);
                    let res = on_pending_request(addr, path).map_err(ServerError::Callback)?;
                    if self.send_file(conn.get_mut(), &res, content_type, etag)? {
                        etag = None;
                    }
                    RequestResult::Ok(Request { sent: res, etag })
                }

                Ok(RequestResult::FileNotFound(path)) => {
                    Self::send_404(conn.get_mut())?;
                    RequestResult::FileNotFound(path)
                }

                Ok(res @(| RequestResult::NoRequestedPath
                         | RequestResult::InvalidHeader
                         | RequestResult::InvalidHttpVersion
                         | RequestResult::InvalidHttpMethod)) => {
                    Self::send_400(conn.get_mut())?;
                    res
                }

                Err(ServerError::Io(err)) if err.kind() == ErrorKind::ConnectionReset => break,

                Err(err) => return Err(err),
            };
            on_request(addr, res).map_err(ServerError::Callback)?
        }
        Ok(())
    }

    /// Serve all connections sequentially & indefinitely, returning only on an error, calling:
    ///
    /// - `on_pending_request` when a new request is about to get a 200 response. The arguments to it are:
    ///     - IP of the sender of the request;
    ///     - Canonical path to the file that's about to be sent.
    ///
    /// It returns the data or the path to the file that's to be sent. To forward the choice of the
    /// server, return the second argument.
    ///
    /// - `on_request` when a new request has been processed. The arguments to it are:
    ///     - IP of the sender of the request;
    ///     - Result of the request.
    ///
    /// This function allows callbacks to return errors & disambiguates server errors & callback
    /// errors with the [`ServerError`] enum.
    ///
    /// If no such error propagation is needed, consider using [`Server::serve_with_callback`] <br/>
    /// If no observation of connections/requests is needed, consider using [`Server::serve`]
    pub fn try_serve_with_callback<E>(
        &mut self,
        mut on_pending_request: impl FnMut(&SocketAddr, PathBuf) -> Result<Response, E>,
        mut on_request: impl FnMut(&SocketAddr, RequestResult) -> Result<(), E>,
    ) -> Result<Infallible, ServerError<E>> {
        loop {
            let (conn, addr) = self.listener.accept()?;
            self.handle_conn(
                conn,
                &addr,
                &mut on_pending_request,
                &mut on_request,
            )?;
        }
    }

    /// Serve all connections sequentially & indefinitely, returning only on an IO error, calling:
    /// - `on_pending_request` when a new request is about to get a 200 response. The arguments to it are:
    ///     - IP of the sender of the request;
    ///     - Canonical path to the file on the machine.
    ///
    /// It returns the data or the path to the file that's to be sent. To forward the choice of the
    /// server, return the second argument.
    ///
    /// - `on_request` when a new request has been processed. The arguments to it are:
    ///     - IP of the sender of the request;
    ///     - Result of the request.
    ///
    /// This function allows callbacks to return errors & disambiguates server errors & callback
    /// errors with the [`ServerError`] enum.
    ///
    /// If no observation of connections/requests is needed, consider using [`Server::serve`] <br/>
    /// If the callbacks have to return an error, consider using [`Server::try_serve_with_callback`]
    pub fn serve_with_callback(
        &mut self,
        mut on_pending_request: impl FnMut(&SocketAddr, PathBuf) -> Response,
        mut on_request: impl FnMut(&SocketAddr, RequestResult),
    ) -> Result<Infallible> {
        self.try_serve_with_callback::<Infallible>(
            |addr, path| Ok(on_pending_request(addr, path)),
            |addr, req| Ok(on_request(addr, req)),
        ).map_err(|err| match err {
            ServerError::Io(err) => err,
            ServerError::Callback(err) => match err {},
        })
    }

    /// Serve all connections sequentially & indefinitely, returning only on an error. <br />
    /// Equivalent to [`serve`] function and the like.
    /// 
    /// If connections/requests need to be observed (e.g. logged), use
    /// [`Server::serve_with_callback`]
    pub fn serve(&mut self) -> Result<Infallible> {
        self.serve_with_callback(|_, path| path.into(), |_, _| ())
    }
}

/// Default function for printing the result of a request along with the IP from which it came.
/// Can be passed to [`Server::serve_with_callback`].
///
/// ```rust, no_run
/// use shrimple_localhost::{Server, print_request_result};
/// use std::convert::Infallible;
/// 
/// fn main() -> std::io::Result<Infallible> {
///     Server::current_dir()?.serve_with_callback(
///         |_, _| todo!(),
///         print_request_result,
///     )
/// }
/// ```
pub fn print_request_result(addr: &SocketAddr, res: RequestResult) {
    match res {
        RequestResult::Ok(req) if req.client_cache_reused() => 
            println!("{addr}:\n -> GET {}\n <- 304 Not Modified", req.sent.display()),
        RequestResult::Ok(req) => 
            println!("{addr}:\n -> GET {}\n <- 200 OK", req.sent.display()),
        RequestResult::InvalidHttpMethod =>
            println!("{addr}:\n -> <invalid HTTP method>\n <- 400 Bad Request"),
        RequestResult::NoRequestedPath => 
            println!("{addr}:\n -> <no requested path>\n <- 400 Bad Request"),
        RequestResult::InvalidHttpVersion =>
            println!("{addr}:\n -> <invalid HTTP version>\n <- 400 Bad Request"),
        RequestResult::InvalidHeader => 
            println!("{addr}:\n -> <invalid header(s)>\n <- 400 Bad Request"),
        RequestResult::FileNotFound(path) =>
            println!("{addr}:\n -> GET {path}\n <- 404 Not Found"),
    }
}

/// Serve files from the current directory at port [`Server::DEFAULT_PORT`]
///
/// - If a custom port needs to be provided, use [`serve_current_dir_at`]
/// - If a custom root needs to be provided, use [`serve`]
pub fn serve_current_dir() -> Result<Infallible> {
    Server::current_dir()?.serve()
}

/// Serve files from `root` at port [`Server::DEFAULT_PORT`]
///
/// - If a custom port needs to be provided, use [`serve_at`]
/// - If `root` is only ever supposed to be the current directory, use [`serve_current_dir`]
pub fn serve(root: impl AsRef<Path>) -> Result<Infallible> {
    Server::new(root)?.serve()
}

/// Serve files from `root` at port [`Server::DEFAULT_PORT`]
///
/// - If it doesn't matter what port is used, use [`serve_current_dir`]
/// - If a custom root needs to be provided, use [`serve_at`]
pub fn serve_current_dir_at(port: u16) -> Result<Infallible> {
    Server::current_dir_at(port)?.serve()
}

/// Serve files from `root` at `addr`
///
/// - If it doesn't matter what port is used, use [`serve`]
/// - If `root` is only ever supposed to be the current directory, use [`serve_current_dir_at`]
pub fn serve_at(root: impl AsRef<Path>, port: u16) -> Result<Infallible> {
    Server::new_at(root, port)?.serve()
}
