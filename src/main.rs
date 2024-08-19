use std::{env::{args_os, current_dir}, fmt::{Debug, Display, Formatter}, path::PathBuf};
use shrimple_localhost::{print_request_result, Server};

// #[derive(Display, From)] // :c
enum Error {
    Io(std::io::Error),
    User(&'static str),
}

impl Display for Error {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::Io(err) => Display::fmt(&err, f),
            Error::User(msg) => f.write_str(msg),
        }
    }
}

impl Debug for Error {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&self, f)
    }
}

impl From<&'static str> for Error {
    fn from(value: &'static str) -> Self {
        Self::User(value)
    }
}

impl From<std::io::Error> for Error {
    fn from(value: std::io::Error) -> Self {
        Self::Io(value)
    }
}

fn parse_args() -> Result<Option<(PathBuf, u16)>, Error> {
    let mut root = None;
    let mut port = None;
    let mut args = args_os();
    let program_name = args.next().ok_or("no program name provided")?
        .into_string().map_err(|_| "program name isn't valid UTF-8")?;
    while let Some(arg) = args.next() {
        match arg.as_encoded_bytes() {
            b"-h" | b"--help" => {
                println!("Localhost server\n\
                          \n\
                          Usage: {program_name} [OPTIONS]\n\
                          \n\
                          Options:\n\
                          \t-h, --help\n\
                          \t\tDisplay this message and exit\n\
                          \t-p, --port\n\
                          \t\tSpecify a port for the server to be at\n\
                          \t-r, --root\n\
                          \t\tSpecify the path at which the server will search for files\n");
                return Ok(None)
            }

            b"-p" | b"--port" => {
                port = args.next().ok_or("no port number provided after `-p`")?
                    .into_string().map_err(|_| "provided port number isn't valid UTF-8")?
                    .parse::<u16>().map_err(|_| "provided port number isn't a number")?
                    .into();
            }

            b"-r" | b"--root" => {
                root = Some(PathBuf::from(args.next().ok_or("no path provided after `-r`")?))
            }

            _ => {
                eprint!("extraneous arguments: [{arg:?}");
                for arg in args {
                    eprint!(", {arg:?}")
                }
                eprintln!("]");
                break
            }
        }
    }
    Ok(Some((root.map_or_else(current_dir, Ok)?, port.unwrap_or(Server::DEFAULT_PORT))))
}

fn main() -> Result<(), Error> {
    let Some((root, port)) = parse_args()? else {
        return Ok(())
    };
    println!("serving files from {root:?} at http://localhost:{port}/");
    Server::new_at(root, port)?.serve_with_callback(|_, path| path.into(), print_request_result)?;
    Ok(())
}
