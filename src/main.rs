use std::convert::Infallible;
use shrimple_localhost::Server;

fn main() -> std::io::Result<Infallible> {
    println!(
        "serving files from the current directory at \"http://localhost:{}/\"",
        Server::DEFAULT_PORT,
    );
    Server::current_dir()?.serve_with_callback(
        |addr| println!("Connection established with {addr}"),
        |addr, res| println!("Request processed from {addr}, result: {res}"),
        |addr| println!("Connection closed with {addr}"),
    )
}
