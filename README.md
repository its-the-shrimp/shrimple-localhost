# `serve_current_dir()`
Host your local files, e.g. for inspection by tools such as your trusty browser:
- On any platform,
- Without any additional dependencies,
- Without even executing any shell commands!
## Installation
Need it as a CLI?
```console
cargo install shrimple-localhost
```
Need it as a library?
```console
cargo add shrimple-localhost
```
## Usage
### CLI
Without any options, `shrimple-localhost` defaults to hosting the files in the current directory at the default port
```console
shrimple-localhost
```
- To specify a custom root, provide the `-r` flag followed by the path to the root
- To specify a custom port, provide the `-p` flag followed by the port number
```console
shrimple-localhost -p 4096 -r ~/website/static
```
### Library
More on this in the docs of the library: https://docs.rs/shrimple-localhost
