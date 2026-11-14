# The TCP examples

Minimal Go programs over `net`'s TCP connections, verified end to end over the TCP extension
(`GooseLang/Ext/Tcp/Impl.lean`, its header states the semantics; project `nettcp` of
`etc/goose.py`, translated into the part `NetTcp/`). They are the extension's adequacy target:
each uses `net.Conn` the way a real client of `net` does (net/http, grpc-go), and its
correctness checks are `panic`s that the proof shows never fire, under every behavior the
semantics allows: a read may return fewer bytes than asked, a connection may break at any
operation (a prefix of its unread bytes surviving), a node may crash or exit (the bytes it wrote
stay in flight; its kernel may FIN or reset its connections, which its peers see as a break).

Each node is a separate program, a command of its example (`cmd/server`, `cmd/client`, `cmd/junk`,
`cmd/node`), run as its own process; the example's top-level theorem (`<ex>_crash_safety`,
`NetTcp/Proof/github_com/mit_pdos/etcd_grove/examples/net/<ex>/Results.lean`) is the distributed
adequacy theorem of exactly those programs, and the package's process tests run them as separate
processes over real TCP.

| Package | Client pattern it mirrors | Nodes | Check |
|---|---|---|---|
| `echo` | a request on a fresh connection (net/http's first request on a new connection, a grpc unary call) | `server`, `client`, `junk` | the reply, read in full, is the request |
| `framed` | several length-prefixed messages on one persistent connection (HTTP/1.1 keep-alive, grpc's length-prefixed messages) | `server`, `client`, `junk` | each of three replies is its request |
| `acceptloop` | an accept loop with a goroutine per connection (`http.Server.Serve`, `grpc.Server.Serve`) | `server`, `client` (two concurrent callers) | each caller gets its own id back |
| `duplex` | a reader and a writer goroutine on one connection (grpc's reader and loopyWriter; net/http's `persistConn` readLoop and writeLoop) | `server`, `client` | the bytes 1..4 come back in order |
| `halfclose` | `CloseWrite` and reading until EOF (net/http's `closeWriteAndWait`, close-delimited bodies) | `server`, `client` | the response read until EOF is a prefix of the request (EOF does not mean the writer finished: a killed process's kernel sends a FIN) |
| `shutdown` | closing a listener under a blocked `Accept`, a connection under a blocked `Read` (`http.Server.Shutdown`, `grpc.Server.GracefulStop`, `http2Client.Close`) | `node` | every operation after `Close` fails |
| `preface` | a handshake read under a deadline, then the deadline cleared (grpc's `handleRawConn` and client preface) | `server`, `client`, `junk` | the reply after the preface is the request |

`wire` holds the shared helper `wire.ReadFull` (io.ReadFull's loop over `Read`);
`internal/proctest` runs a node's command as a process, for the tests.

## Conventions

- **Each node is a command**, `cmd/<node>/main.go`, whose `main` calls the example's body
  (`Serve`, `Call`, `SendJunk`, `Run`); its process may exit (a client does, once its check
  passed): the semantics covers what the peers then see (a process's exit or kill, its kernel's
  FIN or reset, is a break of its connections; `GooseLang/Ext/Tcp/Impl.lean`, D10, D11).
- **Addresses.** Each example has its own address constants, `127.0.0.1:71xx`, distinct across
  all the examples (the deployment's plan names each address and the node that listens at it;
  distinct ports also let the packages' tests run in parallel): `echo` 7101, `framed` 7102,
  `acceptloop` 7103, `duplex` 7104, `halfclose` 7105, `shutdown` 7106, `preface` 7107. The next
  example takes 7108.
- **Errors are opaque**: the programs test only `err != nil`, `err == nil` and `err == io.EOF`.
- **Tests** (`process_test.go`) build the example's commands and run each node as a separate
  process over real TCP on localhost (`internal/proctest`): the server's process, then the client
  nodes' processes, again and again, each required to exit 0 (a panic exits 2); and the server's
  process killed (SIGKILL) and restarted while client processes keep running, none of which may
  panic: the crash case of the theorem. A test never connects to the nodes itself (the theorems
  assume a closed world); it waits for a listener by reading `/proc/net/tcp`.
