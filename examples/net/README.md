# The TCP examples

Minimal Go programs over `net`'s TCP connections, verified end to end over the TCP extension
(`GooseLang/Ext/Tcp/Impl.lean`, its header states the semantics; project `nettcp` of
`etc/goose.py`, translated into the part `NetTcp/`). They are the extension's adequacy target:
each uses `net.Conn` the way a real client of `net` does (net/http, grpc-go), and its
correctness checks are `panic`s that the proof shows never fire, under every behavior the
semantics allows: a read may return fewer bytes than asked, an operation may fail at any time, a
node may crash (the bytes it wrote stay in flight; its connections send no FIN).

| Package | Client pattern it mirrors | Nodes | Check |
|---|---|---|---|
| `echo` | a request on a fresh connection (net/http's first request on a new connection, a grpc unary call) | `Server`, `Client`, `Junk` | the reply, read in full, is the request |
| `framed` | several length-prefixed messages on one persistent connection (HTTP/1.1 keep-alive, grpc's length-prefixed messages) | `Server`, `Client`, `Junk` | each of three replies is its request |
| `acceptloop` | an accept loop with a goroutine per connection (`http.Server.Serve`, `grpc.Server.Serve`) | `Server`, `Client` (two concurrent callers) | each caller gets its own id back |
| `duplex` | a reader and a writer goroutine on one connection (grpc's reader and loopyWriter; net/http's `persistConn` readLoop and writeLoop) | `Server`, `Client` | the bytes 1..4 come back in order |
| `halfclose` | `CloseWrite` and reading until EOF (net/http's `closeWriteAndWait`, close-delimited bodies) | `Server`, `Client` | the response read until EOF is a prefix of the request (EOF does not mean the writer finished: a killed process's kernel sends a FIN) |
| `shutdown` | closing a listener under a blocked `Accept`, a connection under a blocked `Read` (`http.Server.Shutdown`, `grpc.Server.GracefulStop`, `http2Client.Close`) | `Node` | every operation after `Close` fails |
| `preface` | a handshake read under a deadline, then the deadline cleared (grpc's `handleRawConn` and client preface) | `Server`, `Client`, `Junk` | the reply after the preface is the request |

`wire` holds the shared helpers: `wire.ReadFull` (io.ReadFull's loop over `Read`) and
`wire.Forever`.

## Conventions

- **Every node's boot program ends with `wire.Forever()`.** A node is a process that never exits.
  A process that exits has Go's runtime close its sockets, which sends a FIN on each open
  connection; the semantics does not model that (a FIN is sent only by `Close` or `CloseWrite` of
  an end not broken), so a theorem says nothing of a program that exits. Each boot program
  (`Server`, `Client`, `Junk`, `Node`) is its exported body (`Serve`, `Call`, `SendJunk`, `Run`)
  followed by `wire.Forever()`; the tests call the bodies.
- **Addresses.** Each example has its own address constants, `127.0.0.1:71xx`, distinct across
  all the examples (the deployment's plan names each address and the node that listens at it;
  distinct ports also let the packages' tests run in parallel): `echo` 7101, `framed` 7102,
  `acceptloop` 7103, `duplex` 7104, `halfclose` 7105, `shutdown` 7106, `preface` 7107. The next
  example takes 7108.
- **Errors are opaque**: the programs test only `err != nil`, `err == nil` and `err == io.EOF`.
- **Tests** (`<name>_test.go`) run the bodies over real TCP on localhost in one process: the
  server's body in a goroutine started once per process (it never returns), the client's in the
  test, with junk clients where the example has them.
