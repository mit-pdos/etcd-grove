# `fmt.SprintfClientPtr`: any format admitted for a `*clientv3.Client` (prove-reflectfmt, 2026-11-20)

Found by reading the pinned code (go1.27.3 `fmt/print.go`; etcd at the fork's pin), while triaging the
`fmt` trust boundary; confirmed by a Go test, `examples/axiomcx/sprintfclientptr`.

## The axiom, as it stood

`Spec/fmt/SprintfClientPtr.lean`: `fmt.Sprintf(format, args...)` returns, with `SprintfOut format xs s`,
for **any** `format` and arguments that are each `nil`, `fmt.ArgWf`, or a `*clientv3.Client`, with no
ownership of the client. Its docstring argued that `*Client` has no `Error`, `String`, `Format` or
`GoString` method, "so that Go formats it by its kind (a pointer: `%p` its address, `%v` too)".

## Why it is false

The method set is not what matters for a pointer to a struct. Under `%v`, `%s` (and any verb but
`%p`/`%T`), and as an `EXTRA` argument (printed under `%v`), Go formats a non-nil pointer to a struct
at depth 0 by printing the struct's fields (`printValue`, `print.go:902-911`: `&` then the fields), and
at depth 1 calls `handleMethods` on every field it can `Interface()` (`print.go:756-763`): the values
of `Client`'s exported fields (the embedded `KV`, `Watcher`, `Lease`, ... interfaces, `Username`). So
`Sprintf("%v", c)` reads all of `*c` and calls the `String`/`Error` methods of the dynamic values in
its exported interface fields, none of which the precondition owns or specifies: with a concurrent
writer of `c.Username` (the writer holds the points-to; the axiom needs none) it is a data race on a
two-word string, which Go may tear (a crash), and the methods called may do anything. The test builds a
real `clientv3.Client` whose `KV` has a `String()` and shows `%v` and an `EXTRA` call it, while `%p`
calls nothing.

Only `%p` is safe: `printArg` handles `%p` before anything else (`print.go:686-693`), printing the
address (`fmtPointer`), with no method call and no read through the pointer.

## Reachability

Latent: the one caller, clientv3's `dial` (`client.go:327`, `Sprintf("%s://%p/%s", resolver.Schema, c,
authority(...))`), formats the client with `%p`.

## Fix

The premise is now directive-aware (`fmt.SprintfClientArgsOk format xs`, in the style of
`fmt.argsOk`): the format's directives parse (`fmt.fmtDirectives`, which refuses `*` and argument
indexes, so each directive consumes the next argument), and each argument is `nil`, `fmt.ArgWf`, or a
`*clientv3.Client` **under a directive whose verb is `p`** (`fmt.SprintfClientArgOkAt`); arguments left
over are checked under `%v`, so a `*Client` cannot be an `EXTRA`. The post is unchanged. `Client.dial`
discharges it from the literal format. Ledger: `notes/specs-only/ledger.md`, 2026-11-20.
