# `http.ReadAll_ok`: a reader's negative count (prove-http, 2026-11-20)

Found by reading go1.27.3's `io.ReadAll` against `http.ReadAll_spec` while triaging the HTTP
boundary's axioms for proofs; not by the `axiom` skill.

## `http.ReadAll_ok`: **false as stated, fixed**

`http.ReadAll_spec` (`Proof/net/http/Boundary.lean`) holds of any reader keeping
`http.prefixReaderOk rd Src B e`, whose `Read` post related the count `n` to the bytes read `ys` by
`ys.length = sint.nat n`. `sint.nat` is `(sint.Z n).toNat`, `0` for a negative `n`, so a reader
whose `Read` returns `(-1, nil)` and writes nothing kept the contract (with `ys = []`, of any `B`).
go1.27.3 `io/io.go:722-723`:

```go
n, err := r.Read(b[len(b):cap(b)])
b = b[:len(b)+n]
```

panics with `slice bounds out of range [:-1]` on the first such read, while the axiom proved
`io.ReadAll` returns. `examples/premisefix/negread` runs it.

Fix: `prefixReaderOk`'s count is `sint.Z n = ys.length` (as `io.readerStream`'s,
`Proof/io/ReaderStream.lean`), so `n ≥ 0`. Its producers:

- `http.bodyReader_prefixOk`, from `http.bodyRead_spec`, whose post now states the count the same way
  (a strengthening of the trust-boundary axiom `http.bodyRead_ok`'s post: Go's server body reader
  keeps `io.Reader`'s `0 <= n <= len(p)`);
- `ioutil.NewLimitedBufferReader`'s proof, which passes its reader's count through.

Not reachable from etcd: rafthttp reads request bodies through Go's server body reader. Not fixed
(no `io` function applied to them panics on a negative count): `http.streamReaderOk` and
`http.bodyStreamRead_spec` keep `ys.length = sint.nat n`.
