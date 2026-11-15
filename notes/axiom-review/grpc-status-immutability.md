# grpc's `*Status` immutability: a latent assumption of `status.FromError` and `status.Code` (2026-11-15)

Found by the E1 review of k8s 7f-5a-P (`notes/k8s-7f5a-draft.md` §11); decided by etcd-grove-81:
latent, not urgent, fixed in the E1 trusted-text package (drafted in §11, not applied).

## The assumption

`status.FromError.wp_proof` and `status.Code.wp_proof` (axioms, `Proof/google_golang_org/grpc/status/`)
take `statusErrOk err`. Through `grpcErrMethodsOk` (`Proof/go_etcd_io/etcd/cache/v3/Base.lean`) that
says only that `GRPCStatus()` returns one fixed `s : Loc`: no ownership of `*s`, nothing of its
contents. Both functions read `*s` (`s.Proto()` clones `s.s`), and `FromError`'s post says the result's
`Code()` returns `statusCode err`, a fixed Lean function of the error value. That is sound only if
nobody writes `*s`: `grpcErrMethodsOk`'s docstring says "grpc's `*Status` is immutable: `Proto()`
clones, nothing exported writes it", which is false of Go: assigning a whole struct copies its
unexported fields.

## Counterexample sketch (Go; not provable in the current tree)

```go
type myErr struct{ s *status.Status }
func (e myErr) Error() string               { return "x" }
func (e myErr) GRPCStatus() *status.Status  { return e.s }

s := status.New(codes.Canceled, "x")
e := myErr{s}
c1 := status.FromError(e) // reads *s
*s = *status.New(codes.OK, "")
c2 := status.FromError(e)
if c1.Code() != c2.Code() { panic("differs") } // panics in Go; the axiom gives both statusCode e
```

Sequential, no race. A concurrent `*s = ...` races with `FromError`'s and `Code`'s reads instead (the
reviewer's `TestE1Race`, `go test -race` reports it; a racy access is undefined in the model).

## Why it is latent

grpc's `internal/status.Status` is an axiomatized type: its `TypedPointsto` and `IntoValTyped`
instances are `sorry -- axiomatized type` (`GeneratedProof/google_golang_org/grpc/internal/status.lean`).
**No sorry-free proof can allocate, load or store a `*Status`** (`new(status.Status)`, `*s = *t`), so
the program above has no proof without a `sorry`, and no linked result reaches those instances
(`etc/tcb-report.py`). Should grpc's `Status` ever be translated as a struct, the assumption becomes
exploitable: the E1 package must land first.

## The fix (E1 package, `notes/k8s-7f5a-draft.md` §11)

`grpcErrMethodsOk`'s `GRPCStatus` conjunct carries `□` facts of the returned `s` (`Code()` returns
`statusCode`, `Message()` returns `errDesc`), supplied by the producers that build a status fresh
(`status.Error.spec`, the invoker and stream texts); `FromError` and `Code` take them from their
premise; `Base.lean`'s docstring corrected.
