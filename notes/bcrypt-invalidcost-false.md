# `bcrypt.GenerateFromPassword.wp_proof` is false: `InvalidCostError` as a `SafeMapKey` (found 2026-11-25)

A bug in this repository's own trust-boundary axiom (CLAUDE.md, "Issues in the verified code":
`notes/`, not `issues/`). Found by the review that found
[axiom-review/ctx-readerrs-vacuity.md](axiom-review/ctx-readerrs-vacuity.md), the same cause.

## What

`axiom bcrypt.GenerateFromPassword.wp_proof` (`Proof/golang_org/x/crypto/bcrypt/GenerateFromPassword.lean`,
spec `Spec/golang_org/x/crypto/bcrypt/GenerateFromPassword.lean`) posts, for every `cost : w64`, that a
non-nil error `ei` is either a pointer error or

```lean
((∀ T, ei.ty ≠ go.GoType.PointerType T) ∧ SafeMapKey (GF := GF) go.error err ∧
  ei.ty ≠ _root_.Perennial.context.deadlineExceededError.ty)
```

Since Perennial `293bcbdd8` (P8c), `SafeMapKey` at the default `MapKeys GoInterface` instance
(`mapKeys_interface`: `nil` or a pointer) has `key_ok`, so a non-pointer, non-nil interface is never
one: the second branch is `False`. The axiom therefore says that `GenerateFromPassword` never returns a
non-pointer error.

bcrypt v0.57.0 does (`bcrypt.go`): `GenerateFromPassword` calls `newFromPassword`, which calls
`checkCost(cost)`, which for `cost > MaxCost` (31) returns `InvalidCostError(cost)`, a `type
InvalidCostError int`: a non-pointer error. So a Go program that calls
`bcrypt.GenerateFromPassword(pw, 32)` and then panics has, from the axiom, a proof that it does not
panic (the error branch is unsatisfiable, the success branch is not taken). The axiom is false.

etcd itself never reaches it: `auth.NewAuthStore` replaces a cost outside `[MinCost, MaxCost]` by
`DefaultCost`, and `EtcdServer.UserAdd`'s proof calls bcrypt only with the store's cost. The
axiom, though, quantifies over every `cost`.

## Since when

The non-pointer branch with `SafeMapKey` dates from the auth plan's E3y (2026-10-27, after the pin
`f73703285`, `ee9054ae66`, 2026-10-26, brought P8c): false from the start. Reviewed in
[axiom-review/hs6.md](axiom-review/hs6.md) (2026-11-06), which checked the error list but not the
`SafeMapKey` conjunct's meaning after P8c.

## What it reaches

`EtcdServer.UserAdd`'s proof (`Proof/.../etcdserver/EtcdServer__UserAdd.lean`) and
`authStore.selectPassword`'s use it; every closed result over the server's `UserAdd`/auth path rests
on it (the `etcd/auth*` examples, `etcd_safe_single_process`, ...). Those are vacuous anyway through
[axiom-review/ctx-readerrs-vacuity.md](axiom-review/ctx-readerrs-vacuity.md) while they take `Hctx`.

## The fix

Branch `hctx-vacuity/2026-11-25`: the non-pointer branch restated as what bcrypt returns, an
`InvalidCostError` value (`ei.ty = bcrypt.InvalidCostError.ty ∧ ∃ c : w64, ei.v = #c`); the gRPC
layer's map lookup takes it as a key under its own `MapKeys` instance (see the sibling note).
