# `resolver.EtcdManualResolver.Close`: premise missing (prove-grpc3, 2026-11-21)

Found by reading the pinned code (etcd at the fork's pin, grpc v1.84.0), while proving the axiom over the
translated code; no Lean counterexample was built.

`Spec/go_etcd_io/etcd/client/v3/internal/resolver/EtcdManualResolver__Close.lean` said, for any `r : Loc`
with precondition `isPkgInit`, that `r.Close()` returns. `Close` is promoted from the embedded
`*manual.Resolver` (`client/v3/internal/resolver/resolver.go:31-35`; grpc `resolver/manual/manual.go:103-105`:
`func (r *Resolver) Close() { r.CloseCallback() }`): a nil `r` panics loading the `Resolver` field, a nil
embedded resolver or a nil `CloseCallback` panics too. The axiom proved such calls return: false as stated.
Only etcd's client calls it (the package is `internal`), on `New`'s result, where it does return
(`NewBuilderWithScheme` sets `CloseCallback: func() {}`, `manual.go:37`).

Fix (no axiom left): `Close` takes `etcdResolverCloser r` (`Proof/go_etcd_io/etcd/client/v3/InvClientNew.lean`:
half of `r.Resolver`, the manual resolver's `CloseCallback` and a WP that it returns), which `New`'s post gives;
`newClient` keeps it for the `Close` after a failed dial. `New`, `SetEndpoints` and `Close` are now proved over
grpc's `resolver/manual` translated with its bodies, and `etcdResolverOwn` is a definition.
