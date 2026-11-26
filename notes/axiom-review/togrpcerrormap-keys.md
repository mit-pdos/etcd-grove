# `toGRPCErrorMap_init`: a map at Perennial's interface keys holding a struct key (false)

Found 2026-11-26 (grpcerrmap, zeldovich proving session 2), while translating and proving the axiom.

## The axiom

`Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/Init.lean` (until grpcerrmap) stated, for the
untranslated initializer of `toGRPCErrorMap` (`server/etcdserver/api/v3rpc/util.go:35-93`), a post
holding `mp ↦$□ M` (`M : GMap GoInterface GoInterface`) and

    □ (∀ g k, ⌜g ∈ grpcErrKeyGlobals⌝ → globalAddr g ↦□ k -∗ ⌜(M !! k).isSome⌝)

with `context.DeadlineExceeded ∈ grpcErrKeyGlobals`. The package fact `v3rpcInit` holds both
(`grpcErrMap`, `Base.lean`).

## Why it is false

`mp ↦$□ M` elaborates at Perennial's instance `mapKeys_interface` (`Perennial/Golang/Theory/Map.lean`:
an interface key is `nil` or a pointer), and `ownMap`'s `map.Repr` holds `MapKeys.keyOk` of every key.
Perennial's `context.isInit` (`#HDeadlineExceededTy`) gives
`globalAddr context.DeadlineExceeded ↦□ interface.mkOk deadlineExceededError.ty #(zero_val _)`: a struct,
neither `nil` nor a pointer. The wand applied to it says that struct is a key of `M`, so `M` has a key
that is not `keyOk`, contradicting `map.Repr`. The post (and `v3rpcInit`, given `context`'s fact) is
unsatisfiable: everything proved over it held vacuously from the moment the server's package facts were
in scope.

The real map does hold `deadlineExceededError{}` as a key (`util.go:91`, "In sync with
status.FromContextError"): it is Perennial's key class that is too narrow for this map, not the Go code
that is wrong. ctx-leaf-fix (2026-11-25) had introduced `v3rpc.errKeys` (the `errKeyOk` keys: `nil`,
pointers, `deadlineExceededError{}`, bcrypt's `InvalidCostError`) for `togRPCError`'s lookup, but left the
map owned at Perennial's keys.

## Fix

The map is owned at `v3rpc.errKeys` in `grpcErrMap` (`v3rpc/Base.lean`) and `grpcErrOut` (`InvKV.lean`);
`togRPCError` looks up with `v3rpc.wp_errMap_lookup2_at`. The initializer is translated and proved
(`v3rpc/ErrMapInit.lean`, `etc/gen-init.py`): its 53 inserts are `wp_mapInsert` at `errKeys`
(`safeMapKey_errKeys`), which is what makes the `DeadlineExceeded` insert provable at all. No caller used
the map at Perennial's keys beyond the lookup.
