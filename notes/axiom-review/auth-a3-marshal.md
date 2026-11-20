# Review: `proto.MarshalUser` / `proto.MarshalRole` and the restated message predicates (auth-schema-srv A3)

Reviewed 2026-11-17 by the `axiom` skill, as an independent attacker (for etcd-grove-03), on branch
`auth-schema-srv` at `2ba77556da`: the texts of `notes/auth-schema-srv-a3-draft.md` §2.

| # | Target | File | Verdict |
|---|---|---|---|
| 1 | `proto.MarshalUser.wp_proof` | `Spec/google_golang_org/protobuf/proto/MarshalUser.lean` | **survives** |
| 2 | `proto.MarshalRole.wp_proof` | `Spec/google_golang_org/protobuf/proto/MarshalRole.lean` | **survives** |
| 3 | `auth.userOptsIs`, `auth.ownPermW`, `auth.ownPermS` (restated: wire fields `↦□`, size cache in an invariant, `state` not held) | `Proof/go_etcd_io/etcd/server/v3/auth/Buckets.lean` | **survive** |
| 4 | `MarshalIRR.lean`'s docstring edit, the moved meaning of `v3rpc.userAdd_end_to_end_on` | | accepted |

No BLOCKER, no MAJOR. The attacker's evidence (Go, go1.27.3, protobuf-go v1.36.12, the fork's authpb at
`8c28a4296f`, all pass with `-race`): its scratch module `/shared/tmp/a3-attack/mod/att/`
(`attack_test.go`, `big_test.go`; its report `/shared/tmp/a3-attack/report.md`), copied into the repository
beside the author's tests as `examples/authpbmarshal/attack_test.go` and `attack_big_test.go` (package
renamed). What it showed:

- `TestNestedOnlySizeCache`: a byte diff of every message before and after `Marshal` (the top message and the
  nested `Options`/`Permission`s): only the `sizeCache` and `state` words change, nothing a `↦□` of the
  restated predicates holds.
- `TestConcurrentEverything`: concurrent `Marshal`, `proto.Size`, `String()`, protojson and prototext over
  users sharing an `Options` and roles sharing a permission: `-race` silent, every encoding the same.
- `TestDeepGroupDepths`, `TestBigNested` (`A3BIG=1`, 2 GiB key: the nested cache stores 0 above
  `MaxInt32 - 1` and the marshal pass recomputes the size; no wrong bytes): no size premise is needed.

MINORs, applied with the axioms (A3's Freeze, decided by etcd-grove-03):

- m1: `ownPermW` holds the unknown-field bytes `∃ ub, uf ↦*□ ub` (which `proto.MarshalIRR` copies into the
  request's encoding), not only the slice header.
- m2: `pbSizeCacheN`'s docstring: one namespace for every such cache; a cell must never carry two such
  invariants that can be opened together; every invariant is allocated over a fresh message's cache.
- m3: `userOptsIs`'s docstring: every protobuf-go size pass (`Marshal`, `proto.Size`) stores the same value.

Finding about this repository's own specs (`notes/auth-schema-srv-a3-draft.md` §1; recorded in
`notes/STATUS.md`): until A3 the three predicates held the nested messages' whole struct `↦□`, `sizeCache`
and `state` included, a read-only claim false of Go (`Marshal` writes the nested size caches, `String()` and
any `ProtoReflect` a nested `state`). `proto.MarshalIRR`'s precondition held them read-only although the call
writes those caches (its docstring put the caches "outside the model"). No spec or proof reads a size cache
or a `state`, so no result concluded anything from the claim; A3 fixes it (the caches in invariants, which
`MarshalIRR`'s footprint now holds, the `state`s not held).
