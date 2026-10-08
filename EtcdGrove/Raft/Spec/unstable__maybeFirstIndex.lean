/- Port of election_proof/spec_unstable__maybeFirstIndex.v (feb5c73d4). -/
import EtcdGrove.Raft.InvRaftPhys

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **The `unstable` suffix.**

Three `maybe*` methods, all on a bare `*unstable` so they can be reused wherever the
field is split out. Each reads the pending snapshot as `ownUnstable`'s `us.snap`
(`ownSnap`, `InvRaftlog.lean`): `none` is `snapshot = nil`, `some sid` a pending
snapshot whose metadata is `sid` (since 2026-10-02; until then `snapshot = nil` was a
premise and the snapshot arms were dead; until 2026-10-08 `ownSnap uv.snapshot snap` was
a separate premise).

`u.maybeFirstIndex()`: `snapshot.Metadata.Index + 1` when a snapshot is pending, and
`ok = false` otherwise. -/
abbrev unstable.maybeFirstIndex.spec : Prop :=
  ∀ (u : Loc) (us : UnstableSt),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hun" ∷ ownUnstable u us }}
    (App (Val (u @!! go.GoType.PointerType unstable.ty @!! go!"maybeFirstIndex")) (Val #()))
  {{ (i : w64) (ok : Bool), RET (PairV #i #ok);
      ownUnstable u us ∗
      ⌜ok = decide (us.snap ≠ none) ∧
        ∀ sid, us.snap = some sid → i = sid.index' + W64 1⌝ }}

end spec

end EtcdGrove
end Perennial
