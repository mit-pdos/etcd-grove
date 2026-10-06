/- Port of election_proof/spec_unstable__maybeFirstIndex.v (feb5c73d4). -/
import EtcdGrove.Raft.ElectionProof.InvRaftPhys

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
field is split out. Each takes the pending snapshot's pointer as
`ownSnap uv.snapshot snap` (`InvRaftlog.lean`): `none` is `snapshot = nil`, `some sid` a
pending snapshot whose metadata is `sid` (since 2026-10-02; until then
`snapshot = nil` was a premise and the snapshot arms were dead).

`u.maybeFirstIndex()`: `snapshot.Metadata.Index + 1` when a snapshot is pending, and
`ok = false` otherwise. -/
abbrev unstable.maybeFirstIndex.spec : Prop :=
  ∀ (u : Loc) (uv : unstable) (uents : List raftpb.Entry) (snap : Option entryID),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hun" ∷ ownUnstable u uv uents ∗
      "#Hsnap" ∷ ownSnap uv.snapshot' snap }}
    (App (Val (u @!! go.GoType.PointerType unstable.ty @!! go!"maybeFirstIndex")) (Val #()))
  {{ (i : w64) (ok : Bool), RET (PairV #i #ok);
      ownUnstable u uv uents ∗
      ⌜ok = decide (snap ≠ none) ∧
        ∀ sid, snap = some sid → i = sid.index' + W64 1⌝ }}

end spec

end EtcdGrove
end Perennial
