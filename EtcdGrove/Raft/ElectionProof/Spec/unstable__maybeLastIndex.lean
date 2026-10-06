/- Port of election_proof/spec_unstable__maybeLastIndex.v. -/
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

/-- `u.maybeLastIndex()`: the last index of the unstable suffix, and whether there is
one. `ok` is `false` exactly when the suffix is empty.

Stated on a bare `*unstable` rather than through `ownRaftLog`, so that `raftLog`'s own
methods can split the field out and hand it over. `snapshot = nil` is a premise: with a
snapshot present the function has an extra branch, and no snapshot is in scope (see
`InvRaftlog.lean`). -/
abbrev unstable.maybeLastIndex.spec : Prop :=
  ∀ (u : Loc) (uv : unstable) (uents : List raftpb.Entry),
  uv.snapshot' = null →
  uint.Z uv.offset' + (uents.length : Int) < 2^64 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hun" ∷ ownUnstable u uv uents }}
    (App (Val (u @!! go.GoType.PointerType unstable.ty @!! go!"maybeLastIndex")) (Val #()))
  {{ (i : w64) (ok : Bool), RET (PairV #i #ok);
      ownUnstable u uv uents ∗
      ⌜uents = [] → ok = false⌝ ∗
      ⌜uents ≠ [] → ok = true ∧
        uint.Z i = uint.Z uv.offset' + (uents.length : Int) - 1⌝ }}

end spec

end EtcdGrove
end Perennial
