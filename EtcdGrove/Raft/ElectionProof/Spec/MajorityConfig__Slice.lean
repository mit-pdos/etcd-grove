/- Port of election_proof/spec_MajorityConfig__Slice.v (feb5c73d4). -/
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

/-- `MajorityConfig.Slice` returns the ids of the set, sorted. Stated on `ownIdsetOpt`
(`InvTracker.lean`) so that it covers the `nil` sets a simple configuration carries
(`Voters[1]`, `Learners`, `LearnersNext`), for which the result is the empty (nil)
slice. Sortedness is not stated -- `slices.Sort`'s triple gives only a permutation, and
nothing downstream needs more. -/
abbrev quorum.MajorityConfig.Slice.spec : Prop :=
  ∀ (m : Loc) (ids : GMap w64 Unit),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.quorum ∗ ownIdsetOpt m ids }}
    (App (Val (m @!! quorum.MajorityConfig.ty @!! go!"Slice")) (Val #()))
  {{ (sl : GoSlice) (xs : List w64), RET #sl;
      ownIdsetOpt m ids ∗ sl ↦* xs ∗ ownSliceCap w64 sl (DFrac.own 1) ∗
      ⌜xs ≡ₚ elements (domSet ids)⌝ }}

end spec

end EtcdGrove
end Perennial
