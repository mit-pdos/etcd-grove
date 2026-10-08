/- Port of election_proof/spec_unstable__maybeLastIndex.v (feb5c73d4).

Lean notes: Rocq's `(#i, #ok)` is `PairV #i #ok`; `bool_decide` is `decide`.
-/
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

/-- `u.maybeLastIndex()`: the last index of the unstable suffix, and whether there is
one. With an empty suffix it is the pending snapshot's index if a snapshot is pending,
and `ok = false` otherwise.

Stated on a bare `*unstable` rather than through `ownRaftLog`, so that `raftLog`'s own
methods can split the field out and hand it over; the snapshot is `us.snap`
(see `Spec/unstable__maybeFirstIndex.lean`). -/
abbrev unstable.maybeLastIndex.spec : Prop :=
  ∀ (u : Loc) (us : UnstableSt),
  uint.Z us.offset + (us.ents.length : Int) < 2^64 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hun" ∷ ownUnstable u us }}
    (App (Val (u @!! go.GoType.PointerType unstable.ty @!! go!"maybeLastIndex")) (Val #()))
  {{ (i : w64) (ok : Bool), RET (PairV #i #ok);
      ownUnstable u us ∗
      ⌜us.ents = [] → ok = decide (us.snap ≠ none) ∧
                    ∀ sid, us.snap = some sid → i = sid.index'⌝ ∗
      ⌜us.ents ≠ [] → ok = true ∧
        uint.Z i = uint.Z us.offset + (us.ents.length : Int) - 1⌝ }}

end spec

end EtcdGrove
end Perennial
