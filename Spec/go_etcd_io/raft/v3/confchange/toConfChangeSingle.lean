/-
`confchange.toConfChangeSingle(cs)` turns a `ConfState` into the single changes that
rebuild it. Lean-first (no Rocq counterpart); see `InvConfchange.lean`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvRestore
public import Proof.go_etcd_io.raft.v3.InvPb

@[expose] public section

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

/-- The changes `Restore` replays a `ConfState` as (`InvRestore.lean`): `out` holds one
`AddNode` per outgoing voter (`restoreOutCC`; `nil` when there is none), `in` one `RemoveNode`
per outgoing voter, then one `AddNode` per voter, one `AddLearnerNode` per learner and per
staged learner (`restoreInCC`), in a fresh slice. Generalized 2026-10-14 (reconfiguration
stage B8) from the non-joint case (empty `VotersOutgoing` and `LearnersNext`).

(2026-10-15, raft v3.7 retarget, stage R2: `cs` a `*pb.ConfState` owned at `dq` (`ownCSM`,
which holds every slice's points-to, so the old `ownIdList` of the three lists other than the
voters goes) instead of a `ConfState` value with four fractions; the results are slices of
fresh `*pb.ConfChangeSingle` pointers `lo`, `li`, each `ccsRO` of its change, instead of slices
of the change values.) -/
abbrev confchange.toConfChangeSingle.spec : Prop :=
  ∀ (cs : Loc) (c : ConfStateM) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange ∗ ownCSM cs dq c }}
    (App (Val #(functions confchange.toConfChangeSingle [])) (Val #cs))
  {{ (o s : GoSlice) (lo li : List Loc), RET (PairV #o #s);
      ownCSM cs dq c ∗
      o ↦* lo ∗ ([∗list] q;x ∈ lo;restoreOutCC c.VotersOutgoing', ccsRO q x) ∗
      s ↦* li ∗
      ([∗list] q;x ∈ li;restoreInCC c.VotersOutgoing' c.Voters' c.Learners' c.LearnersNext',
        ccsRO q x) ∗
      ownSliceCap Loc s (DFrac.own 1) }}

end spec

end EtcdGrove
end Perennial
