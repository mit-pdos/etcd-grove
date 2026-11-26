/- Lean-first (no Rocq counterpart).

# A receiver's share of `s.readych` (etcd-dist N5, `notes/etcd-dist-plan.md` §19)

`srvReadyRecv s` (persistent): `s.readych`'s field, read-only, and the broadcast idiom's persistent part of the
channel (`ownBroadcastChan … .Unknown`, nothing promised to receivers: `True`), what `ReadyNotify()`'s caller
receives on. `srvReadyCh_recv` splits it off the right to close the channel (`srvReadyCh`, `InvMonitors.lean`),
which stays whole for `publishV3`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvMonitors

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **A receiver's share of `s.readych`** (persistent; see the file header). -/
def srvReadyRecv (s : Loc) : IProp GF :=
  iprop(∃ (rdc : GoChan) (γ : ChanNames), structFieldRef EtcdServer go!"readych" s ↦□ rdc ∗
    ownBroadcastChan rdc γ iprop(True) .Unknown)

instance srvReadyRecv_persistent (s : Loc) : Persistent (srvReadyRecv (GF := GF) s) := by
  unfold srvReadyRecv; infer_instance

/-- **The receiver's share, split off the right to close `s.readych`** (which stays whole). -/
theorem srvReadyCh_recv (s : Loc) : srvReadyCh (GF := GF) s ⊢ srvReadyCh s ∗ srvReadyRecv s := by
  iintro H
  iunfold srvReadyCh at H
  icases H with ⟨%rdc, %γ, #Hf, Hc⟩
  icases ownBroadcastChan_open _ _ _ _ $$ Hc with ⟨%γch, #Hint, Hown⟩
  isplitl [Hown]
  · iunfold srvReadyCh
    iexists rdc, γ
    iframe Hf
    iapply ownBroadcastChan_close _ _ _ .Pending γch
    iframe Hint Hown
  · iunfold srvReadyRecv
    iexists rdc, γ
    iframe Hf
    iapply ownBroadcastChan_close _ _ _ .Unknown γch
    iframe Hint

end defs

end EtcdGrove
end Perennial

end
