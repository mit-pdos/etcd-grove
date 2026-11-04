/-
**The stopped backend's data, observed** (the restart plan's R2b-3d stage 3, 2026-11-04;
`notes/restart-plan.md`, "R2b-3d stage 3"). Lean-first (no Rocq counterpart).

`Cleanup`'s `backend.Close`, given the server's request of the stop's commit (`commitReq_freeze`:
the idle apply thread's state for the frozen protocol, `freezeY`), returns what the stopped batch
lock held at the data `D` its file holds (`bStopView`, at the server's own resources,
`srvStopChans`), with a reader's bound of the compaction keys' flag at `D`. With the apply thread's
halves of what the lock tracks, the same observation as the merged snapshot's window
(`snapObs_window`, `txn.kvWriter_keyObs`, `apply.cmpObs`, `txn.kvWriter_noCmp`) gives `D`'s
`mergedObsM` (`mergedObsM_of_obs`): the image of the applied log at the applied index.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapSendBranch
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvStop
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.TrackedLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The stopped backend's data is the image of the applied log** (see the file header): with the
frozen protocol at the apply thread's state `st` (`freezeY`, the stop's commit stored `ciEff γA
st.k = ai`), its halves of the tracked buckets at the rest model's, the KV's writer and compaction
right, what `Close` returned of the stopped lock at `D` gives `mergedObsM`. -/
theorem stop_mergedObs (γA : ApplyNames) (E : apply.AEnv GF) (γr : ReadNames) (ai : w64)
    (A : List EntryModel) (x : apply.ApplyKV) (d : mvcc.KBReal) (f : w64 → w64) (st : ApplyState)
    (D : backend.Data) (hkb : E.γ.kb = some d) (hcK : ciKeys d.P)
    (hRB : ∀ n ∈ restBuckets, d.P.RB n = true) (hcm : d.cm = E.cmp) (hci : ciEff γA st.k = ai)
    (Hwf : mvcc.IdxWf x.log []) :
    freezeY γA st ∗
      backend.rbOwnIn d.γB membership.clusterBkts
        (apply.restLeasesWith f (srvIds E (appliedTable γr A).ids)
          (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A))).bk ∗
      backend.rbPart d.γB (restSet E.authMode)
        (apply.restLeasesWith f (srvIds E (appliedTable γr A).ids)
          (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A))).bk ∗
      txn.kvWriter E.s E.γ x.log ∗ apply.cmpOwn E x.crev ∗
      backend.bStopView d.γB d.P (mvcc.lateWD d) (batchLockInv γA (metaTM d.γB d.P)) D ⊢
    ⌜mergedObsM E.authMode γr E.cmp E.lg ai A x.log x.crev D⌝ := by
  iintro ⟨HY, Hrc, Hrn, Hkw, Hcmo, Hsv⟩
  iunfold backend.bStopView at Hsv
  icases Hsv with ⟨HW, HPk, Hv, Hpv, Hhk, Hr, Hck, %R, #Hfk⟩
  -- no compaction key in a store that does not compact
  ihave ⟨%hnc0, Hkw⟩ := txn.kvWriter_noCmp E.s E.γ d hkb x.log (D, R) $$ [Hkw Hfk]
  · iframe Hkw Hfk
  have hnc : d.cm = false → backend.fkAbsD D := fun h => (hnc0 h).1
  -- the window's observation, at the stopped lock's pieces
  ihave #Hobs := snapObs_window γA d.γB d.P hcK (mvcc.lateWD d)
    iprop(txn.kvWriter E.s E.γ x.log ∗ apply.cmpOwn E x.crev) st (restSet E.authMode)
    (apply.restLeasesWith f (srvIds E (appliedTable γr A).ids)
      (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A))).bk (fun _ => False) ∅
    (fun vd v => ((∀ k v, vd.lookup (mvcc.keyName, k) = some v →
        (mvcc.bucketMap x.log).lookup k = some v) ∧
      (d.cm = false → ∀ k, vd.lookup (mvcc.keyName, k) = (mvcc.bucketMap x.log).lookup k)) ∧
      apply.windowObs d x.log x.crev vd v) $$ []
  · iintro !> %vd %v ⟨Hkw, Hcmo⟩ HW Hv Hp Hc
    rcases Bool.eq_false_or_eq_true d.cm with hc | hc
    · icases apply.cmpObs E d hkb hc x.log x.crev vd v $$ [$Hkw $Hcmo $HW $Hp $Hc]
        with ⟨Hkw, -, -, %ho⟩
      ihave %hk := txn.kvWriter_keyObs E.s E.γ d hkb x.log vd $$ [Hkw Hv]
      · iframe
      ipureintro
      exact ⟨hk, fun _ => ho⟩
    · ihave %hk := txn.kvWriter_keyObs E.s E.γ d hkb x.log vd $$ [Hkw Hv]
      · iframe
      ipureintro
      exact ⟨hk, fun h => by rw [hc] at h; cases h⟩
  ihave Hnone := backend.rbPart_none (GF := GF) d.γB (∅ : GMap GoString backend.BktData)
  ihave %h := Hobs $$ %(backend.sData d.P D) %(backend.hkData d.P D) %(backend.rbData d.P D)
    %(backend.fkVals D) [HY Hrc Hrn Hnone Hkw Hcmo] HW HPk Hv Hpv Hhk Hr Hck
  · iframe HY Hkw Hcmo
    iframe Hrc Hrn Hnone
  ipureintro
  obtain ⟨⟨hciO, hrbD, -⟩, ⟨-, hex⟩, hwo⟩ := h
  exact mergedObsM_of_obs E γr ai A x d f D hcK hRB hcm (hci ▸ hciO) hrbD hex hwo hnc Hwf

end proof

end EtcdGrove
end Perennial
