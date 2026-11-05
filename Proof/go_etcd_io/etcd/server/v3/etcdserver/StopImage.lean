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

/-- **The image clause of the stopped backend's data** (the restart plan's R2b-3d stage 5a; the
pure part of `merged_image`): an observation `mergedObs` of `D` at the applied index `ai` of the
applied log `A`, at the server with the KV's start values, is `imageAt` of `A` at `ai`, the KV
names' (`srvDiskImage`'s backend clause). -/
theorem merged_imageAt (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (ai : w64) (A : List EntryModel)
    (x : apply.ApplyKV) (D : backend.Data)
    (h0 : γr.kv.c0 = W64 0 ∧ γr.kv.log0 = [[], []]) :
    ⌜mergedObs γr E.cmp E.lg ai A x.log x.crev D⌝ ∗ isServer s γ ci TM E ρ γr ∗
      kvApplied γr.raft γr.kv A x ⊢
      |={⊤}=> kvApplied γr.raft γr.kv A x ∗
        ⌜imageAt γr.kv γr.raft.raft.boot ai (γr.raft.pre ++ A) A D⌝ := by
  iintro ⟨%hobs, #Hsrv, Hka⟩
  obtain ⟨⟨r, hkI, hr⟩, hci, hterm, hrest, hwf⟩ := hobs
  iunfold isServer at Hsrv
  icases Hsrv with ⟨-, -, -, Hat, -, -⟩
  iunfold srvAtomics at Hat
  icases Hat with ⟨-, -, Hki⟩
  iunfold srvKVInvs at Hki
  icases Hki with ⟨#Hki, -, #Hrl, -, %Hcm, %Hlgk, -⟩
  ihave %hraft := srvRaftLogInv_fresh γr.raft $$ Hrl
  iunfold kvApplied at Hka
  icases Hka with ⟨Hka, %hx⟩
  iunfold kvAppliedL at Hka
  icases Hka with ⟨#HA, Hhi, Hcert, %hlog⟩
  imod crevOf_offM γr.raft γr.kv A $$ Hki Hrl HA with %Hoff
  imod kv_log_plain γr.raft γr.kv A $$ Hki Hrl HA with %Hpl0
  imodintro
  isplitl [Hhi Hcert]
  · iunfold kvApplied
    iunfold kvAppliedL
    iframe HA Hhi Hcert
    ipureintro; exact ⟨hlog, hx⟩
  ipureintro
  have hpre : γr.raft.pre = [] := by rw [hraft]
  rw [hlog] at hkI hwf
  have hrc : r.crev = crevOf γr.kv A := by
    cases hc : E.cmp
    · rw [hc] at hkI
      obtain ⟨-, rfl⟩ := (mvcc.keyImageM_off _ _ D).1 hkI
      rw [mvcc.CmpRecs.crev_empty]; exact (Hoff (Hcm.1.trans hc)).symm
    · rw [hr hc, hx.2]
  refine ⟨⟨r, ?_, hrc⟩, hci, hterm, ?_, hwf⟩
  · rw [Hcm.1]; exact hkI
  · cases hlg : E.lg
    · rw [hlg] at hrest
      simp only [Bool.false_eq_true, ↓reduceIte] at hrest
      have hpl : plainLogM γr.kv.cmp .none A := by
        have := Hpl0.1; rw [Hlgk.2, apply.AEnv.lm_of_lg_false hlg] at this; exact this
      have hn : (kvLeases γr.kv (γr.raft.pre ++ A)).ids = [] := by
        rw [hpre, List.nil_append]; unfold kvLeases; rw [kvTableOf_plainM _ _ _ A hpl]; rfl
      exact bkRestAtL_of_nil hn hrest
    · rw [hlg] at hrest
      exact hrest

end proof

end EtcdGrove
end Perennial
