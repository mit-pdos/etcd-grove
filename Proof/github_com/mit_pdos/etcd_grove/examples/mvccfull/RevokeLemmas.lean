/-
mvccfull's `runner.apply`, the revoke arm (mvccrand's `writer__revoke.lean` over the keys `ks` and
the member's incarnation): the model of the revoke's revision (`opPend_revoke`: the tester's keys
on the lease deleted from the last state, in key order), which is the store's `leaseDels`
(`pendOk_revoke'`), its model step (`runM_succ_revoke`), the bound on the store's state
(`stMatch_length_le'`), and `Revoke`'s update at the writer's part of the incarnation
(`revoke_au`: `Write`'s begin at `σ`, then `End`'s two steps as `endCb_txnEnd`'s). Lean-first (no
Rocq counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.ApplyLemmas
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.CheckLeasesLemmas
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.WriteSubLemmas
public import Proof.go_etcd_io.etcd.server.v3.lease.MvccShapes

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section model
variable [GooseExts]

/-- `pending`'s deletes of the keys `KS`, one at a time. -/
theorem foldl_delOne (KS : List GoString) : ∀ P : PendM,
    KS.foldl PendM.delOne P = { P with st := delAll KS P.st, chs := P.chs ++ KS.map delChange } := by
  induction KS with
  | nil => intro P; simp [delAll]
  | cons k KS ih =>
    intro P
    rw [List.foldl_cons, ih]
    simp only [PendM.delOne, delAll, List.foldl_cons, List.map_cons, List.append_assoc,
      List.cons_append, List.nil_append]

/-- **The revision a revoke makes**: the tester's keys on the lease, in key order, deleted from the
last state. -/
theorem opPend_revoke (ks : List GoString) (s : MSt) (o : OpM) (hk : o.kind = kRevoke) :
    opPend ks s o = ⟨W64 (s.hs.length : Int), delAll (ks.filter (onLease (lastSt s.hs) o.id))
      (lastSt s.hs), (ks.filter (onLease (lastSt s.hs) o.id)).map delChange⟩ := by
  unfold opPend
  rw [hk]
  simp only [show (kRevoke = kPut) = False from by simp, show (kRevoke = kDelete) = False from by simp,
    show (kRevoke = kTxn) = False from by simp, ↓reduceIte]
  rw [foldl_delOne]
  simp

/-- **The revoke's model is the store's deletes of the lease** (`leaseDels`, at a live lease: not
`0`). -/
theorem pendOk_revoke' (ks : List GoString) (hks : ks.Pairwise go.GoStringLt) (σ : MvccState)
    (Hs : List HRev) (hM : stMatch ks (lastSt Hs) (stateAfter σ.log)) (id : w64) (hid : id ≠ W64 0) :
    pendOk ks σ Hs (leaseDels (stateAfter σ.log) id)
      ⟨W64 (Hs.length : Int), delAll (ks.filter (onLease (lastSt Hs) id)) (lastSt Hs),
        (ks.filter (onLease (lastSt Hs) id)).map delChange⟩ := by
  have hs : (stateAfter σ.log).Pairwise etcdKvLess := stateAfter_sorted σ.log
  have hk := leaseDelKeys_eq_onLease ks hks (lastSt Hs) _ hM hs id hid
  unfold leaseDels
  rw [hk]
  refine ⟨?_, stMatch_delAll' _ _ _ _ _ hM⟩
  have := delOne_foldl (ks.filter (onLease (lastSt Hs) id)) ⟨W64 (Hs.length : Int), lastSt Hs, []⟩
  simpa only [List.nil_append, pendOf] using this

/-- **A revoke's model step** leaves the compaction revision, the granted leases and the
compactions; the lease leaves the live ones. -/
theorem runM_succ_revoke (ks : List GoString) (ops : List OpM) (n : Nat) (o : OpM)
    (ho : ops[n]? = some o) (hk : o.kind = kRevoke) :
    cmpAfter ks ops (n + 1) = cmpAfter ks ops n ∧
      leasesAfter ks ops (n + 1) = (leasesAfter ks ops n).filter (· != o.id) ∧
      grantedAfter ks ops (n + 1) = grantedAfter ks ops n ∧ compsAt ks ops (n + 1) = compsAt ks ops n := by
  unfold cmpAfter leasesAfter grantedAfter compsAt
  rw [runM_succ ks ops n o ho]
  unfold opStep
  rw [hk]
  simp

/-- **A state the tester's map matches has at most its keys' count of key-values** (sorted:
distinct keys). -/
theorem stMatch_length_le' (ks : List GoString) (M : GMap GoString kvRec) (s : List EtcdKv)
    (hM : stMatch ks M s) (hs : s.Pairwise etcdKvLess) : s.length ≤ ks.length := by
  have hnd : (s.map EtcdKv.key).Nodup := by
    unfold List.Nodup
    rw [List.pairwise_map]
    refine hs.imp ?_
    intro a b h heq
    unfold etcdKvLess at h
    rw [heq] at h
    exact go.goStringLt_irrefl _ h
  have hsub : s.map EtcdKv.key ⊆ ks := by
    intro k hk
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hk
    exact hM.2 v hv
  have := (List.subperm_of_subset hnd hsub).length_le
  simpa using this

end model

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **`End`'s two steps** (`srvApi.auEnd`) of the writer's transaction at `σ` (nothing pending),
its changes `pend`, at the incarnation's invariant: `endCb_txnEnd`'s, to the writer's halves at the
committed state. -/
theorem end_au (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (ks : List GoString) (γh : HistNames) (i : Nat) (mp : Loc) (m : MemberNames) (ι : IncNames)
    (kv : GoInterface) (qw : Qp) (σ : MvccState) (b : Bnd) (pend : List Change) (Hs' : List HRev)
    (hpn : σ.pending = none) (hh : histOkM ks (commitSt σ pend) Hs')
    (honce : onceUpToAll (commitSt σ pend).log)
    (hb : ((commitSt σ pend).rev : Int) ≤ sint.Z b.2.1) :
    isInc (GF := GF) ks γh i mp m ι kv ∗ monoListLbOwn γh.l Hs' ∗ ghostVar ι.ret qw () ∗
        ghostVar m.σ (1 : Qp).half σ ∗ ghostVar m.bnd (1 : Qp).half b ⊢
      srvApi.auEnd ι.kv σ pend iprop(ghostVar ι.ret qw () ∗
        ghostVar m.σ (1 : Qp).half (commitSt σ pend) ∗ ghostVar m.bnd (1 : Qp).half b) := by
  haveI := memberInv_timeless hpers ks γh mp m ι
  haveI := isInc_persistent hpers
  have Hm := memberN_mask i
  iintro ⟨#Hinc, #Hlb, Hret, Hσw, Hbw⟩
  ihave #Hinv : inv (memberN i) (memberInv (GF := GF) ks γh mp m ι) $$ []
  · iunfold isInc at Hinc; icases Hinc with ⟨#H, -, -⟩; iexact H
  unfold srvApi.auEnd
  -- the notify step
  iauintro
  unfold atomic_acc
  iinv Hinv with >Hi Hclose
  iunfold memberInv at Hi
  icases Hi with (Hs | Hr)
  rotate_left
  · icombine Hret Hr gives %Hq0
    obtain ⟨Hq, -⟩ := Hq0
    exfalso
    have h := Qp.le_iff.mp Hq
    simp only [Qp.val_add, Qp.val_one] at h
    have := qw.2
    grind
  iunfold memberState at Hs
  icases Hs with ⟨%σ1, %b1, %Hl1, Hs, Hσi, Hrl, Hrh, Hcl, Hch, Hbi, Hrev, Hcrev, Hnrev, Hlb1, %Hp⟩
  ihave %Hag := ghostVar_agree m.σ _ _ _ _ $$ Hσi Hσw
  ihave %Hagb := ghostVar_agree m.bnd _ _ _ _ $$ Hbi Hbw
  subst Hag Hagb
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ (⊤ \ ↑mvccN) \ ↑(memberN i) from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists σ1
  iframe Hs
  isplit
  · iintro Hs
    imod Hclose2 with -
    imod Hclose $$ [Hs Hσi Hrl Hrh Hcl Hch Hbi Hrev Hcrev Hnrev Hlb1] with -
    · inext; iunfold memberInv; ileft; iunfold memberState; iexists σ1, b1, Hl1; iframe
      ipureintro; exact Hp
    imodintro
    iframe
  · iintro ⟨-, Hs, -⟩
    imod Hclose2 with -
    have hok1 : bndOk ks σ1 b1 Hl1 := Hp
    have hokn := bndOk_notify ks σ1 pend b1 Hl1 Hs' hpn hok1 hh honce hb
    have hn := notify_notified_eq σ1 pend hpn
    have hn0 : σ1.notifiedLog = σ1.log := by unfold MvccState.notifiedLog; rw [hpn]
    have hle : σ1.notifiedLog.length ≤ (σ1.notify pend).notifiedLog.length := by
      rw [hn, hn0, commitSt_log]; unfold commitLog; split <;> simp
    imod ghostVar_update_halves (σ1.notify pend) m.σ _ _ $$ Hσi Hσw with ⟨Hσi, Hσw⟩
    imod mono_nat_own_update (σ1.notify pend).notifiedLog.length hle $$ Hnrev with ⟨Hnrev, -⟩
    iclear Hlb1
    imod Hclose $$ [Hs Hσi Hrl Hrh Hcl Hch Hbi Hrev Hcrev Hnrev] with -
    · inext; iunfold memberInv; ileft; iunfold memberState; iexists σ1.notify pend, b1, Hs'
      iframe; iframe #
      ipureintro; exact hokn
    imodintro
    -- the commit step
    iauintro
    unfold atomic_acc
    iinv Hinv with >Hi Hclose
    iunfold memberInv at Hi
    icases Hi with (Hs | Hr)
    rotate_left
    · icombine Hret Hr gives %Hq0
      obtain ⟨Hq, -⟩ := Hq0
      exfalso
      have h := Qp.le_iff.mp Hq
      simp only [Qp.val_add, Qp.val_one] at h
      have := qw.2
      grind
    iunfold memberState at Hs
    icases Hs with ⟨%σ2, %b2, %Hl2, Hs, Hσi, Hrl, Hrh, Hcl, Hch, Hbi, Hrev, Hcrev, Hnrev, Hlb2, %Hp2⟩
    ihave %Hag := ghostVar_agree m.σ _ _ _ _ $$ Hσi Hσw
    ihave %Hagb := ghostVar_agree m.bnd _ _ _ _ $$ Hbi Hbw
    subst Hag Hagb
    iapply fupd_mask_intro (show (∅ : CoPset) ⊆ (⊤ \ ↑mvccN) \ ↑(memberN i) from
      Std.LawfulSet.empty_subset)
    iintro Hclose2
    isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
    iexists σ1.notify pend
    iframe Hs
    isplit
    · iintro Hs
      imod Hclose2 with -
      imod Hclose $$ [Hs Hσi Hrl Hrh Hcl Hch Hbi Hrev Hcrev Hnrev Hlb2] with -
      · inext; iunfold memberInv; ileft; iunfold memberState; iexists σ1.notify pend, b2, Hl2
        iframe; ipureintro; exact Hp2
      imodintro
      iframe
    · iintro ⟨-, Hs⟩
      imod Hclose2 with -
      have hcp : (σ1.notify pend).commitPending = commitSt σ1 pend := rfl
      rw [hcp]
      have hokc := bndOk_commit ks σ1 pend b2 Hl2 hpn Hp2 hb
      have hrge : (σ1.notify pend).rev ≤ (commitSt σ1 pend).rev := commitSt_rev_ge σ1 pend
      have hnl : (commitSt σ1 pend).notifiedLog.length = (σ1.notify pend).notifiedLog.length := by
        rw [commitSt_notifiedLog_eq, notify_notified_eq σ1 pend hpn]
      imod ghostVar_update_halves (commitSt σ1 pend) m.σ _ _ $$ Hσi Hσw with ⟨Hσi, Hσw⟩
      imod mono_nat_own_update (commitSt σ1 pend).rev hrge $$ Hrev with ⟨Hrev, -⟩
      imod Hclose $$ [Hs Hσi Hrl Hrh Hcl Hch Hbi Hrev Hcrev Hnrev Hlb2] with -
      · inext; iunfold memberInv; ileft; iunfold memberState; iexists commitSt σ1 pend, b2, Hl2
        iframe
        rw [hnl]; iframe
        ipureintro; have h := hokc; unfold bndOk at h; rw [hnl] at h; exact h
      imodintro
      iframe

/-- **`Revoke`'s update** at the writer's part of the incarnation at `σ` (nothing pending): the
deleter's `Write` begins at `σ` (the writer's half pins it), then `End`'s two steps (`end_au`). -/
theorem revoke_au (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (ks : List GoString) (γh : HistNames) (i : Nat) (mp : Loc) (m : MemberNames) (ι : IncNames)
    (kv : GoInterface) (qw : Qp) (σ : MvccState) (b : Bnd) (pend : List Change) (Hs' : List HRev)
    (hpn : σ.pending = none) (hh : histOkM ks (commitSt σ pend) Hs')
    (honce : onceUpToAll (commitSt σ pend).log)
    (hb : ((commitSt σ pend).rev : Int) ≤ sint.Z b.2.1) :
    isInc (GF := GF) ks γh i mp m ι kv ∗ monoListLbOwn γh.l Hs' ∗ ghostVar ι.ret qw () ∗
        ghostVar m.σ (1 : Qp).half σ ∗ ghostVar m.bnd (1 : Qp).half b ⊢
      srvApi.auBegin ι.kv σ (srvApi.auEnd ι.kv σ pend iprop(ghostVar ι.ret qw () ∗
        ghostVar m.σ (1 : Qp).half (commitSt σ pend) ∗ ghostVar m.bnd (1 : Qp).half b)) := by
  haveI := memberInv_timeless hpers ks γh mp m ι
  haveI := isInc_persistent hpers
  have Hm := memberN_mask i
  iintro ⟨#Hinc, #Hlb, Hret, Hσw, Hbw⟩
  ihave #Hinv : inv (memberN i) (memberInv (GF := GF) ks γh mp m ι) $$ []
  · iunfold isInc at Hinc; icases Hinc with ⟨#H, -, -⟩; iexact H
  unfold srvApi.auBegin
  iauintro
  unfold atomic_acc
  iinv Hinv with >Hi Hclose
  iunfold memberInv at Hi
  icases Hi with (Hs | Hr)
  rotate_left
  · icombine Hret Hr gives %Hq0
    obtain ⟨Hq, -⟩ := Hq0
    exfalso
    have h := Qp.le_iff.mp Hq
    simp only [Qp.val_add, Qp.val_one] at h
    have := qw.2
    grind
  iunfold memberState at Hs
  icases Hs with ⟨%σ1, %b0, %Hl, Hs, Hσi, Hrest⟩
  ihave %Hag := ghostVar_agree m.σ _ _ _ _ $$ Hσi Hσw
  subst Hag
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ (⊤ \ ↑mvccN) \ ↑(memberN i) from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists σ1
  iframe Hs
  isplit
  · iintro Hs
    imod Hclose2 with -
    imod Hclose $$ [Hs Hσi Hrest] with -
    · inext; iunfold memberInv; ileft; iunfold memberState; iexists σ1, b0, Hl; iframe
    imodintro
    iframe
  · iintro ⟨-, Hs⟩
    imod Hclose2 with -
    imod Hclose $$ [Hs Hσi Hrest] with -
    · inext; iunfold memberInv; ileft; iunfold memberState; iexists σ1, b0, Hl; iframe
    imodintro
    isplitr
    · ipureintro; rfl
    iapply end_au hpers ks γh i mp m ι kv qw σ1 b pend Hs' hpn hh honce hb
    iframe; iframe #

end lemmas

end mvccfull
end EtcdGrove
end Perennial
