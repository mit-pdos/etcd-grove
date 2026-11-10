/-
mvccfull's writer: small Iris lemmas of the writer's part of an incarnation (F1 Prove). Lean-first
(no Rocq counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.RestoreLemmas
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.WriterShares
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.EndLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section model
variable [GooseExts]

theorem notify_notified_eq (σ : MvccState) (pend : List Change) (_hpn : σ.pending = none) :
    (σ.notify pend).notifiedLog = (commitSt σ pend).log := by
  rw [MvccState.notify_notifiedLog, commitSt_log]

/-- **The notify step keeps the bounds' facts** (at the history `Hs'` covering the committed log,
each key changed once in it, the writer's `revHi` above the committed revision). -/
theorem bndOk_notify (ks : List GoString) (σ : MvccState) (pend : List Change) (b : Bnd)
    (Hl Hs' : List HRev) (hpn : σ.pending = none) (hok : bndOk ks σ b Hl)
    (hh : histOkM ks (commitSt σ pend) Hs') (honce : onceUpToAll (commitSt σ pend).log)
    (hb : ((commitSt σ pend).rev : Int) ≤ sint.Z b.2.1) :
    bndOk ks (σ.notify pend) b Hs' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hok
  have hrv : (σ.notify pend).rev = σ.rev := rfl
  have hn := notify_notified_eq σ pend hpn
  have hl1 : 1 ≤ σ.log.length := by unfold MvccState.rev at h2; omega
  have hcl := commitSt_len σ pend hl1
  refine ⟨h1, by rw [hrv]; exact h2, by rw [hrv]; exact h3, h4, ?_, h6, h7, h8, ?_, ?_⟩
  · rw [hn, hcl]; push_cast; omega
  · unfold histOkM at hh ⊢; rw [hn]; exact hh
  · unfold onceUpToAll at honce ⊢; rw [hn]; exact honce

/-- **The commit step keeps them.** -/
theorem bndOk_commit (ks : List GoString) (σ : MvccState) (pend : List Change) (b : Bnd)
    (Hs' : List HRev) (hpn : σ.pending = none) (hok : bndOk ks (σ.notify pend) b Hs')
    (hb : ((commitSt σ pend).rev : Int) ≤ sint.Z b.2.1) :
    bndOk ks (commitSt σ pend) b Hs' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hok
  have hrv : (σ.notify pend).rev = σ.rev := rfl
  have hn := notify_notified_eq σ pend hpn
  have hcn : (commitSt σ pend).notifiedLog = (σ.notify pend).notifiedLog := by
    rw [commitSt_notifiedLog_eq, hn]
  have hge := commitSt_rev_ge σ pend
  refine ⟨h1, ?_, hb, h4, by rw [hcn]; exact h5, h6, h7, h8, ?_, ?_⟩
  · rw [hrv] at h2; omega
  · unfold histOkM at h9 ⊢; rw [hcn]; exact h9
  · unfold onceUpToAll at h10 ⊢; rw [hcn]; exact h10

end model

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **The bounds' facts hold at the writer's state and bounds** (the invariant's, which its halves
pin). -/
theorem incW_bndOk (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG)) (ks : List GoString)
    (γh : HistNames) (i : Nat) (mp : Loc) (m : MemberNames) (ι : IncNames) (kv : GoInterface)
    (qw : Qp) (σ : MvccState) (b : Bnd) :
    incW (GF := GF) ks γh i mp m ι kv qw σ b ={⊤}=∗
      incW ks γh i mp m ι kv qw σ b ∗ ⌜∃ Hl, bndOk ks σ b Hl⌝ := by
  haveI := isInc_persistent hpers
  iintro H
  iunfold incW at H
  icases H with ⟨#Hinc, Hret, Hσw, Hbw⟩
  imod bnd_acc hpers ks γh i mp m ι kv qw σ b $$ [Hret Hσw Hbw]
    with ⟨%Hl0, %Hok0, Hrl, Hrh, Hcl, Hch, Hcls⟩
  · iframe #; iframe
  imod Hcls $$ %b %Hok0 Hrl Hrh Hcl Hch with ⟨Hret, Hσw, Hbw⟩
  imodintro
  isplitl
  · iunfold incW; iframe #; iframe
  · ipureintro; exact ⟨Hl0, Hok0⟩

/-- **`tw.End` is `end`'s callback** for the writer's transaction at `σ` (nothing pending), its
changes `pend`: `End`'s first update (the notify) fires at the incarnation's invariant (the writer's
halves pin the state and the bounds), the history's lower bound moved to `Hs'` (which covers the
committed log); the second (the commit) moves the state to `commitSt σ pend`. The writer's `revHi`
is above the committed revision (`begin`'s). -/
theorem endCb_txnEnd {ty : go.GoType} {v : val}
    (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hEnd : mvcc.api.Txn.End.contract (GF := GF) (hG := hG) ty v)
    (ks : List GoString) (γh : HistNames) (i : Nat) (mp : Loc) (m : MemberNames) (ι : IncNames)
    (kv : GoInterface) (qw : Qp) (σ : MvccState) (b : Bnd) (pend : List Change) (Hs' : List HRev)
    (trace : Loc) (q : Qp) (B : MvccStorage)
    (hpn : σ.pending = none) (hh : histOkM ks (commitSt σ pend) Hs')
    (honce : onceUpToAll (commitSt σ pend).log)
    (hb : ((commitSt σ pend).rev : Int) ≤ sint.Z b.2.1) :
    ⊢ endCb (GF := GF) (methods ty go!"End" v) ks γh i mp m ι kv qw σ b pend Hs'
        iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
          mvccTxn (interface.mkOk ty v) ι.kv trace (.write σ pend) ∗
          mvccBackend ι.kv q B iprop(True))
        (mvccBackend ι.kv q B iprop(True)) := by
  haveI := memberInv_timeless hpers ks γh mp m ι
  haveI := isInc_persistent hpers
  have Hm := memberN_mask i
  have hE := hEnd ι.kv trace (.write σ pend) q B iprop(True)
    iprop(ghostVar ι.ret qw () ∗ ghostVar m.σ (1 : Qp).half (commitSt σ pend) ∗
      ghostVar m.bnd (1 : Qp).half b)
  dsimp only at hE
  unfold endCb
  iintro %Φ ⟨Hw, #Hlb, #Hpkg, Htx, Hbk⟩ HΦ
  iunfold incW at Hw
  icases Hw with ⟨#Hinc, Hret, Hσw, Hbw⟩
  ihave #Hinv : inv (memberN i) (memberInv (GF := GF) ks γh mp m ι) $$ []
  · iunfold isInc at Hinc; icases Hinc with ⟨#H, -⟩; iexact H
  iapply hE $$ [Htx Hbk Hret Hσw Hbw]
  · iframe Hpkg Htx Hbk
    isplitr
    · itrivial
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
  inext
  iintro ⟨Hrdr, Hbk, Hret, Hσw, Hbw⟩
  iapply HΦ
  iframe
  iunfold incW; iframe; iframe #

end lemmas

end mvccfull
end EtcdGrove
end Perennial
