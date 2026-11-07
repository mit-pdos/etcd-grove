/-
`end`'s callback at a write transaction's `End` (`w.end(p, tw.End)`, in `put`, `deleteRange` and
`txn`). Lean-first (no Rocq counterpart).

**`endCb_txnEnd`**: `tw.End` (`Txn.End.contract`) is `end`'s callback (`endCb`) for the writer's
transaction (`σ`, `pend`, the model `P`, `pendOk`), its frame the transaction, the backend share and
the tester's invariant: `End`'s first update (the notify) fires at the invariant's `σ` (the writer's
half of `γ.σ`), moving both halves to `σ.notify pend`, with the history's lower bound moved to
`histAfter Hs P` (`histOk_commit`: it covers the notified log); the second (the commit) moves them to
`commitSt σ pend`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.Writer

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.mvccrand mvcc mvcc.api

section model
variable [GooseExts]

/-- **The history after the transaction covers the committed log** (pure): the writer's revisions
`Hs` are its log's (`revOk`), so `histAfter Hs P` (the pending revision appended once it has a change)
is `commitLog σ.log pend`'s. -/
theorem histOk_commit (σ : MvccState) (Hs : List HRev) (pend : List Change) (P : PendM)
    (hok : pendOk σ Hs pend P) (hlen : Hs.length = σ.log.length)
    (hrev : ∀ r < Hs.length, ∃ e, Hs[r]? = some e ∧ revOk σ.log Hs r e) :
    (histAfter Hs P).length = (commitLog σ.log pend).length ∧
    ∀ r < (histAfter Hs P).length, ∃ e, (histAfter Hs P)[r]? = some e ∧
      revOk (commitLog σ.log pend) (histAfter Hs P) r e := by
  obtain ⟨hP, hst⟩ := hok
  by_cases hpe : pend = []
  · have hc : P.chs = [] := by rw [hP]; exact (pendOf_chs_nil_iff _ _ _).2 hpe
    have h1 : histAfter Hs P = Hs := by unfold histAfter; simp [hc]
    have h2 : commitLog σ.log pend = σ.log := by unfold commitLog; simp [hpe]
    rw [h1, h2]
    exact ⟨hlen, hrev⟩
  · have hc : P.chs ≠ [] := by rw [hP]; exact fun h => hpe ((pendOf_chs_nil_iff _ _ _).1 h)
    have h1 : histAfter Hs P = Hs ++ [(P.st, P.chs)] := by unfold histAfter; simp [hc]
    have h2 : commitLog σ.log pend = σ.log ++ [pend] := by unfold commitLog; simp [hpe]
    rw [h1, h2]
    refine ⟨by simp [hlen], fun r hr => ?_⟩
    simp only [List.length_append, List.length_singleton] at hr
    by_cases hlt : r < Hs.length
    · obtain ⟨e, he, hst', hprev⟩ := hrev r hlt
      refine ⟨e, by rw [List.getElem?_append_left hlt]; exact he, ?_, fun h1r => ?_⟩
      · rw [stateAt_append_lt _ _ (by omega)]; exact hst'
      · obtain ⟨e', he', heq⟩ := hprev h1r
        refine ⟨e', by rw [List.getElem?_append_left (by omega)]; exact he', ?_⟩
        have hg : (σ.log ++ [pend]).getD r [] = σ.log.getD r [] := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (show r < σ.log.length by omega)]
        rw [hg]; exact heq
    · have hr' : r = Hs.length := by omega
      subst hr'
      refine ⟨(P.st, P.chs), by simp, ?_, fun h1r => ?_⟩
      · rw [hlen, stateAt_pend]; exact hst
      · have hlt' : Hs.length - 1 < Hs.length := by omega
        refine ⟨Hs[Hs.length - 1], by
          rw [List.getElem?_append_left hlt']; exact List.getElem?_eq_getElem hlt', ?_⟩
        have hg : (σ.log ++ [pend]).getD Hs.length [] = pend := by
          simp [List.getD_eq_getElem?_getD, hlen]
        have hl : lastSt Hs = (Hs[Hs.length - 1]).1 := by
          unfold lastSt; rw [List.getElem?_eq_getElem hlt']; rfl
        rw [hg, ← hl, ← hP]

/-- The notify step's history: `histAfter Hs P` covers the notified log. -/
theorem histOkM_notify (σ : MvccState) (Hs : List HRev) (pend : List Change) (P : PendM)
    (hok : pendOk σ Hs pend P) (hlen : Hs.length = σ.log.length)
    (hrev : ∀ r < Hs.length, ∃ e, Hs[r]? = some e ∧ revOk σ.log Hs r e) :
    histOkM (σ.notify pend) (histAfter Hs P) := by
  obtain ⟨h1, h2⟩ := histOk_commit σ Hs pend P hok hlen hrev
  unfold histOkM
  rw [MvccState.notify_notifiedLog]
  exact ⟨Nat.le_of_eq h1.symm, fun r hr => h2 r (by omega)⟩

theorem commitSt_log (σ : MvccState) (pend : List Change) :
    (commitSt σ pend).log = commitLog σ.log pend := by
  unfold commitSt MvccState.commitPending MvccState.notify
  by_cases hp : pend = [] <;> simp [hp, commitLog]

/-- The committed state's notified log is the notify step's. -/
theorem commitSt_notifiedLog (σ : MvccState) (pend : List Change) :
    (commitSt σ pend).notifiedLog = (σ.notify pend).notifiedLog := by
  rw [MvccState.notify_notifiedLog, ← commitSt_log]
  rfl

theorem commitSt_crev (σ : MvccState) (pend : List Change) : (commitSt σ pend).crev = σ.crev := rfl

theorem commitSt_pending (σ : MvccState) (pend : List Change) : (commitSt σ pend).pending = none :=
  rfl

theorem commitSt_rev_ge (σ : MvccState) (pend : List Change) : σ.rev ≤ (commitSt σ pend).rev := by
  unfold MvccState.rev; rw [commitSt_log]
  unfold commitLog; split <;> simp

end model

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **`tw.End` is `end`'s callback** (see the file header). -/
theorem endCb_txnEnd {ty : go.GoType} {v : val}
    (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hEnd : mvcc.api.Txn.End.contract (GF := GF) (hG := hG) ty v)
    (h : Loc) (γ : RandNames) (σ : MvccState) (Hs : List HRev) (pend : List Change) (P : PendM)
    (trace : Loc) (q : Qp) (B : MvccStorage)
    (hok : pendOk σ Hs pend P) (_hpn : σ.pending = none) (hlen : Hs.length = σ.log.length)
    (hrev : ∀ r < Hs.length, ∃ e, Hs[r]? = some e ∧ revOk σ.log Hs r e) :
    ⊢ endCb (GF := GF) (methods ty go!"End" v) γ σ pend (histAfter Hs P)
        iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
          inv worldN (worldInv h γ) ∗
          mvccTxn (interface.mkOk ty v) γ.kv trace (.write σ pend) ∗ mvccBackend γ.kv q B iprop(True))
        (mvccBackend γ.kv q B iprop(True)) := by
  haveI := fun σ => hpers.2.2.2.2.2.1 γ.kv σ
  haveI := fun S => hpers.2.2.2.2.2.2.1 γ.ws S
  haveI : Timeless (worldInv (GF := GF) h γ) := by unfold worldInv; infer_instance
  have hdisj : (↑worldN : CoPset) ⊆ ⊤ \ ↑mvccN :=
    nclose_subseteq' "world" (mask_ndot_ne' nroot "mvccrand" "mvcc" (by decide))
  have hE := hEnd γ.kv trace (.write σ pend) q B iprop(True)
    iprop(ghostVar γ.σ (1 : Qp).half (commitSt σ pend))
  dsimp only at hE
  unfold endCb
  iintro %Φ ⟨Hw, #Hlb, #Hpkg, #Hinv, Htx, Hbk⟩ HΦ
  iapply hE $$ [Htx Hbk Hw]
  · iframe Hpkg Htx Hbk
    isplitr
    · itrivial
    -- the notify step
    iauintro
    unfold atomic_acc
    iinv Hinv with >Hi Hclose
    iunfold worldInv at Hi
    icases Hi with ⟨%σ1, %S, %p, %Hl, %W, Hs, Hgσ, HS, Hreg, Hpub, Hpv, Hpm, Hlb0, %Hok⟩
    ihave %Hag := ghostVar_agree γ.σ _ _ _ _ $$ Hgσ Hw
    have Hag' := Hag.symm
    subst Hag'
    iapply fupd_mask_intro (show (∅ : CoPset) ⊆ (⊤ \ ↑mvccN) \ ↑worldN from
      Std.LawfulSet.empty_subset)
    iintro Hclose2
    isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
    iexists σ
    iframe Hs
    isplit
    · iintro Hs
      imod Hclose2 with -
      imod Hclose $$ [Hs Hgσ HS Hreg Hpub Hpv Hpm Hlb0] with -
      · inext; iunfold worldInv; iexists σ, S, p, Hl, W; iframe; ipureintro; exact Hok
      imodintro
      iframe Hw
    · iintro ⟨%Heq, Hs, -⟩
      imod Hclose2 with -
      imod ghostVar_update_halves (σ.notify pend) γ.σ _ _ $$ Hgσ Hw with ⟨Hgσ, Hw⟩
      iclear Hlb0
      imod Hclose $$ [Hs Hgσ HS Hreg Hpub Hpv Hpm] with -
      · inext; iunfold worldInv; iexists σ.notify pend, S, p, histAfter Hs P, W; iframe; iframe #
        ipureintro
        obtain ⟨h1, h2, h3, -, h5⟩ := Hok
        exact ⟨h1, h2, h3, histOkM_notify σ Hs pend P hok hlen hrev, h5⟩
      imodintro
      -- the commit step
      iauintro
      unfold atomic_acc
      iinv Hinv with >Hi Hclose
      iunfold worldInv at Hi
      icases Hi with ⟨%σ2, %S2, %p2, %Hl2, %W2, Hs, Hgσ, HS, Hreg, Hpub, Hpv, Hpm, Hlb2, %Hok2⟩
      iapply fupd_mask_intro (show (∅ : CoPset) ⊆ (⊤ \ ↑mvccN) \ ↑worldN from
        Std.LawfulSet.empty_subset)
      iintro Hclose2
      isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
      iexists σ2
      iframe Hs
      isplit
      · iintro Hs
        imod Hclose2 with -
        imod Hclose $$ [Hs Hgσ HS Hreg Hpub Hpv Hpm Hlb2] with -
        · inext; iunfold worldInv; iexists σ2, S2, p2, Hl2, W2; iframe; ipureintro; exact Hok2
        imodintro
        iframe Hw
      · iintro ⟨%Heq2, Hs⟩
        imod Hclose2 with -
        subst Heq2
        imod ghostVar_update_halves (commitSt σ pend) γ.σ _ _ $$ Hgσ Hw with ⟨Hgσ, Hw⟩
        imod Hclose $$ [Hs Hgσ HS Hreg Hpub Hpv Hpm Hlb2] with -
        · inext; iunfold worldInv; iexists commitSt σ pend, S2, p2, Hl2, W2; iframe
          ipureintro
          obtain ⟨h1, h2, h3, h4, h5⟩ := Hok2
          have hr := commitSt_rev_ge σ pend
          refine ⟨h1, h2, ?_, ?_, h5⟩
          · simp only [MvccState.rev, MvccState.notify] at h3 hr ⊢; omega
          · unfold histOkM at h4 ⊢; rw [commitSt_notifiedLog]; exact h4
        imodintro
        iexact Hw
  inext
  iintro ⟨Htt, Hrdr, Hbk, HQ⟩
  iapply HΦ
  iframe

end lemmas

end mvccrand
end EtcdGrove
end Perennial
