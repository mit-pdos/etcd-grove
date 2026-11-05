/-
**The two-step commit's ghost steps from the client's updates** (M4, track B, 2026-11-06;
`notes/mvcc-api-invariants.md` §3). Lean-first (no Rocq counterpart). Over the sealed definitions of
`Api.lean` (imported with `import all`).

`Txn.End.contract`'s precondition, for a write transaction begun at `σ₀`, is the client's nested
update: the notify step (`σ₀` to `σ₀.notify pend`, with the receipt of the history it makes), then
the commit (`commitPending`). The internal `End`s take the moves of the API's slots as their caller's
step (`Api/TxnSteps.lean`: `endCb`); this module makes that step from the client's update, for a
transaction whose writer's slot is at `σ₀` (`Yat γ σ₀`: the writer's quarter of the view at
`σ₀.log`, `σ₀.crev`, its part of the pending revision at `none`, the records' half at `σ₀.crev`):

* `endCb_of_au`: a store without watchers (the writer's part of the pending revision a half): with
  no change, both of the client's steps by agreement at the check-in (the state unchanged, its
  receipt the certificate's); with one, both at the bump, the view and the pending revision moved
  with `s.revMu`'s quarter (`slotX`, at the transaction's compaction revision, which the writer's
  agrees with) and the writer's, the notified log's authority extended, the receipt the committed
  log's certificate's.
* `Yat_slotY`: the writer's slot at `σ₀` is the writer's slot at its log.

The watchable store's notify step (`wsEndCb`) is not made here: its no-change arm is stated at the
writer's `slotY` (the watchable `End`'s transaction carries `slotY`, not `Yat`), so it needs the
transaction's slot at `σ₀` carried from `Write` (the hand-off, "track B").
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
import all Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.TxnSteps

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc
namespace api

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

/-! ## The pure steps -/

theorem MvccState.ext' {σ σ' : MvccState} (h1 : σ.log = σ'.log) (h2 : σ.crev = σ'.crev)
    (h3 : σ.pending = σ'.pending) : σ = σ' := by
  cases σ; cases σ'; simp_all

theorem notify_nil_of {σ : MvccState} (h : σ.pending = none) : σ.notify [] = σ :=
  MvccState.ext' rfl rfl (by simp [MvccState.notify, h])

theorem commitPending_of_none {σ : MvccState} (h : σ.pending = none) : σ.commitPending = σ :=
  MvccState.ext' (by simp [MvccState.commitPending, h, commitLog]) rfl
    (by simp [MvccState.commitPending, h])

theorem notify_cons_pending {σ : MvccState} {pend : List Change} (h : pend ≠ []) :
    (σ.notify pend).pending = some pend := by
  simp [MvccState.notify, h]

theorem notify_cons_commit_log {σ : MvccState} {pend : List Change} (h : pend ≠ []) :
    (σ.notify pend).commitPending.log = σ.log ++ [pend] := by
  simp [MvccState.commitPending, MvccState.notify, h, commitLog]

theorem notifiedLog_none {σ : MvccState} (h : σ.pending = none) : σ.notifiedLog = σ.log := by
  simp [MvccState.notifiedLog, h]

/-! ## The writer's slot at a state -/

section steps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **The writer's slot at the state `σ`** (`slotY` with its compaction revision named). -/
def Yat (γ : StoreNames) (σ : MvccState) : IProp GF :=
  iprop(absPart γ.api (1 : Qp).half.half σ.log σ.crev ∗ pndPart γ.api (pndW γ) none ∗
    rcvW γ (1 : Qp).half σ.crev)

theorem Yat_slotY (γ : StoreNames) (σ : MvccState) : Yat (GF := GF) γ σ ⊢ slotY γ σ.log := by
  iintro H
  iunfold Yat at H
  icases H with ⟨Ha, Hp, Hr⟩
  iunfold slotY
  iexists σ.crev
  iframe Ha Hp Hr

/-- The client's update, nested (`Txn.End.contract`'s write arm, `mvccState` unfolded to its body
at the store's names `γ`). -/
abbrev endAU (γ : StoreNames) (σ₀ : MvccState) (pend : List Change) (Q : IProp GF) : IProp GF :=
  iprop(AU <{ ∃∃ (σ : MvccState), mvccStateI γ.api σ }> @ ⊤ \ ↑mvccN, ∅
    <{ ⌜σ = σ₀⌝ ∗ mvccStateI γ.api (σ.notify pend) ∗ ⧖ (logCh (σ.log ++ [pend])), COMM
        AU <{ ∃∃ (σ' : MvccState), mvccStateI γ.api σ' }> @ ⊤ \ ↑mvccN, ∅
          <{ ⌜σ' = σ₀.notify pend⌝ ∗ mvccStateI γ.api σ'.commitPending, COMM Q }> }>)

theorem absPart_quarters (a : AbsNames) (L : Log) (c : Int) :
    absPart (GF := GF) a (1 : Qp).half.half L c ∗ absPart a (1 : Qp).half.half L c ⊢
      absPart a (1 : Qp).half L c := by
  have h := (absPart_fractional (GF := GF) a L c).fractional (1 : Qp).half.half (1 : Qp).half.half
  rw [Qp.half_add_half] at h
  exact h.2

theorem absPart_halves (a : AbsNames) (L : Log) (c : Int) :
    absPart (GF := GF) a (1 : Qp).half L c ⊢
      absPart a (1 : Qp).half.half L c ∗ absPart a (1 : Qp).half.half L c := by
  have h := (absPart_fractional (GF := GF) a L c).fractional (1 : Qp).half.half (1 : Qp).half.half
  rw [Qp.half_add_half] at h
  exact h.1

/-- **The commit's step from the client's update** (a store without watchers; see the header). -/
theorem endCb_of_au (γ : StoreNames) (σ₀ : MvccState) (ilog : Log) (pend : List Change) (crev : Int)
    (Q : IProp GF) (hw : γ.watchQ = false) (hl : σ₀.log = ilog)
    (hp : σ₀.pending = none) :
    endAU γ σ₀ pend Q ⊢ endCb γ ilog pend crev (Yat γ σ₀) Q := by
  have hpw : pndW γ = (1 : Qp).half := by
    unfold pndW; rw [hw]; rfl
  subst hl
  iintro Hau
  by_cases hpe : pend = []
  · subst hpe
    iapply (endCb_nil_iff γ σ₀.log crev _ Q).2
    iintro #Hcert HY
    iunfold Yat at HY
    icases HY with ⟨HYa, HYp, HYr⟩
    ihave Hau := atomic_update_mask_weaken (Eo1 := ⊤ \ ↑mvccN) (Eo2 := ⊤)
      (fun _ _ => CoPset.mem_full) $$ Hau
    ihave Hacc := aupd_aacc $$ Hau
    unfold atomic_acc
    imod Hacc with Hacc
    isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
    icases Hacc with ⟨%σ, Hσ, Hucl⟩
    icases Hucl with ⟨-, Hcommit⟩
    isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hcommit
    iunfold mvccStateI at Hσ
    icases Hσ with ⟨Ha, Hp, Hcr, Hnl, %Hreach⟩
    ihave %Hag := absPart_agree _ _ _ _ _ _ _ $$ [Ha HYa]
    · iframe Ha HYa
    ihave %Hpg := pndPart_agree _ _ _ _ _ $$ [Hp HYp]
    · iframe Hp HYp
    have hσ : σ = σ₀ := MvccState.ext' Hag.1 Hag.2 (by rw [Hpg, hp])
    subst hσ
    ihave #Hr := idxCert_rcpt _ _ $$ Hcert
    ihave #Hr' : ⧖ (logCh (σ.log ++ [[]])) $$ []
    · rw [logCh_append_nil]; iexact Hr
    imod Hcommit $$ [Ha Hp Hcr Hnl] with Hau2
    · isplitr
      · ipureintro; rfl
      rw [notify_nil_of hp]
      iframe Hr'
      iunfold mvccStateI
      iframe Ha Hp Hcr Hnl
      ipureintro; exact Hreach
    ihave Hau2 := atomic_update_mask_weaken (Eo1 := ⊤ \ ↑mvccN) (Eo2 := ⊤)
      (fun _ _ => CoPset.mem_full) $$ Hau2
    ihave Hacc := aupd_aacc $$ Hau2
    unfold atomic_acc
    imod Hacc with Hacc
    isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
    icases Hacc with ⟨%σ', Hσ, Hucl⟩
    icases Hucl with ⟨-, Hcommit⟩
    isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hcommit
    iunfold mvccStateI at Hσ
    icases Hσ with ⟨Ha, Hp, Hcr, Hnl, %Hreach'⟩
    ihave %Hag' := absPart_agree _ _ _ _ _ _ _ $$ [Ha HYa]
    · iframe Ha HYa
    ihave %Hpg' := pndPart_agree _ _ _ _ _ $$ [Hp HYp]
    · iframe Hp HYp
    have hσ' : σ' = σ := MvccState.ext' Hag'.1 Hag'.2 (by rw [Hpg', hp])
    subst hσ'
    imod Hcommit $$ [Ha Hp Hcr Hnl] with HQ
    · isplitr
      · ipureintro; exact (notify_nil_of hp).symm
      rw [commitPending_of_none hp]
      iunfold mvccStateI
      iframe Ha Hp Hcr Hnl
      ipureintro; exact Hreach'
    imodintro
    iframe HQ
    iapply Yat_slotY
    iunfold Yat
    iframe HYa HYp HYr
  · iapply (endCb_cons_iff γ σ₀.log pend hpe crev _ Q).2
    iintro #Hcert ⟨HX, HY⟩
    iunfold Yat at HY
    icases HY with ⟨HYa, HYp, HYr⟩
    iunfold slotX at HX
    iunfold revMuAbs at HX
    icases HX with ⟨HXa, HXc⟩
    ihave %HagY := absPart_agree _ _ _ _ _ _ _ $$ [HXa HYa]
    · iframe HXa HYa
    have hc : σ₀.crev = crev := HagY.2.symm
    subst hc
    ihave Hau := atomic_update_mask_weaken (Eo1 := ⊤ \ ↑mvccN) (Eo2 := ⊤)
      (fun _ _ => CoPset.mem_full) $$ Hau
    ihave Hacc := aupd_aacc $$ Hau
    unfold atomic_acc
    imod Hacc with Hacc
    isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
    icases Hacc with ⟨%σ, Hσ, Hucl⟩
    icases Hucl with ⟨-, Hcommit⟩
    isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hcommit
    iunfold mvccStateI at Hσ
    icases Hσ with ⟨Ha, Hp, Hcr, Hnl, %Hreach⟩
    ihave %Hag := absPart_agree _ _ _ _ _ _ _ $$ [Ha HYa]
    · iframe Ha HYa
    ihave %Hpg := pndPart_agree _ _ _ _ _ $$ [Hp HYp]
    · iframe Hp HYp
    have hσ : σ = σ₀ := MvccState.ext' Hag.1 Hag.2 (by rw [Hpg, hp])
    subst hσ
    -- the notification: the pending revision (the client's half and the writer's) and the notified
    -- log's authority
    rw [hpw]
    imod pndPart_update _ _ _ (Qp.half_add_half 1) _ _ (some pend) $$ [Hp HYp] with ⟨Hp, HYp⟩
    · iframe Hp HYp
    iunfold nlAuth at Hnl
    rw [notifiedLog_none hp]
    imod monoListAuthOwn_update_app [pend] $$ Hnl with ⟨Hnl, -⟩
    ihave #Hc3 := Hcert
    iunfold idxCert at Hc3
    icases Hc3 with ⟨-, %Hlwf, -, #Hr⟩
    have hwf : LogWf (σ.log ++ [pend]) := ⟨Hlwf.1.1 (by simp), Hlwf.1.2⟩
    have e1 : σ.notify pend = ⟨σ.log, σ.crev, some pend⟩ :=
      MvccState.ext' rfl rfl (notify_cons_pending hpe)
    have hreach1 : MvccReachable (⟨σ.log, σ.crev, some pend⟩ : MvccState) :=
      e1 ▸ MvccReachable.notify σ pend Hreach hp hwf
    imod Hcommit $$ [Ha Hp Hcr Hnl] with Hau2
    · isplitr
      · ipureintro; rfl
      rw [e1]
      iframe Hr
      iunfold mvccStateI
      simp only [MvccState.notifiedLog]
      iframe Ha Hp Hcr
      isplitl [Hnl]
      · iunfold nlAuth; iexact Hnl
      ipureintro; exact hreach1
    -- the commit: the view (the client's half, `s.revMu`'s quarter and the writer's), the pending
    -- revision back
    ihave Hau2 := atomic_update_mask_weaken (Eo1 := ⊤ \ ↑mvccN) (Eo2 := ⊤)
      (fun _ _ => CoPset.mem_full) $$ Hau2
    ihave Hacc := aupd_aacc $$ Hau2
    unfold atomic_acc
    imod Hacc with Hacc
    isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
    icases Hacc with ⟨%σ', Hσ, Hucl⟩
    icases Hucl with ⟨-, Hcommit⟩
    isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hcommit
    iunfold mvccStateI at Hσ
    icases Hσ with ⟨Ha, Hp, Hcr, Hnl, %Hreach'⟩
    ihave %Hag' := absPart_agree _ _ _ _ _ _ _ $$ [Ha HYa]
    · iframe Ha HYa
    ihave %Hpg' := pndPart_agree _ _ _ _ _ $$ [Hp HYp]
    · iframe Hp HYp
    have hσ' : σ' = σ.notify pend :=
      MvccState.ext' Hag'.1 Hag'.2 (by rw [Hpg', notify_cons_pending hpe])
    subst hσ'
    ihave HXY := absPart_quarters _ _ _ $$ [HXa HYa]
    · iframe HXa HYa
    have hl2 : (σ.notify pend).log = σ.log := rfl
    have hc2 : (σ.notify pend).crev = σ.crev := rfl
    ihave Ha : absPart _ (1 : Qp).half σ.log σ.crev $$ [Ha]
    · rw [← hl2, ← hc2]; iexact Ha
    imod absPart_update _ _ _ (Qp.half_add_half 1) _ _ (σ.log ++ [pend]) _ _ σ.crev $$ [Ha HXY]
      with ⟨Ha, HXY⟩
    · iframe Ha HXY
    icases absPart_halves _ _ _ $$ HXY with ⟨HXa, HYa⟩
    imod pndPart_update _ _ _ (Qp.half_add_half 1) _ _ none $$ [Hp HYp] with ⟨Hp, HYp⟩
    · iframe Hp HYp
    have e2 : (σ.notify pend).commitPending = ⟨σ.log ++ [pend], σ.crev, none⟩ :=
      MvccState.ext' (notify_cons_commit_log hpe) rfl rfl
    have hreach2 : MvccReachable (⟨σ.log ++ [pend], σ.crev, none⟩ : MvccState) :=
      e2 ▸ MvccReachable.commit _ Hreach'
    have hn2 : (σ.notify pend).notifiedLog = σ.log ++ [pend] := by
      rw [MvccState.notify_notifiedLog]; unfold commitLog; rw [if_neg hpe]
    ihave Hnl : nlAuth _ 1 (σ.log ++ [pend]) $$ [Hnl]
    · rw [← hn2]; iexact Hnl
    ihave Hcr : crevAuth _ (1 : Qp).half σ.crev $$ [Hcr]
    · rw [← hc2]; iexact Hcr
    imod Hcommit $$ [Ha Hp Hcr Hnl] with HQ
    · isplitr
      · ipureintro; rfl
      rw [e2]
      iunfold mvccStateI
      simp only [MvccState.notifiedLog]
      iframe Ha Hp Hcr Hnl
      ipureintro; exact hreach2
    imodintro
    iframe HQ
    isplitl [HXa HXc]
    · iunfold slotX; iunfold revMuAbs; iframe HXa HXc
    iunfold slotY
    iexists σ.crev
    rw [hpw]
    iframe HYa HYp HYr

end steps

end api
end mvcc
end EtcdGrove
end Perennial
