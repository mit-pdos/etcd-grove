/-
**The watchable store's commit steps from the client's updates** (M4, track B, 2026-11-06;
`notes/mvcc-api-invariants.md` §3). Lean-first (no Rocq counterpart). Over the sealed definitions of
`Api.lean` (imported with `import all`).

`wsEndCbY_of_au`: the watchable `End`'s caller's step (`wsEndCbY`) from `Txn.End.contract`'s nested
update, for a transaction begun at `σ₀` (nothing pending) whose writer's slot is at `σ₀`'s log and
compaction revision (`slotYc`): with no change, the plain store's step (`endCb_nil_of_au`); with
one, the notify step at the notification under the watchable store's `s.mu` (the pending revision
from the client's half, the writer's quarter and the lock's, `wsSlot`'s; the notified log's
authority extended, its lower bound minted for the lock's slot and the watchers' sends; the receipt
and the log's well-formedness from the sealed log), and the commit step at the inner `End`'s bump
(the view from the client's half, `s.revMu`'s quarter and the writer's; the pending revision back
to `none` from the three parts).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
import all Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.EndSteps
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.WsTxnSteps

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc
namespace api

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section steps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem Yat_slotYc (γ : StoreNames) (σ : MvccState) :
    Yat (GF := GF) γ σ = slotYc γ σ.log σ.crev := rfl

theorem pndPart_quarters (a : AbsNames) (p : Option (List Change)) :
    pndPart (GF := GF) a (1 : Qp).half.half p ∗ pndPart a (1 : Qp).half.half p ⊢
      pndPart a (1 : Qp).half p := by
  have h := (pndPart_fractional (GF := GF) a p).fractional (1 : Qp).half.half (1 : Qp).half.half
  rw [Qp.half_add_half] at h
  exact h.2

theorem pndPart_halves (a : AbsNames) (p : Option (List Change)) :
    pndPart (GF := GF) a (1 : Qp).half p ⊢
      pndPart a (1 : Qp).half.half p ∗ pndPart a (1 : Qp).half.half p := by
  have h := (pndPart_fractional (GF := GF) a p).fractional (1 : Qp).half.half (1 : Qp).half.half
  rw [Qp.half_add_half] at h
  exact h.1

/-- **The watchable `End`'s step from the client's update** (see the header). -/
theorem wsEndCbY_of_au (γw : WsNames) (σ₀ : MvccState) (pend : List Change) (Q : IProp GF)
    (hw : γw.st.watchQ = true) (hp : σ₀.pending = none) :
    endAU γw.st σ₀ pend Q ⊢ wsEndCbY γw σ₀.log pend σ₀.crev Q := by
  have hpw : pndW γw.st = (1 : Qp).half.half := by
    unfold pndW; rw [hw]; rfl
  by_cases hpe : pend = []
  · subst hpe
    iintro Hau
    iapply (wsEndCbY_nil_iff γw σ₀.log σ₀.crev Q).2
    rw [← Yat_slotYc]
    iapply endCb_nil_of_au γw.st σ₀ σ₀.crev Q hp $$ Hau
  iintro Hau
  iapply (wsEndCbY_cons_iff γw σ₀.log pend hpe σ₀.crev Q).2
  iintro #Hsl ⟨HY, HS⟩
  iunfold slotYc at HY
  icases HY with ⟨HYa, HYp, HYr, HYw⟩
  iunfold wsSlot at HS
  icases HS with ⟨HSp, -⟩
  rw [hpw]
  -- the notify step: the state is `σ₀` by agreement
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
  -- the pending revision: the client's half, the writer's quarter and the lock's
  ihave HWS := pndPart_quarters _ _ $$ [HYp HSp]
  · iframe HYp HSp
  imod pndPart_update _ _ _ (Qp.half_add_half 1) _ _ (some pend) $$ [Hp HWS] with ⟨Hp, HWS⟩
  · iframe Hp HWS
  icases pndPart_halves _ _ $$ HWS with ⟨HYp, HSp⟩
  -- the notified log's authority, extended; its lower bound
  iunfold nlAuth at Hnl
  rw [notifiedLog_none hp]
  imod monoListAuthOwn_update_app [pend] $$ Hnl with ⟨Hnl, #Hnlb⟩
  ihave #Hsl3 := Hsl
  iunfold idxSealed at Hsl3
  icases Hsl3 with ⟨-, %Hlwf, #Hr⟩
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
  imodintro
  isplitr
  · iunfold nlLb; iexact Hnlb
  -- the commit step, at the inner `End`'s bump
  icombine HYa HYp HYr HYw HSp Hau2 as Hall
  iexists _
  isplitl [Hall]
  · iexact Hall
  iapply (endCb_cons_iff γw.st σ.log pend hpe σ.crev _ _).2
  iintro #Hcert ⟨HX, HYa, HYp, HYr, HYw, HSp, Hau2⟩
  iunfold slotX at HX
  iunfold revMuAbs at HX
  icases HX with ⟨HXa, HXc⟩
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
  -- the view: the client's half, `s.revMu`'s quarter and the writer's
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
  -- the pending revision back to none: the client's half, the writer's quarter and the lock's
  ihave HWS := pndPart_quarters _ _ $$ [HYp HSp]
  · iframe HYp HSp
  imod pndPart_update _ _ _ (Qp.half_add_half 1) _ _ none $$ [Hp HWS] with ⟨Hp, HWS⟩
  · iframe Hp HWS
  icases pndPart_halves _ _ $$ HWS with ⟨HYp, HSp⟩
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
  isplitl [HYa HYp HYr HYw]
  · iunfold slotY
    iexists σ.crev
    rw [hpw]
    iframe HYa HYp HYr HYw
  iunfold wsSlot
  iframe HSp
  iunfold nlLb; iexact Hnlb

end steps

end api
end mvcc
end EtcdGrove
end Perennial
