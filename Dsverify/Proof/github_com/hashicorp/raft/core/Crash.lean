/-
(hraft_robust L0, R1 §1.3–§3; stage R2 proves it) **The crash laws of one server**: opening its crash
invariant `srvDurInv` (with the generation's crash token), the views' agreement and update, arming a
generation (`raft_arm`, at boot, before the generation's WP) and the crash (`raft_crash`: the next
generation's vacant state from the dead one's, firing its pending steps).

The definitions (`SrvDur`, `durBody`, `srvDurInv`, the views `srvV`/`srvVP`/`stV`/`termV`/`cidxV`,
`Pend`/`winRes`) are in `core/Defs.lean`. Statements marked "(R2)" are proved by stage R2; their exact
form may be refined there (with the lead's OK, `/shared/tmp/ps2/hraft/robust/HANDOFF.md`).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.core.Laws

@[expose] public section

set_option linter.unusedVariables false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace github_com.hashicorp.raft

open proto gprot

section crash
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

variable (γ : GNames) (rc : RCtx GF) (i : SID)

/-! ## Opening the crash invariant -/

/-- **Opening `srvDurInv`** with the generation's crash token (`inv_nc_acc`): the crash state's
body, and the closing update. The generic accessor; the laws below are its uses. -/
theorem durAcc {E : CoPset} (hE : ↑durN ⊆ E) :
    srvDurInv γ rc i ⊢ |NC={E, E \ ↑durN}=> ▷ (∃ X : SrvDur, durBody γ rc i X) ∗
      (▷ (∃ X : SrvDur, durBody γ rc i X) ={E \ ↑durN, E}=∗ True) := by
  unfold srvDurInv
  exact inv_nc_acc hE

/-- (R2) The main goroutine's view agrees with the crash state. -/
theorem durBody_srvVP_agree (X : SrvDur) (s : SState) (tp : Option TermPend) (dp : Option DiscPend) :
    durBody γ rc i X ∗ srvVP rc s tp dp ⊢ ⌜X.s = s ∧ X.tp = tp ∧ X.dp = dp⌝ := by
  sorry -- hraft_robust L0: R2

/-- (R2) The stable store's view agrees with the crash state. -/
theorem durBody_stV_agree (X : SrvDur) (D : StableAbs) :
    durBody γ rc i X ∗ stV rc D ⊢ ⌜X.D = D⌝ := by
  sorry -- hraft_robust L0: R2

/-- (R2) The term atomic's view agrees with the crash state's term. -/
theorem durBody_termV_agree (X : SrvDur) (t : Nat) :
    durBody γ rc i X ∗ termV rc t ⊢ ⌜X.s.term = t⌝ := by
  sorry -- hraft_robust L0: R2

/-- (R2) The commit index atomic's view agrees with the crash state's `cidx`. -/
theorem durBody_cidxV_agree (X : SrvDur) (c : Nat) :
    durBody γ rc i X ∗ cidxV rc c ⊢ ⌜X.s.cidx = c⌝ := by
  sorry -- hraft_robust L0: R2

/-- (R2) **A step of the main goroutine on the crash state**: with its view of `s` (and the pending
records `tp`, `dp`), any update of the body and the view together (the continuation may use gprot's
laws on the body's halves and must re-establish the couplings). The thin wrappers of gprot's laws
(`*_R`, stage R2) are its instances. -/
theorem durStep {E : CoPset} (hE : ↑durN ⊆ E) (s : SState) (tp : Option TermPend)
    (dp : Option DiscPend) (P : IProp GF) (Q : SrvDur → IProp GF) :
    srvDurInv γ rc i ∗ srvVP rc s tp dp ∗ P ∗
      (∀ X : SrvDur, ⌜X.s = s ∧ X.tp = tp ∧ X.dp = dp⌝ -∗ durBody γ rc i X -∗ srvVP rc s tp dp -∗ P -∗
        |={E \ ↑durN}=> ∃ X' : SrvDur, durBody γ rc i X' ∗ srvVP rc X'.s X'.tp X'.dp ∗ Q X') ⊢
      |NC={E}=> ∃ X' : SrvDur, srvVP rc X'.s X'.tp X'.dp ∗ Q X' := by
  sorry -- hraft_robust L0: R2

/-! ## Arming and crashing -/

/-- (hraft_robust L0, R1 §1.3, §6.1) **What a generation of server `i` starts from**: gprot's halves
and the stores' client authorities (`rc.ownL`, `rc.ownS`, `rc.ownSS`: the generation's handles, fixed before it
runs; `rc`'s names are not used) at the crash state `X`, with the couplings, but no generation's names yet (`raft_arm` allocates
them). A fresh server's is its genesis state; a restarted one's comes from `raft_crash`. -/
def srvVacant (X : SrvDur) : IProp GF :=
  iprop(srvOwn γ i X.s ∗ durView γ i (1 : Qp).half X.s.dur.1 ∗ logCouple γ i X.s.log ∗
    termCouple γ i X.s.term ∗ cidxCouple γ i X.s.cidx ∗
    rc.ownL X.A ∗ rc.ownS X.D ∗ rc.ownSS X.lat ∗
    ⌜logOk X.A X.s.log X.lo ∧ X.lo ≤ X.c + 1 ∧ voteMatches X.D X.s ∧ termDurOk X.D X.s X.tp ∧
      uint.nat X.A.ci ≤ X.s.dur.1 ∧ uint.nat X.A.staged ≤ X.s.dur.1 ∧ X.pend = none⌝ ∗
    latestOk γ rc X.lat ∗
    (⌜X.lat = none⌝ ∨ ∃ (m : SnapshotMeta) (b : List w8), ⌜X.lat = some (m, b)⌝ ∗
      (durLb γ i (uint.nat m.Index') ∨ snapFollow γ i (uint.nat m.Index') (uint.nat m.Term'))) ∗
    tpRes γ X.tp ∗ dpRes γ i X.s X.dp)

/-- (R2) **Arming a generation** (at boot, before its WP): fresh crash-state names, the crash
invariant (for the context `rc` with those names and the generation's store handles), the crash
token for the crash wand, and the generation's initial resources: the main goroutine's views, the
atomics' views, the `lastApplied` authority (at `0`, both halves), the compaction frontier's
authority (at `X.c`) and the main goroutine's half of the pending-install record (none). -/
theorem raft_arm (rc0 : RCtx GF) (X : SrvDur) :
    srvVacant γ rc0 i X ⊢ |==> ∃ dn : DurNames,
      srvDurInv γ { rc0 with dur := dn } i ∗ srvCrashTok { rc0 with dur := dn } ∗
      srvVP { rc0 with dur := dn } X.s X.tp X.dp ∗ stVS { rc0 with dur := dn } X.D X.A.staged ∗
      termV { rc0 with dur := dn } X.s.term ∗ cidxV { rc0 with dur := dn } X.s.cidx ∗
      monoNatAuthOwn dn.applied 1 0 ∗ monoNatAuthOwn dn.comp 1 X.c ∗
      ghostVar dn.pend (1 : Qp).half (none : Option (Nat × Nat × GoString)) := by
  sorry -- hraft_robust L0: R2

/-- (R2, R1 §1.3) **The crash of a generation**: with `crashed` and the generation's crash token, the
crash state is taken out of the invariant, its pending term step fired (`setTerm_upd`/`electTerm_upd`
from `tpRes`), the pending install record dropped, a write's window (`winRes`, given back by the
store's crash lemma when the write's new contents survived) fired (`pend_fire`), and the commit index
reset (`setCidx_upd … 0`, the atomic being volatile). The stores' authorities are the dead
generation's: the store's crash lemma (stage R3, `diskCrash`) re-keys them to the next generation's
handles at the surviving image, which is `X'`'s. -/
theorem raft_crash {E : CoPset} (hE : ↑gprotN ∪ ↑durN ⊆ E) (p : Option Pend) :
    crashed -∗ srvCrashTok rc -∗ srvDurInv γ rc i -∗ Inv γ -∗
      (match p with | none => iprop(True) | some p => winRes γ rc i p) ={E}=∗
      ∃ X' : SrvDur, srvVacant γ rc i X' ∗
        ⌜X'.s.cidx = 0 ∧ X'.tp = none⌝ := by
  sorry -- hraft_robust L0: R2

end crash

end github_com.hashicorp.raft

end Perennial
