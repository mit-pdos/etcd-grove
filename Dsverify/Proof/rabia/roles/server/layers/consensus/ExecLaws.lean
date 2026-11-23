/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/roles/server/layers/consensus/ExecLaws.lean`, run `rabia-r1wake-1`.)

The executor's laws: `fact_mine` (a missing law of Ghost.lean, H-K-6: proved by unfolding
`isRabia`, `rabiaInv`, `rabiaInvAt`, `KeysOk`), its converse `fact_of_mine`, and `exIdle_init`.
-/
module

public import Dsverify.Proof.rabia.roles.server.layers.consensus.ExecDefs

@[expose] public section

noncomputable section

namespace Perennial.rabia.roles.server.layers.consensus

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model NetConn Dsv rabia.internal.message
  rabia.internal.config rabia.internal.ledger rabia rabia.internal.queue

set_option linter.unusedSectionVars false

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable {cf : RCfg}

theorem fact_mine_proof (γ : RabiaNames) (E : CoPset) (hE : ↑rabiaN ⊆ E) (W : Writer)
    (K : List FKey) (key : FKey) (v : FVal) :
    isRabia (GF := GF) γ ∗ keysOf γ W K ∗ fact γ key v ⊢
      |={E}=> keysOf γ W K ∗ ⌜key.writer = some W → key ∈ K⌝ :=
  fact_mine γ E hE W K key v

/-- A key among the writer's keys is recorded. -/
theorem fact_of_mine (γ : RabiaNames) (E : CoPset) (hE : ↑rabiaN ⊆ E) (W : Writer)
    (K : List FKey) (key : FKey) (hw : key.writer = some W) (hk : key ∈ K) :
    isRabia (GF := GF) γ ∗ keysOf γ W K ⊢
      |={E}=> keysOf γ W K ∗ ∃ v, fact γ key v := by
  unfold isRabia
  iintro ⟨#Hinv, HK⟩
  imod inv_acc hE $$ Hinv with ⟨Hi, Hclose⟩
  unfold rabiaInv
  icases Hi with ⟨%M, >%HV, Hi⟩
  imod invAt_keys _ γ M W K $$ [Hi HK] with ⟨%hks, HK, Hi⟩
  · iframe
  have hm := (hks key hw).mp hk
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hm
  imod invAt_fact _ γ M key v hv $$ Hi with ⟨#Hx, Hi⟩
  imod Hclose $$ [Hi] with -
  · inext; iexists M; iframe Hi; ipureintro; exact HV
  imodintro
  iframe HK
  iexists v
  iexact Hx

theorem exLogOk_nil : ExLogOk [] := by
  unfold ExLogOk RoundsOrdered; simp

theorem exIdle_init_proof (γ : Names) (k : Nat) (γl : SrvNames) (γc : ConsNames) (ch : SrvChans)
    (c : Loc) :
    consExecRes (GF := GF) γ cf k γl γc ch c ⊢
      |==> exIdle γ cf k γl γc ch c { t := 0, H := [], cmds := [], Ke := [], L := [], sent := [] } := by
  iintro H
  unfold consExecRes
  icases H with ⟨#Hro, Hseq, Hcoin, ⟨%mp, Hdis, Hmap⟩, Hst, Htr, Hdist, Hslots, Hprod, Hex, HKe, -⟩
  imodintro
  unfold exIdle exCommon exFields freshSlots histFacts matchedToks
  have hm1 : (W64 (2 ^ 64 - 1) : w64) = W64 (((0 : Nat) : Int) - 1) := by decide
  rw [← hm1]
  isplitl [Hdis Hmap Hst Htr Hdist Hslots Hprod Hex HKe]
  · isplitr
    · iexact Hro
    isplitl [Hdis Hmap Hst Htr Hdist]
    · isplitl [Hdis Hmap]
      · iexists mp, ∅; iframe
      isplitl [Hst]
      · iexact Hst
      isplitl [Htr]
      · iexact Htr
      · iexact Hdist
    isplitr
    · iapply (BigSepL.bigSepL_nil).2; iempintro
    isplitr
    · iapply (BigSepL.bigSepL_nil).2; iempintro
    isplitr
    · ipureintro; rfl
    isplitr
    · unfold prefixFacts; ipureintro; rfl
    isplitl [HKe]
    · iexact HKe
    isplitr
    · ipureintro; exact ⟨fun _ h => by simp at h, fun _ h => by simp at h⟩
    isplitl [Hex]
    · iexact Hex
    isplitl [Hprod]
    · iexact Hprod
    isplitr
    · ipureintro; exact ⟨rfl, exLogOk_nil, fun _ h => by simp at h, fun _ h => by omega⟩
    iapply BigSepL.bigSepL_mono_of_forall (fun {_ _} => ?_) $$ Hslots
    simp only [Nat.zero_le, ↓reduceIte]
    exact .rfl
  isplitl [Hcoin]
  · iexact Hcoin
  isplitl [Hseq]
  · iexact Hseq
  · ipureintro; show 0 ≤ lenLedger; unfold lenLedger; omega

end laws

end Perennial.rabia.roles.server.layers.consensus

