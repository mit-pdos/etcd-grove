/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/examples/rabianet/GhostAux.lean`, run `rabia-r1wake-1`.)

Auxiliary laws of the shared ghost state the client needs (internal to `rabianet`; each unfolds
`Ghost.lean`'s `rabiaInv`/`prefixFacts`, a missing law recorded in `notes/hub-requests.md`):
a registered command is the command of an input meeting the premise (`opState`'s), so the store
after the commands of a reply's `prefixFacts` holds no empty value (a get's reply tells "found"
by a non-empty value).
-/
module

public import Dsverify.Proof.rabia.Core.Ghost

@[expose] public section

noncomputable section

namespace Perennial.rabia

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model

section pure

/-- A store with no empty value. -/
def NoEmpty (s : KStore) : Prop := ∀ k, s k ≠ some []

theorem noEmpty_exec (s : KStore) (hs : NoEmpty s) (i : KvInput GoString GoString)
    (hi : inputOk i) : NoEmpty (execCmd s (cmdOf i)).1 := by
  have h := execCmd_step s i hi
  cases i with
  | get k =>
    obtain ⟨h1, -⟩ := h
    rw [h1]; exact hs
  | put k v =>
    obtain ⟨h1, -⟩ := h
    rw [h1]
    intro k'
    by_cases e : k' = k
    · simp only [e, ↓reduceIte, ne_eq, Option.some.injEq]; exact hi.2
    · simp only [e, ↓reduceIte]; exact hs k'

theorem noEmpty_foldl (L : List GoString) (hL : ∀ c ∈ L, ∃ i, c = cmdOf i ∧ inputOk i) :
    ∀ s, NoEmpty s → NoEmpty (L.foldl (fun s c => (execCmd s c).1) s) := by
  induction L with
  | nil => intro s hs; exact hs
  | cons c L ih =>
    intro s hs
    obtain ⟨i, rfl, hi⟩ := hL c (by simp)
    exact ih (fun c' h => hL c' (by simp [h])) _ (noEmpty_exec s hs i hi)

theorem noEmpty_stateOfCmds (L : List GoString) (hL : ∀ c ∈ L, ∃ i, c = cmdOf i ∧ inputOk i) :
    NoEmpty (stateOfCmds L) :=
  noEmpty_foldl L hL _ (fun _ => by simp)

end pure

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF]

attribute [local instance] GooseGlobalGS.gooseInvGS GooseGlobalGS.gooseAllG

instance isRabia_persistent' (γ : RabiaNames) : Persistent (isRabia (GF := GF) γ) := by
  unfold isRabia; infer_instance

theorem opState_inputOk (γ : RabiaNames) (M : Facts) (r : ReqId) :
    opState (GF := GF) γ M r ⊢
      ⌜∃ i, M (.reg r) = some (.cmd (cmdOf i)) ∧ inputOk i⌝ ∗ opState γ M r := by
  unfold opState
  iintro ⟨%γq, %i, Hq, %h, Hrest⟩
  isplitr
  · ipureintro; exact ⟨i, h⟩
  iexists γq, i
  iframe Hq Hrest
  ipureintro; exact h

theorem invAt_reg_inputOk (γ : RabiaNames) (M : Facts) (r : ReqId) (c : GoString) :
    rabiaInvAt (GF := GF) γ M ∗ fact γ (.reg r) (.cmd c) ⊢
      ⌜∃ i, c = cmdOf i ∧ inputOk i⌝ ∗ rabiaInvAt γ M := by
  unfold rabiaInvAt
  iintro ⟨⟨%MG, %KS, %n, Hf, %HMG, Hfs, Hk, %HKO, Hkw, %Hn, Hkv, HQS, HCS, Hops⟩, #Hreg⟩
  ihave %hl := fact_lookup γ MG _ _ $$ Hf Hreg
  icases (BigSepM.bigSepM_delete (Φ := fun k _ => opsTerm (GF := GF) γ M k) hl).1 $$ Hops
    with ⟨Hop, Hops⟩
  rw [opsTerm_reg]
  icases opState_inputOk γ M r $$ Hop with ⟨%hi, Hop⟩
  isplitr
  · ipureintro
    obtain ⟨i, h1, h2⟩ := hi
    rw [← HMG, hl] at h1
    exact ⟨i, by injection h1 with h; injection h, h2⟩
  iexists MG, KS, n
  iframe Hf Hfs Hk Hkw Hkv HQS HCS
  isplitr
  · ipureintro; exact HMG
  isplitr
  · ipureintro; exact HKO
  isplitr
  · ipureintro; exact Hn
  iapply (BigSepM.bigSepM_delete (Φ := fun k _ => opsTerm (GF := GF) γ M k) hl).2
  rw [opsTerm_reg]
  iframe Hop Hops

/-- A registered command is the command of an input meeting the premise. -/
theorem reg_inputOk (γ : RabiaNames) (E : CoPset) (hE : ↑rabiaN ⊆ E) (r : ReqId)
    (c : GoString) :
    isRabia (GF := GF) γ ∗ fact γ (.reg r) (.cmd c) ⊢
      |={E}=> ⌜∃ i, c = cmdOf i ∧ inputOk i⌝ := by
  unfold isRabia
  iintro ⟨#Hinv, #Hreg⟩
  imod inv_acc hE $$ Hinv with ⟨Hi, Hclose⟩
  unfold rabiaInv
  icases Hi with ⟨%M, >%HV, Hi⟩
  ihave Hx : ▷ (⌜∃ i, c = cmdOf i ∧ inputOk i⌝ ∗ rabiaInvAt γ M) $$ [Hi]
  · inext
    iapply invAt_reg_inputOk γ M r c $$ [Hi]
    iframe Hi; iexact Hreg
  icases Hx with ⟨>%h, Hi⟩
  imod Hclose $$ [Hi] with -
  · inext
    iexists M
    iframe Hi
    ipureintro; exact HV
  imodintro
  ipureintro; exact h

/-- The commands at the indices `l` of a batch's registered commands are commands of inputs
meeting the premise. -/
theorem regFacts_inputOk_at (γ : RabiaNames) (E : CoPset) (hE : ↑rabiaN ⊆ E) (rs : List ReqId)
    (bc : List GoString) :
    ∀ l : List Nat, isRabia (GF := GF) γ ∗ regFacts γ rs bc ⊢
      |={E}=> ⌜∀ i ∈ l, ∀ c, bc[i]? = some c → ∃ x, c = cmdOf x ∧ inputOk x⌝
  | [] => by
    iintro -
    imodintro; ipureintro; simp
  | i :: l => by
    iintro ⟨#Hinv, #Hr⟩
    imod regFacts_inputOk_at γ E hE rs bc l $$ [Hinv Hr] with %hl
    · iframe #
    ihave #Hr' := Hr
    iunfold regFacts at Hr'
    icases Hr' with ⟨%hlen, #Hall⟩
    rcases h : rs[i]? with _ | r
    · imodintro; ipureintro
      intro j hj c hc
      rcases List.mem_cons.mp hj with rfl | hj
      · exfalso
        have : j < bc.length := (List.getElem?_eq_some_iff.1 hc).1
        rw [List.getElem?_eq_none_iff] at h; omega
      · exact hl j hj c hc
    ihave ⟨%cm, %hcm, #Hreg⟩ := (BigSepL.bigSepL_lookup (i := i) h) $$ Hall
    imod reg_inputOk γ E hE r cm $$ [Hinv Hreg] with %h1
    · iframe #
    imodintro; ipureintro
    intro j hj c hc
    rcases List.mem_cons.mp hj with rfl | hj
    · rw [hcm] at hc; cases hc; exact h1
    · exact hl j hj c hc

theorem regFacts_inputOk (γ : RabiaNames) (E : CoPset) (hE : ↑rabiaN ⊆ E) (rs : List ReqId)
    (bc : List GoString) :
    isRabia (GF := GF) γ ∗ regFacts γ rs bc ⊢ |={E}=> ⌜∀ c ∈ bc, ∃ x, c = cmdOf x ∧ inputOk x⌝ := by
  iintro H
  imod regFacts_inputOk_at γ E hE rs bc (List.range bc.length) $$ H with %h
  imodintro; ipureintro
  intro c hc
  obtain ⟨i, hi, hci⟩ := List.getElem_of_mem hc
  exact h i (List.mem_range.2 hi) c (by rw [List.getElem?_eq_getElem hi, hci])

/-- The commands of a prefix of decided slots are commands of inputs meeting the premise. -/
theorem prefix_inputOk (γ : RabiaNames) (E : CoPset) (hE : ↑rabiaN ⊆ E) :
    ∀ (s : Nat) (cmds : List GoString),
    isRabia (GF := GF) γ ∗ prefixFacts γ s cmds ⊢
      |={E}=> ⌜∀ c ∈ cmds, ∃ i, c = cmdOf i ∧ inputOk i⌝ ∗ prefixFacts γ s cmds
  | 0, cmds => by
    simp only [prefixFacts]
    iintro ⟨-, %h⟩
    imodintro
    isplitr
    · ipureintro; subst h; simp
    · ipureintro; exact h
  | s + 1, cmds => by
    iintro ⟨#Hinv, Hp⟩
    simp only [prefixFacts]
    icases Hp with ⟨%cmds0, %d, Hp, #Hdec, Hd⟩
    imod prefix_inputOk γ E hE s cmds0 $$ [Hp] with ⟨%h0, Hp⟩
    · iframe Hinv; iexact Hp
    cases d with
    | null =>
      icases Hd with %e
      imodintro
      isplitr
      · ipureintro; subst e; exact h0
      iexists cmds0, DVal.null
      iframe Hp Hdec
      ipureintro; exact e
    | obj id =>
      icases Hd with ⟨%rs, %bc, #Hpo, #Hreg, %e⟩
      imod regFacts_inputOk γ E hE rs bc $$ [Hinv Hreg] with %h1
      · iframe Hinv; iexact Hreg
      imodintro
      isplitr
      · ipureintro
        subst e
        intro c hc
        rcases List.mem_append.mp hc with hc | hc
        · exact h0 c hc
        · exact h1 c hc
      iexists cmds0, DVal.obj id
      iframe Hp Hdec
      iexists rs, bc
      iframe Hpo Hreg
      ipureintro; exact e

end laws

end Perennial.rabia
