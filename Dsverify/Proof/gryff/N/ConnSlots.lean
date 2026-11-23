/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/N/ConnSlots.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit N1: splitting the peer slices into the dialer's, the acceptor's and the own slot, and
joining them back (`ConnectToPeers`)
-/
module

public import Dsverify.Proof.gryff.N.WaitPeers

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.netN

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto

attribute [local instance] GooseGlobalGS.gooseInvGS

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]


/-- The lower peers (dialed). -/
def below (k : Fin 3) : Fin 3 → Bool := fun j => decide (j < k)
/-- The own slot (never written). -/
def atk (k : Fin 3) : Fin 3 → Bool := fun j => decide (j = k)

theorem slot_dist (γ : GryffNames GF) (k : Fin 3) (S : PeerSlices) (j : Fin 3) (b : Bool) :
    slotOwn γ k S j b ⊢ (if below k j then slotOwn γ k S j b else True) ∗
      (if above k j then slotOwn γ k S j b else True) ∗
      (if atk k j then slotOwn γ k S j b else True) := by
  iintro H
  unfold below above atk
  rcases Nat.lt_trichotomy j.val k.val with h | h | h
  · have h1 : j < k := h
    have h2 : ¬ k < j := fun h' => absurd (Fin.lt_def.1 h') (by omega)
    have h3 : ¬ j = k := fun h' => by subst h'; omega
    simp only [h1, h2, h3, _root_.decide_true, _root_.decide_false, ↓reduceIte, Bool.false_eq_true]
    iframe H
    isplitl <;> itrivial
  · have h1 : ¬ j < k := fun h' => absurd (Fin.lt_def.1 h') (by omega)
    have h2 : ¬ k < j := fun h' => absurd (Fin.lt_def.1 h') (by omega)
    have h3 : j = k := Fin.ext h
    subst h3
    simp only [h1, _root_.decide_true, _root_.decide_false, ↓reduceIte, Bool.false_eq_true]
    isplitr; itrivial
    isplitr; itrivial
    iexact H
  · have h1 : ¬ j < k := fun h' => absurd (Fin.lt_def.1 h') (by omega)
    have h2 : k < j := h
    have h3 : ¬ j = k := fun h' => by subst h'; omega
    simp only [h1, h2, h3, _root_.decide_true, _root_.decide_false, ↓reduceIte, Bool.false_eq_true]
    isplitr; itrivial
    iframe H

/-- The four slices as three slots (`ConnectToPeers`' start). -/
theorem slices_split (γ : GryffNames GF) (k : Fin 3) (S : PeerSlices) :
    S.pS ↦* List.replicate 3 interface.nil ∗ S.rS ↦* List.replicate 3 null ∗
      S.wS ↦* List.replicate 3 null ∗ S.aS ↦* List.replicate 3 false ⊢
    ⌜sliceShape S.pS 3 ∧ sliceShape S.rS 3 ∧ sliceShape S.wS 3 ∧ sliceShape S.aS 3⌝ ∗
    slots γ k S (below k) (fun _ => false) ∗ slots γ k S (above k) (fun _ => false) ∗
      slots γ k S (atk k) (fun _ => false) := by
  iintro ⟨Hp, Hr, Hw, Ha⟩
  icases ownSlice_elems _ _ (by simp) $$ Hp with ⟨%hp, Hp⟩
  icases ownSlice_elems _ _ (by simp) $$ Hr with ⟨%hr, Hr⟩
  icases ownSlice_elems _ _ (by simp) $$ Hw with ⟨%hw, Hw⟩
  icases ownSlice_elems _ _ (by simp) $$ Ha with ⟨%ha, Ha⟩
  simp only [List.length_replicate] at hp hr hw ha
  isplitr
  · ipureintro; exact ⟨hp, hr, hw, ha⟩
  simp only [List.replicate, BigSepL.bigSepL_cons, BigSepL.bigSepL_nil]
  icases Hp with ⟨Hp0, Hp1, Hp2, -⟩
  icases Hr with ⟨Hr0, Hr1, Hr2, -⟩
  icases Hw with ⟨Hw0, Hw1, Hw2, -⟩
  icases Ha with ⟨Ha0, Ha1, Ha2, -⟩
  ihave H0 : slotOwn γ k S 0 false $$ [Hp0 Hr0 Hw0 Ha0]
  · iunfold slotOwn; iexists _, _, _, _; iunfold cellsAt
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show ((((0 : Fin 3) : Nat)) : Int) = ((0 : Nat) : Int) from rfl]
    iframe
    ipureintro; rfl
  ihave H1 : slotOwn γ k S 1 false $$ [Hp1 Hr1 Hw1 Ha1]
  · iunfold slotOwn; iexists _, _, _, _; iunfold cellsAt
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show ((((1 : Fin 3) : Nat)) : Int) = ((0 + 1 : Nat) : Int) from rfl]
    iframe
    ipureintro; rfl
  ihave H2 : slotOwn γ k S 2 false $$ [Hp2 Hr2 Hw2 Ha2]
  · iunfold slotOwn; iexists _, _, _, _; iunfold cellsAt
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show ((((2 : Fin 3) : Nat)) : Int) = ((0 + 1 + 1 : Nat) : Int) from rfl]
    iframe
    ipureintro; rfl
  icases slot_dist γ k S 0 false $$ H0 with ⟨A0, B0, C0⟩
  icases slot_dist γ k S 1 false $$ H1 with ⟨A1, B1, C1⟩
  icases slot_dist γ k S 2 false $$ H2 with ⟨A2, B2, C2⟩
  unfold slots
  iframe

/-- A predicate at each of the three ids. -/
def tri (P : Fin 3 → IProp GF) : IProp GF := iprop(P 0 ∗ P 1 ∗ P 2)

theorem tri_acc (P P' : Fin 3 → IProp GF) (q : Fin 3) (h : ∀ j, j ≠ q → P j = P' j) :
    tri P ⊢ P q ∗ (P' q -∗ tri P') := by
  unfold tri
  iintro ⟨H0, H1, H2⟩
  obtain ⟨q, hq3⟩ := q
  rcases q with _ | _ | _ | q
  · rw [show (⟨_, hq3⟩ : Fin 3) = 0 from Fin.ext rfl]
    rw [h 1 (by intro e; have := congrArg Fin.val e; simp at this),
      h 2 (by intro e; have := congrArg Fin.val e; simp at this)]
    iframe H0; iintro H; iframe
  · rw [show (⟨_, hq3⟩ : Fin 3) = 1 from Fin.ext rfl]
    rw [h 0 (by intro e; have := congrArg Fin.val e; simp at this),
      h 2 (by intro e; have := congrArg Fin.val e; simp at this)]
    iframe H1; iintro H; iframe
  · rw [show (⟨_, hq3⟩ : Fin 3) = 2 from Fin.ext rfl]
    rw [h 0 (by intro e; have := congrArg Fin.val e; simp at this),
      h 1 (by intro e; have := congrArg Fin.val e; simp at this)]
    iframe H2; iintro H; iframe
  · omega

theorem tri_sep (P Q : Fin 3 → IProp GF) : tri (fun j => iprop(P j ∗ Q j)) ⊣⊢ tri P ∗ tri Q := by
  unfold tri
  show iprop((P 0 ∗ Q 0) ∗ (P 1 ∗ Q 1) ∗ (P 2 ∗ Q 2)) ⊣⊢ _
  constructor
  · iintro ⟨⟨A0, B0⟩, ⟨A1, B1⟩, ⟨A2, B2⟩⟩; iframe
  · iintro ⟨⟨A0, A1, A2⟩, ⟨B0, B1, B2⟩⟩; iframe

/-- The peers of `k` as the ids other than `k`. -/
theorem peers_tri (k : Fin 3) (Φ : Fin 3 → IProp GF) :
    ([∗list] q ∈ replica2.peers k, Φ q) ⊣⊢ tri (fun j => if j = k then iprop(True) else Φ j) := by
  unfold tri replica2.peers
  obtain ⟨k, hk⟩ := k
  rcases k with _ | _ | _ | k
  · rw [show (⟨_, hk⟩ : Fin 3) = 0 from Fin.ext rfl]
    rw [show (List.finRange 3).filter (fun x => decide (x ≠ (0 : Fin 3))) = [1, 2] from by decide]
    simp (config := {decide := true}) only [↓reduceIte, BigSepL.bigSepL_cons, BigSepL.bigSepL_nil]
    constructor
    · iintro ⟨H1, H2, -⟩; iframe
    · iintro ⟨-, H1, H2⟩; iframe; iapply BigSepL.bigSepL_nil.2; iempintro
  · rw [show (⟨_, hk⟩ : Fin 3) = 1 from Fin.ext rfl]
    rw [show (List.finRange 3).filter (fun x => decide (x ≠ (1 : Fin 3))) = [0, 2] from by decide]
    simp (config := {decide := true}) only [↓reduceIte, BigSepL.bigSepL_cons, BigSepL.bigSepL_nil]
    constructor
    · iintro ⟨H0, H2, -⟩; iframe
    · iintro ⟨H0, -, H2⟩; iframe; iapply BigSepL.bigSepL_nil.2; iempintro
  · rw [show (⟨_, hk⟩ : Fin 3) = 2 from Fin.ext rfl]
    rw [show (List.finRange 3).filter (fun x => decide (x ≠ (2 : Fin 3))) = [0, 1] from by decide]
    simp (config := {decide := true}) only [↓reduceIte, BigSepL.bigSepL_cons, BigSepL.bigSepL_nil]
    constructor
    · iintro ⟨H0, H1, -⟩; iframe
    · iintro ⟨H0, H1, -⟩; iframe; iapply BigSepL.bigSepL_nil.2; iempintro
  · omega

theorem ite_sep (c : Prop) [Decidable c] (A B : IProp GF) :
    (if c then iprop(True) else iprop(A ∗ B)) ⊢
      (if c then iprop(True) else A) ∗ (if c then iprop(True) else B) := by
  by_cases h : c
  · simp only [h, ↓reduceIte]; iintro -; isplitl <;> itrivial
  · simp only [h, ↓reduceIte]; iintro H; iexact H

theorem tri_merge (k : Fin 3) (A B : Fin 3 → IProp GF) :
    tri (fun j => if j = k then iprop(True) else A j) ∗
      tri (fun j => if j = k then iprop(True) else B j) ⊢
    tri (fun j => if j = k then iprop(True) else iprop(A j ∗ B j)) := by
  unfold tri
  iintro ⟨⟨A0, A1, A2⟩, ⟨B0, B1, B2⟩⟩
  isplitl [A0 B0]
  · by_cases h : (0 : Fin 3) = k
    · simp only [h, ↓reduceIte]; itrivial
    · simp only [h, ↓reduceIte] at *; iframe
  isplitl [A1 B1]
  · by_cases h : (1 : Fin 3) = k
    · simp only [h, ↓reduceIte]; itrivial
    · simp only [h, ↓reduceIte] at *; iframe
  · by_cases h : (2 : Fin 3) = k
    · simp only [h, ↓reduceIte]; itrivial
    · simp only [h, ↓reduceIte] at *; iframe

theorem slot_gather (γ : GryffNames GF) (k : Fin 3) (S : PeerSlices) (j : Fin 3) :
    (if below k j then slotOwn γ k S j true else True) ∗
      (if above k j then slotOwn γ k S j true else True) ∗
      (if atk k j then slotOwn γ k S j false else True) ⊢
    ∃ (cv : GoInterface) (rd w : Loc), cellsAt S j.val cv rd w (decide (j ≠ k)) ∗
      (if j = k then True else peerReaderB γ j k rd [] ∗ peerWriterB γ k j w []) := by
  iintro ⟨A, B, C⟩
  unfold below above atk
  rcases Nat.lt_trichotomy j.val k.val with h | h | h
  · have h1 : j < k := h
    have h2 : ¬ k < j := fun h' => absurd (Fin.lt_def.1 h') (by omega)
    have h3 : ¬ j = k := fun h' => by subst h'; omega
    simp only [h1, h2, h3, _root_.decide_true, _root_.decide_false, ↓reduceIte,
      Bool.false_eq_true]
    iunfold slotOwn at A
    simp only [↓reduceIte]
    icases A with ⟨%cv, %rd, %w, %al, Hc, %Hal, Hr, Hw⟩
    subst Hal
    iexists cv, rd, w
    rw [decide_eq_true h3]
    iframe
  · have h3 : j = k := Fin.ext h
    subst h3
    simp only [Fin.lt_irrefl, _root_.decide_true, _root_.decide_false, ↓reduceIte,
      Bool.false_eq_true]
    iunfold slotOwn at C
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases C with ⟨%cv, %rd, %w, %al, Hc, %Hal⟩
    subst Hal
    iexists cv, rd, w
    rw [show decide (j ≠ j) = false by simp]
    iframe
  · have h1 : ¬ j < k := fun h' => absurd (Fin.lt_def.1 h') (by omega)
    have h2 : k < j := h
    have h3 : ¬ j = k := fun h' => by subst h'; omega
    simp only [h1, h2, h3, _root_.decide_true, _root_.decide_false, ↓reduceIte,
      Bool.false_eq_true]
    iunfold slotOwn at B
    simp only [↓reduceIte]
    icases B with ⟨%cv, %rd, %w, %al, Hc, %Hal, Hr, Hw⟩
    subst Hal
    iexists cv, rd, w
    rw [decide_eq_true h3]
    iframe

/-- The three slots back as the four slices (`ConnectToPeers`' end), with the peers' readers
and writers, and `Alive` with the peers' entries true and the own entry false (N1-3). -/
theorem slices_join (γ : GryffNames GF) (k : Fin 3) (S : PeerSlices)
    (hS : sliceShape S.pS 3 ∧ sliceShape S.rS 3 ∧ sliceShape S.wS 3 ∧ sliceShape S.aS 3) :
    slots γ k S (below k) (fun _ => true) ∗ slots γ k S (above k) (fun _ => true) ∗
      slots γ k S (atk k) (fun _ => false) ⊢
    ∃ (cvs : List GoInterface) (rds ws : List Loc),
      ⌜rds.length = 3 ∧ ws.length = 3⌝ ∗
      S.pS ↦* cvs ∗ S.rS ↦* rds ∗ S.wS ↦* ws ∗ S.aS ↦* replica2.aliveList k ∗
      tri (fun j => if j = k then iprop(True) else peerReaderB γ j k (rds.getD j.val null) []) ∗
      tri (fun j => if j = k then iprop(True) else peerWriterB γ k j (ws.getD j.val null) []) := by
  obtain ⟨hp, hr, hw, ha⟩ := hS
  unfold slots
  iintro ⟨⟨A0, A1, A2⟩, ⟨B0, B1, B2⟩, ⟨C0, C1, C2⟩⟩
  icases slot_gather γ k S 0 $$ [$A0 $B0 $C0] with ⟨%cv0, %rd0, %w0, Hc0, H0⟩
  icases slot_gather γ k S 1 $$ [$A1 $B1 $C1] with ⟨%cv1, %rd1, %w1, Hc1, H1⟩
  icases slot_gather γ k S 2 $$ [$A2 $B2 $C2] with ⟨%cv2, %rd2, %w2, Hc2, H2⟩
  iunfold cellsAt at Hc0 Hc1 Hc2
  icases Hc0 with ⟨P0, R0, W0, L0⟩
  icases Hc1 with ⟨P1, R1, W1, L1⟩
  icases Hc2 with ⟨P2, R2, W2, L2⟩
  iexists [cv0, cv1, cv2], [rd0, rd1, rd2], [w0, w1, w2]
  isplitr
  · ipureintro; exact ⟨rfl, rfl⟩
  isplitl [P0 P1 P2]
  · iapply ownSlice_of_elems _ _ hp
    iapply BigSepL.bigSepL_cons.2; iframe
    iapply BigSepL.bigSepL_cons.2; iframe
    iapply BigSepL.bigSepL_cons.2; iframe
    iapply BigSepL.bigSepL_nil.2; iempintro
  isplitl [R0 R1 R2]
  · iapply ownSlice_of_elems _ _ hr
    iapply BigSepL.bigSepL_cons.2; iframe
    iapply BigSepL.bigSepL_cons.2; iframe
    iapply BigSepL.bigSepL_cons.2; iframe
    iapply BigSepL.bigSepL_nil.2; iempintro
  isplitl [W0 W1 W2]
  · iapply ownSlice_of_elems _ _ hw
    iapply BigSepL.bigSepL_cons.2; iframe
    iapply BigSepL.bigSepL_cons.2; iframe
    iapply BigSepL.bigSepL_cons.2; iframe
    iapply BigSepL.bigSepL_nil.2; iempintro
  isplitl [L0 L1 L2]
  · unfold replica2.aliveList
    iapply ownSlice_of_elems _ _ ha
    iapply BigSepL.bigSepL_cons.2; iframe
    iapply BigSepL.bigSepL_cons.2; iframe
    iapply BigSepL.bigSepL_cons.2; iframe
    iapply BigSepL.bigSepL_nil.2; iempintro
  simp only [tri, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, List.getD_cons_zero,
    List.getD_cons_succ]
  icases ite_sep _ _ _ $$ H0 with ⟨Ra, Wa⟩
  icases ite_sep _ _ _ $$ H1 with ⟨Rb, Wb⟩
  icases ite_sep _ _ _ $$ H2 with ⟨Rc, Wc⟩
  iframe

end

end Perennial.gryff.netN
