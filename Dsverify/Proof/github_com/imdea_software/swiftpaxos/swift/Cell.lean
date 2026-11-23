/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/Cell.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
A **one-shot cell** (internal to the swift group): a resource `S` that a filler deposits once,
after the cell was created, and a claimer takes once, after it learned (a persistent witness)
that the cell was filled. Used for a goroutine spawned before the resources it will need exist:
`New` spawns the reply goroutine before it writes `ballot`; the goroutine claims its reading
right when it handles its first message, which carries the witness.

* `swift.isCell N γ S` (persistent): the cell's invariant;
* `swift.cellFillTok γ`, `swift.cellClaimTok γ`: the filler's and the claimer's tokens;
* `swift.cellFilled γ` (persistent): the cell was filled.

Laws: `cell_alloc`, `cell_fill`, `cell_claim`.
-/
module

public import Perennial.Ghost.MonoNat
public import Perennial.Ghost.Token
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.Defs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

/-- The cell's ghost names. -/
structure swift.CellNames where
  m : GName
  f : GName
  k : GName

section cell
variable {GF : BundledGFunctors} [AllG GF] [InvGS GF]

/-- The cell's state: `0` empty, `1` filled (with `S`), `2` claimed. -/
def swift.cellInv (γ : swift.CellNames) (S : IProp GF) : IProp GF :=
  iprop(∃ s : Nat, monoNatAuthOwn γ.m 1 s ∗
    (⌜s = 0⌝ ∨ (⌜s = 1⌝ ∗ token γ.f ∗ S) ∨ (⌜s = 2⌝ ∗ token γ.f ∗ token γ.k)))

/-- The cell (persistent). -/
def swift.isCell (N : Namespace) (γ : swift.CellNames) (S : IProp GF) : IProp GF :=
  inv N (swift.cellInv γ S)

instance swift.isCell_persistent (N : Namespace) (γ : swift.CellNames) (S : IProp GF) :
    Persistent (swift.isCell N γ S) := by unfold swift.isCell; infer_instance

/-- The filler's token. -/
def swift.cellFillTok (γ : swift.CellNames) : IProp GF := token γ.f
/-- The claimer's token. -/
def swift.cellClaimTok (γ : swift.CellNames) : IProp GF := token γ.k
/-- The cell was filled (persistent). -/
def swift.cellFilled (γ : swift.CellNames) : IProp GF := monoNatLbOwn γ.m 1

instance swift.cellFilled_persistent (γ : swift.CellNames) :
    Persistent (swift.cellFilled (GF := GF) γ) := by unfold swift.cellFilled; infer_instance

theorem swift.cell_alloc (N : Namespace) (E : CoPset) (S : IProp GF) :
    ⊢ |={E}=> ∃ γ : swift.CellNames, swift.isCell N γ S ∗ swift.cellFillTok γ ∗
      swift.cellClaimTok γ := by
  imod mono_nat_own_alloc (GF := GF) 0 with ⟨%γm, Hm, -⟩
  imod token_alloc (GF := GF) with ⟨%γf, Hf⟩
  imod token_alloc (GF := GF) with ⟨%γk, Hk⟩
  imod inv_alloc N E (swift.cellInv ⟨γm, γf, γk⟩ S) $$ [Hm] with #Hinv
  · inext
    unfold swift.cellInv
    iexists 0
    iframe Hm
    ileft
    ipureintro; rfl
  imodintro
  iexists ⟨γm, γf, γk⟩
  unfold swift.isCell swift.cellFillTok swift.cellClaimTok
  iframe Hinv Hf Hk

theorem swift.cell_fill (N : Namespace) (E : CoPset) (hE : ↑N ⊆ E) (γ : swift.CellNames)
    (S : IProp GF) :
    swift.isCell N γ S ∗ swift.cellFillTok γ ∗ S ⊢ |={E}=> swift.cellFilled γ := by
  iintro ⟨#Hinv, Hf, HS⟩
  unfold swift.isCell swift.cellFillTok swift.cellFilled
  iinv Hinv with Hi Hclose
  unfold swift.cellInv
  icases Hi with ⟨%s, >Hm, Hs⟩
  icases Hs with (>%Hs | ⟨>%Hs, >Hf2, -⟩ | ⟨>%Hs, >Hf2, -⟩)
  · subst Hs
    imod mono_nat_own_update (GF := GF) (γ := γ.m) 1 (Nat.zero_le 1) $$ Hm with ⟨Hm, #Hlb⟩
    imod Hclose $$ [Hm Hf HS] with -
    · inext
      iexists 1
      iframe Hm
      iright; ileft
      iframe Hf HS
      ipureintro; rfl
    imodintro
    iexact Hlb
  · icombine Hf Hf2 gives %Hc; exact Hc.elim
  · icombine Hf Hf2 gives %Hc; exact Hc.elim

theorem swift.cell_claim (N : Namespace) (E : CoPset) (hE : ↑N ⊆ E) (γ : swift.CellNames)
    (S : IProp GF) :
    swift.isCell N γ S ∗ swift.cellClaimTok γ ∗ swift.cellFilled γ ⊢ |={E}=> ▷ S := by
  iintro ⟨#Hinv, Hk, #Hlb⟩
  unfold swift.isCell swift.cellClaimTok swift.cellFilled
  iinv Hinv with Hi Hclose
  unfold swift.cellInv
  icases Hi with ⟨%s, >Hm, Hs⟩
  ihave %Hle := monoNatLbOwn_valid γ.m 1 s 1 $$ Hm Hlb
  icases Hs with (>%Hs | ⟨>%Hs, >Hf, HS⟩ | ⟨>%Hs, -, >Hk2⟩)
  · omega
  · subst Hs
    imod mono_nat_own_update (GF := GF) (γ := γ.m) 2 (by omega) $$ Hm with ⟨Hm, -⟩
    imod Hclose $$ [Hm Hf Hk] with -
    · inext
      iexists 2
      iframe Hm
      iright; iright
      iframe Hf Hk
      ipureintro; rfl
    imodintro
    iexact HS
  · icombine Hk Hk2 gives %Hc; exact Hc.elim

end cell

end Perennial.github_com.imdea_software.swiftpaxos
