/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/N/ConnDefs.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit N1: the peer slots `ConnectToPeers` and `waitForPeerConnections` fill

`slotOwn γ k S j b`: the `j`-th elements of the generic replica's `Peers`, `PeerReaders`,
`PeerWriters`, `Alive` slices (`S`), with, once filled (`b`), the connection with peer `j`'s reader
and writer (`peerReaderB`, `peerWriterB`) and `Alive[j] = true` (unfilled: `Alive[j] = false`, N1-3). `slots γ k S P cs`: the slots
`j` with `P j`, filled as `cs` says. The dialer owns the slots below `k`, the acceptor those
above.
-/
module

public import Dsverify.Proof.gryff.N.SpecsDefs
public import Dsverify.Proof.gryff.N.SliceElems

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.netN

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto

attribute [local instance] GooseGlobalGS.gooseInvGS

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]


/-- The four peer slices. -/
structure PeerSlices where
  pS : GoSlice
  rS : GoSlice
  wS : GoSlice
  aS : GoSlice

/-- The `j`-th elements of the four slices. -/
def cellsAt (S : PeerSlices) (j : Nat) (cv : GoInterface) (rd w : Loc) (al : Bool) : IProp GF :=
  iprop(sliceIndexRef GoInterface (j : Int) S.pS ↦ cv ∗ sliceIndexRef Loc (j : Int) S.rS ↦ rd ∗
    sliceIndexRef Loc (j : Int) S.wS ↦ w ∗ sliceIndexRef Bool (j : Int) S.aS ↦ al)

/-- Slot `j` of replica `k`, filled (`b`) with the connection with peer `j`. -/
def slotOwn (γ : GryffNames GF) (k : Fin 3) (S : PeerSlices) (j : Fin 3) (b : Bool) : IProp GF :=
  iprop(∃ (cv : GoInterface) (rd w : Loc) (al : Bool), cellsAt S j.val cv rd w al ∗
    if b then ⌜al = true⌝ ∗ peerReaderB γ j k rd [] ∗ peerWriterB γ k j w [] else ⌜al = false⌝)

/-- The slots `j` with `P j`, filled as `cs` says. -/
def slots (γ : GryffNames GF) (k : Fin 3) (S : PeerSlices) (P : Fin 3 → Bool)
    (cs : Fin 3 → Bool) : IProp GF :=
  iprop((if P 0 then slotOwn γ k S 0 (cs 0) else True) ∗
    (if P 1 then slotOwn γ k S 1 (cs 1) else True) ∗
    (if P 2 then slotOwn γ k S 2 (cs 2) else True))

/-- `cs` with slot `q` set to `b`. -/
def upd (cs : Fin 3 → Bool) (q : Fin 3) (b : Bool) : Fin 3 → Bool :=
  fun j => if j = q then b else cs j

/-- Access to slot `q`. -/
theorem slots_acc (γ : GryffNames GF) (k : Fin 3) (S : PeerSlices) (P : Fin 3 → Bool)
    (cs : Fin 3 → Bool) (q : Fin 3) (hq : P q = true) :
    slots γ k S P cs ⊢ slotOwn γ k S q (cs q) ∗
      ∀ b, slotOwn γ k S q b -∗ slots γ k S P (upd cs q b) := by
  unfold slots upd
  iintro ⟨H0, H1, H2⟩
  obtain ⟨q, hq3⟩ := q
  rcases q with _ | _ | _ | q
  · simp only [Fin.zero_eta, Fin.isValue] at hq ⊢
    simp only [hq, ↓reduceIte]
    iframe H0
    iintro %b Hb
    simp (config := {decide := true}) only [↓reduceIte, Fin.isValue]
    iframe
  · rw [show (⟨_, hq3⟩ : Fin 3) = 1 from Fin.ext rfl] at hq ⊢
    simp only [hq, ↓reduceIte]
    iframe H1
    iintro %b Hb
    simp (config := {decide := true}) only [↓reduceIte, Fin.isValue]
    iframe
  · rw [show (⟨_, hq3⟩ : Fin 3) = 2 from Fin.ext rfl] at hq ⊢
    simp only [hq, ↓reduceIte]
    iframe H2
    iintro %b Hb
    simp (config := {decide := true}) only [↓reduceIte, Fin.isValue]
    iframe
  · omega

end

end Perennial.gryff.netN
