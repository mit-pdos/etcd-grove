/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/N/Handshake.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit N: the peer connections' protocols after the handshake (`ConnectToPeers`)

The dialer `k` of peer `q` (`q < k`) writes `u32Le (k ||| peerMark)` then its stream to `q`;
the bridges `peerWriterB` / `peerReaderB` keep, from the connection's protocols
(`gryffWireP` / `gryffWireQ`, `Proto/Wire.lean`).
-/
module

public import Dsverify.Proof.gryff.N.SpecsDefs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.netN

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto

attribute [local instance] GooseGlobalGS.gooseInvGS

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]


theorem rid3_W32 (k : Fin 3) : rid3 (W32 (k.val : Int)) = k := by
  apply Fin.ext
  simp only [rid3]
  have : (W32 (k.val : Int)).toNat = k.val := by
    have := k.isLt; simp [BitVec.toNat_ofInt]; omega
  rw [this]; exact Nat.mod_eq_of_lt k.isLt

/-- The dialer's handshake. -/
def peerHs (k : Fin 3) : w32 := W32 (k.val : Int) ||| peerMark

theorem W32_lt_peerMark (k : Fin 3) : W32 (k.val : Int) < peerMark := by
  have hk := k.isLt
  unfold peerMark
  rw [BitVec.lt_def]
  simp only [BitVec.toNat_ofInt]
  omega

/-- **The dialer's writer bridge**: after the handshake, any prefix of `k`'s stream to `q` is
allowed on the connection (the peer branch of `dialStream`). -/
theorem dialer_bridge (γ : GryffNames GF) (k q : Fin 3) (a : GoString) (c : Nat) :
    □ peerRole γ a (W32 (k.val : Int)) ∗ □ portId γ a (W32 (q.val : Int)) ⊢
      □ ∀ X, peerStreamOk γ.proto k q X -∗ □ gryffWireP γ a c (u32Le (peerHs k) ++ X) := by
  iintro ⟨#Hrole, #Hport⟩
  imodintro
  iintro %X #Hps
  imodintro
  unfold gryffWireP
  iright
  iexists u32Le (peerHs k) ++ X
  isplitr
  · ipureintro; exact List.prefix_refl _
  imodintro
  unfold dialStream
  iexists peerHs k, X
  isplitr
  · ipureintro; rfl
  ileft
  iexists W32 (k.val : Int), W32 (q.val : Int)
  isplitr
  · ipureintro; exact ⟨rfl, W32_lt_peerMark k⟩
  iframe Hrole Hport
  rw [rid3_W32, rid3_W32]
  iexact Hps

end

end Perennial.gryff.netN
