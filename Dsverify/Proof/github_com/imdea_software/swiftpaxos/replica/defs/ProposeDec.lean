/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/defs/ProposeDec.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
What `Propose.Unmarshal` reads decodes to the proposal it builds (`sp.decodes`, pure): the
value's two ignored length bytes are 0 on any encoder's stream.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.WireWf

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

namespace sp

/-- The bytes `Value.Unmarshal` accepts: two length bytes, two ignored bytes, the value. -/
def decValue (l0 l1 x y : w8) (v : List w8) : List w8 := [l0, l1, x, y] ++ v

theorem decValue_peel {l0 l1 x y : w8} {v v' rest rest' : List w8}
    (hl : l0.toNat + 256 * l1.toNat = v.length) (hv' : v'.length < 2 ^ 16)
    (h : decValue l0 l1 x y v ++ rest = encValue v' ++ rest') :
    v = v' ∧ decValue l0 l1 x y v = encValue v' ∧ rest = rest' := by
  unfold decValue encValue at *
  simp only [List.cons_append, List.nil_append, List.cons.injEq, List.append_assoc] at h ⊢
  obtain ⟨h0, h1, h2, h3, h⟩ := h
  have e0 := congrArg BitVec.toNat h0
  have e1 := congrArg BitVec.toNat h1
  simp only [W8, BitVec.toNat_ofInt] at e0 e1
  have hlen : v.length = v'.length := by omega
  obtain ⟨rfl, rfl⟩ := List.append_inj h hlen
  exact ⟨rfl, ⟨h0, h1, h2, h3, rfl⟩, rfl⟩

/-- The decoded proposal. -/
theorem propose_decodes (seq cl : w32) (op : w8) (k : w64) (l0 l1 x y : w8) (v : List w8)
    (ts : w64) (hv : v.length < 2 ^ 16) (hl : l0.toNat + 256 * l1.toNat = v.length) :
    decodes (W8 0) (le32 seq ++ le32 cl ++ [op] ++ le64 k ++ decValue l0 l1 x y v ++ le64 ts)
      (.propose seq cl ⟨op, k, v⟩ ts) := by
  refine ⟨rfl, hv, fun m' u w hw hc h => ?_⟩
  cases m' <;> simp only [Msg.code, rpcTable] at hc <;> (try exact absurd hc (by decide))
  rename_i seq' cl' c' ts'
  simp only [Msg.body, encCmd, List.append_assoc] at h ⊢
  obtain ⟨h1, h⟩ := le32_peel h
  obtain ⟨h2, h⟩ := le32_peel h
  obtain ⟨h3, h⟩ := byte_peel h
  obtain ⟨h4, h⟩ := le64_peel h
  obtain ⟨h5, h6, h⟩ := decValue_peel hl hw (by simpa [List.append_assoc] using h)
  obtain ⟨h7, -⟩ := le64_peel h
  subst h1 h2 h3 h4 h5 h7
  refine ⟨by cases c'; rfl, ?_⟩
  rw [← h6]

end sp

end Perennial.github_com.imdea_software.swiftpaxos
