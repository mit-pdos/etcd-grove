/-
Pure decoding facts used by the wire package's decoders (internal).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.Binary16
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.PeerWire
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.Wire

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

theorem prefix_eq_of_len {α} (d x y : List α) (hp : d <+: x ++ y) (hl : d.length = x.length) :
    d = x := by
  obtain ⟨t, ht⟩ := hp
  exact (append_prefix_of_length_eq hl (by rw [ht])).1

theorem prefix_skip {α} (d h t rest : List α) (hl : d.length = h.length)
    (hp : d ++ t <+: h ++ rest) : t <+: rest := by
  obtain ⟨u, hu⟩ := hp
  rw [List.append_assoc] at hu
  exact ⟨u, (append_prefix_of_length_eq hl hu).2⟩

/-- The 4-byte length header of an encoded value. -/
theorem value_hdr (d1 : List w8) (hl : d1.length = 4) (v ext : List w8) (hv : v.length < 2^16)
    (hp : d1 <+: encValue v ++ ext) :
    d1 = u32Le (W32 (v.length % 2^16 : Nat)) ∧
      ∃ a b, d1 = [a, b, W8 0, W8 0] ∧ uint.Z a + 256 * uint.Z b = v.length := by
  have h4 : d1 = u32Le (W32 (v.length % 2^16 : Nat)) := by
    unfold encValue at hp
    rw [List.append_assoc] at hp
    exact prefix_eq_of_len _ _ _ hp (by rw [hl, u32Le_length])
  refine ⟨h4, ?_⟩
  have hw : (W32 (v.length % 2^16 : Nat)) = W32 (uint.Z (W16 (v.length : Int))) := by
    congr 1
  rw [hw, ← encoding.binary.u16Le_u32Le] at h4
  refine ⟨_, _, h4, ?_⟩
  simp [uint.Z, W16, W8, Int.shiftRight_eq_div_pow]
  omega

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
