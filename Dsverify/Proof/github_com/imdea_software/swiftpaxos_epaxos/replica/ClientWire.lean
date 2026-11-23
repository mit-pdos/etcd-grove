/-
Pure facts of a client connection's bytes (package-internal, for `clientListener`): a `Propose`
read whole from a client's stream is the one the client sent.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.Wire

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

theorem encPropose_prefix_eq (a b a' b' : w32) (c c' : WCmd) (t t' : w64)
    (hc : c.val.length < 2 ^ 16) (hc' : c'.val.length < 2 ^ 16)
    (h : encPropose a b c t <+: encPropose a' b' c' t') :
    a = a' ∧ b = b' ∧ c = c' ∧ t = t' := by
  obtain ⟨X, hX⟩ := h
  unfold encPropose encCommand encValue at hX
  simp only [List.append_assoc, List.cons_append, List.nil_append] at hX
  obtain ⟨ha, hX⟩ := List.append_inj hX (by simp [u32Le_length])
  obtain ⟨hb, hX⟩ := List.append_inj hX (by simp [u32Le_length])
  simp only [List.cons.injEq] at hX
  obtain ⟨hop, hX⟩ := hX
  obtain ⟨hk, hX⟩ := List.append_inj hX (by simp [u64Le_length])
  obtain ⟨hl, hX⟩ := List.append_inj hX (by simp [u32Le_length])
  have hl' := u32Le_inj hl
  have hlen : c.val.length = c'.val.length := by
    have h1 : (W32 (c.val.length % 2 ^ 16 : Nat)).toNat = (W32 (c'.val.length % 2 ^ 16 : Nat)).toNat := by
      rw [hl']
    rw [Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hc'] at h1
    have e1 : (W32 (c.val.length : Nat)).toNat = c.val.length := by word
    have e2 : (W32 (c'.val.length : Nat)).toNat = c'.val.length := by word
    omega
  obtain ⟨hv, hX⟩ := List.append_inj hX hlen
  have ht : u64Le t = u64Le t' := by
    have h1 := congrArg List.length hX
    simp only [List.length_append, u64Le_length] at h1
    have hX0 : X = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hX0
    simpa using hX
  refine ⟨u32Le_inj ha, u32Le_inj hb, ?_, u64Le_inj ht⟩
  have hk' := u64Le_inj hk
  cases c; cases c'
  simp_all

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
