/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/N/PeerMark.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Two pure laws of the handshake (`peerMark`'s bit, prefixes of equal length), stated here for the
server side (`N/ConnLaws`, `N/ClientConn`) so that it does not import the client's `Client/Stream`
(which has copies, `peerMark_or_ge` and `prefix_same_len`).
-/
module

public import Dsverify.Proof.gryff.Proto.Wire

@[expose] public section

noncomputable section

namespace Perennial.gryff

/-- `peerMark`'s bit is set in a peer's handshake. -/
theorem peerMark_or_ge_n (id : w32) : ¬ (id ||| peerMark) < peerMark := by
  -- bit 31 is set (no `bv_decide`: its native evaluation would add an axiom)
  unfold peerMark
  intro h
  have hb : (id ||| W32 (2 ^ 31)).getLsbD 31 = true := by simp
  have hge : 2 ^ 31 ≤ (id ||| W32 (2 ^ 31)).toNat := Nat.ge_two_pow_of_testBit hb
  rw [BitVec.lt_def] at h
  have : (W32 (2 ^ 31)).toNat = 2 ^ 31 := by decide
  omega

theorem prefix_same_len_n {α : Type _} {a b X : List α} (hl : a.length = b.length)
    (h : a ++ X <+: b ∨ b <+: a ++ X) : a = b := by
  rcases h with h | h
  · exact ((List.prefix_append a X).trans h).eq_of_length hl
  · exact (List.prefix_of_prefix_length_le (List.prefix_append a X) h (by omega)).eq_of_length hl

end Perennial.gryff
