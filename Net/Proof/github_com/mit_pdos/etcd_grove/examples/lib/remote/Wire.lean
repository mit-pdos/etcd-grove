/-
`examples/lib/remote`'s wire format (`notes/remote-port-plan.md`, §3): a frame is an 8-byte
little-endian length, then the body (`frame`, kvraft's format); a body is at most `maxLen` bytes
(`MaxLen`, 2^20). One connection carries one request frame and at most one reply frame. A reader
that reads a whole frame at the start of a direction whose bytes are a prefix of a frame reads that
frame (`frame_prefix_eq`): no frame is a proper prefix of another.
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Base
public import GooseLang.Ext.Net.Proto

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

namespace github_com.mit_pdos.etcd_grove.examples.lib.remote

/-- `MaxLen`: the longest body a frame may have. -/
abbrev maxLen : Nat := 2 ^ 20

/-- A frame: `body`'s length (8 bytes, little-endian), then `body` (`writeFrame`). -/
def frame (body : List w8) : List w8 := u64Le (W64 body.length) ++ body

theorem frame_length (body : List w8) : (frame body).length = 8 + body.length := by
  simp [frame, u64Le_length]

/-- `W64` is injective below `2 ^ 64`. -/
theorem W64_natCast_inj {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (h : (W64 a : w64) = W64 b) : a = b := by
  have := congrArg BitVec.toNat h
  simp [W64] at this
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

/-- A whole frame that is a prefix of a frame (bodies shorter than `2 ^ 63`) is that frame. -/
theorem frame_prefix_eq {p p' : List w8} (hp : p.length < 2 ^ 63) (hp' : p'.length < 2 ^ 63)
    (h : frame p <+: frame p') : p = p' := by
  obtain ⟨t, ht⟩ := h
  simp only [frame, List.append_assoc] at ht
  obtain ⟨h1, h2⟩ := List.append_inj ht (by simp [u64Le_length])
  have hl : p.length = p'.length :=
    W64_natCast_inj (by omega) (by omega) (u64Le_inj h1)
  have h3 := congrArg List.length h2
  simp only [List.length_append] at h3
  have hn : t = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst hn
  simpa using h2

/-- A frame's header decodes to its body's length. -/
theorem frame_hdr (body : List w8) :
    leToU64 (u64Le (W64 body.length)) = W64 body.length := u64Le_to_word _

end github_com.mit_pdos.etcd_grove.examples.lib.remote
end Perennial
