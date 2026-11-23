/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/tcp/Frames.lean`, run `rabia-r1wake-1`.)

Pure lemmas on streams of frames: what a reader reads of a well-formed stream (every payload
below `2^32`) is the stream's elements in order.
-/
module

public import Dsverify.Proof.rabia.internal.tcp.Enc

@[expose] public section

namespace Perennial.rabia.model

theorem frames_cons (a : List w8) (A : List (List w8)) : frames (a :: A) = frame a ++ frames A := by
  simp [frames]

theorem frames_nil : frames ([] : List (List w8)) = [] := rfl

theorem frames_append (A B : List (List w8)) : frames (A ++ B) = frames A ++ frames B := by
  simp [frames]

theorem frame_ne_nil (a : List w8) : frame a ≠ [] := by simp [frame]

/-- A reader that has read the frames `A` and then `b` of a well-formed stream `frames L` has read
`L`'s first elements. -/
theorem frames_decomp {A L : List (List w8)} {b X : List w8}
    (hA : ∀ a ∈ A, a.length < 2 ^ 32) (hL : ∀ l ∈ L, l.length < 2 ^ 32) (hb : b.length < 2 ^ 32)
    (h : frames A ++ frame b ++ X <+: frames L) : A ++ [b] <+: L := by
  induction A generalizing L with
  | nil =>
    cases L with
    | nil =>
      simp only [frames_nil, List.nil_append] at h
      have := h.length_le
      simp [frame_length] at this
    | cons l L =>
      simp only [frames_nil, List.nil_append, frames_cons] at h
      have hp : frame b <+: frame l ++ frames L := (List.prefix_append _ _).trans h
      have := frame_prefix_inj hb (hL l (by simp)) hp
      subst this
      simp
  | cons a A ih =>
    cases L with
    | nil =>
      simp only [frames_cons, frames_nil] at h
      have := h.length_le
      simp [frame_length] at this
    | cons l L =>
      simp only [frames_cons, List.append_assoc] at h
      have hp : frame a <+: frame l ++ frames L := (List.prefix_append _ _).trans h
      have hal := frame_prefix_inj (hA a (by simp)) (hL l (by simp)) hp
      subst hal
      have h' : frames A ++ frame b ++ X <+: frames L := by
        rw [List.append_assoc]
        exact (List.prefix_append_right_inj (frame a)).1 h
      have := ih (fun x hx => hA x (by simp [hx])) (fun x hx => hL x (by simp [hx])) h'
      simpa using this

/-- The same after a fixed prefix (a handshake). -/
theorem frames_decomp_pre {pre : List w8} {A L : List (List w8)} {b X : List w8}
    (hA : ∀ a ∈ A, a.length < 2 ^ 32) (hL : ∀ l ∈ L, l.length < 2 ^ 32) (hb : b.length < 2 ^ 32)
    (h : pre ++ frames A ++ frame b ++ X <+: pre ++ frames L) : A ++ [b] <+: L := by
  apply frames_decomp hA hL hb
  simp only [List.append_assoc] at h ⊢
  exact (List.prefix_append_right_inj pre).1 h

/-- The element of `L` after a prefix `A ++ [b]`. -/
theorem prefix_snoc_getElem {α : Type} {A L : List α} {b : α} (h : A ++ [b] <+: L) :
    L[A.length]? = some b := by
  obtain ⟨t, rfl⟩ := h
  simp

theorem map_prefix_of_inj {α β : Type} {f : α → β} (hf : ∀ a b, f a = f b → a = b) :
    ∀ {l1 l2 : List α}, l1.map f <+: l2.map f → l1 <+: l2
  | [], _, _ => List.nil_prefix
  | a :: l1, [], h => by simp at h
  | a :: l1, b :: l2, h => by
    simp only [List.map_cons, List.cons_prefix_cons] at h
    obtain ⟨h1, h2⟩ := h
    rw [hf a b h1]
    exact List.cons_prefix_cons.2 ⟨rfl, map_prefix_of_inj hf h2⟩

theorem prefix_squeeze {α : Type} {W a b : List α} (h1 : W <+: a) (h2 : a ++ b <+: W) :
    a = W ∧ b = [] := by
  have l1 := h1.length_le
  have l2 := h2.length_le
  simp only [List.length_append] at l2
  have hb : b = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst hb
  simp only [List.append_nil] at h2
  exact ⟨(h2.eq_of_length (by omega)), rfl⟩

end Perennial.rabia.model
