/-
**Paths that fit** (`PathFits`, `Premises.lean`): the window property of a directory (`WinOk`: every
256-byte infix holds a `/`) and the facts that build it up, a component at a time, so that a client
proves `PathFits` of `d/b` from a bound on `d` and `b` (`pathFits_child`), and of a literal prefix by
its length (`winOk_short`). `DirFits d`: `d`'s window property, with room for a 255-byte component
and more below it (`d.length < 3800`). Untrusted.
-/
module

public import GooseLang.Ext.Fs.Premises
public import GooseLang.Ext.Fs.TreeLemmas

@[expose] public section

namespace Perennial
namespace Fs

/-- Every 256-byte infix of `p` holds a `/` (`PathFits`' second conjunct). -/
def WinOk (p : GoString) : Prop := ∀ q : GoString, q <:+: p → q.length = 256 → slashB ∈ q

/-- **A directory that fits with room below it**: its windows hold a `/`, and it is shorter than
3800 bytes (room for a `/` and a 255-byte name, with some to spare for a deeper path). -/
def DirFits (d : GoString) : Prop := d.length < 3800 ∧ WinOk d

/-- A string shorter than 256 bytes has no 256-byte infix. -/
theorem winOk_short {p : GoString} (h : p.length < 256) : WinOk p := by
  intro q hq hl
  have := hq.length_le
  omega

/-- A `/`-free prefix of `a ++ / :: b` is a prefix of `a`. -/
theorem prefix_noSlash {q a b : GoString} (h : q <+: a ++ slashB :: b) (hq : slashB ∉ q) :
    q <+: a := by
  induction a generalizing q with
  | nil =>
    rcases List.prefix_cons_iff.1 h with rfl | ⟨t, rfl, -⟩
    · exact List.nil_prefix
    · exact absurd (List.mem_cons_self ..) hq
  | cons x a ih =>
    rcases List.prefix_cons_iff.1 h with rfl | ⟨t, rfl, ht⟩
    · exact List.nil_prefix
    · exact List.cons_prefix_cons.2 ⟨rfl, ih ht (fun hm => hq (List.mem_cons_of_mem _ hm))⟩

/-- A `/`-free infix of `a ++ / :: b` is an infix of `a` or of `b`. -/
theorem infix_noSlash {q a b : GoString} (h : q <:+: a ++ slashB :: b) (hq : slashB ∉ q) :
    q <:+: a ∨ q <:+: b := by
  induction a with
  | nil =>
    rcases List.infix_cons_iff.1 h with hp | hi
    · rcases List.prefix_cons_iff.1 hp with rfl | ⟨t, rfl, -⟩
      · exact .inl List.nil_infix
      · exact absurd (List.mem_cons_self ..) hq
    · exact .inr hi
  | cons x a ih =>
    rcases List.infix_cons_iff.1 h with hp | hi
    · exact .inl (prefix_noSlash (a := x :: a) hp hq).isInfix
    · rcases ih hi with h1 | h1
      · exact .inl (h1.trans (List.suffix_cons _ _).isInfix)
      · exact .inr h1

/-- **A component below a directory keeps the window property** when it is at most 255 bytes. -/
theorem winOk_child {a b : GoString} (ha : WinOk a) (hb : b.length ≤ 255) :
    WinOk (child a b) := by
  intro q hq hl
  refine Classical.byContradiction fun hs => ?_
  rcases infix_noSlash hq hs with h | h
  · exact hs (ha q h hl)
  · have := h.length_le; omega

/-- **`d/b` fits** when `d`'s windows hold a `/`, `b` is at most 255 bytes, and the whole is under
4096 bytes. -/
theorem pathFits_child {d b : GoString} (hd : WinOk d) (hb : b.length ≤ 255)
    (hl : d.length + b.length < 4095) : PathFits (child d b) :=
  ⟨by simp [child]; omega, winOk_child hd hb⟩

/-- `d/b` of a directory that fits (`DirFits`) and a name of at most 255 bytes fits. -/
theorem pathFits_of_dirFits {d b : GoString} (hd : DirFits d) (hb : b.length ≤ 255) :
    PathFits (child d b) :=
  pathFits_child hd.2 hb (by have := hd.1; omega)

end Fs
end Perennial
