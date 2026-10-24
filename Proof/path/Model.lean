/-
**Go's `path`, as pure functions** (rafthttp stage 5d; the user chose a translation over a trusted
model, 2026-10-22, D38 stage 2). Lean-first.

Each function follows its Go code step by step (`path.go`, `internal/bytealg`'s
`LastIndexByteString`): the specs (`Spec/path/*.lean`) say the code returns the model's value, and
the lemmas below say what the model gives on the strings rafthttp builds: a clean rooted path, a
`/`, and a segment without `/` or `.` (a member id's hexadecimal rendering).

* `lastIndexByte s c`: the last index of `c` in `s`, or `-1`.
* `cleanModel p`: `Clean(p)`, a loop over `p` (`cleanLoop`) whose state is the read index `r`, the
  output `o` (the lazy buffer's first `w` bytes) and `dotdot`; `backW` is the backtracking loop of a
  `..` element, `copyElem` the copy of a real element.
* `splitModel`, `joinModel` (of a list of elements), `baseModel`, `dirModel`.
-/
module

public import Perennial.Proof.ProofPrelude

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace path

/-- Writing `c` at `w` and taking `w + 1`. -/
theorem take_set_succ (L : List w8) (w : Nat) (c : w8) (h : w < L.length) :
    (L.set w c).take (w + 1) = L.take w ++ [c] := by
  rw [List.take_succ, List.take_set, List.set_eq_of_length_le (by simp; omega)]
  simp [h]

/-- `'/'`. -/
abbrev slash : w8 := W8 47
/-- `'.'`. -/
abbrev dot : w8 := W8 46

/-- `LastIndexByteString`'s loop from `i` down: the last index below `i` of `c` in `s`, or `-1`. -/
def lastIdxFrom (s : List w8) (c : w8) : Nat → Int
  | 0 => -1
  | j + 1 => if s.getD j 0 = c then j else lastIdxFrom s c j

/-- `bytealg.LastIndexByteString(s, c)`: the last index of `c` in `s`, or `-1`. -/
def lastIndexByte (s : List w8) (c : w8) : Int := lastIdxFrom s c s.length

theorem lastIdxFrom_bounds (s : List w8) (c : w8) (j : Nat) :
    -1 ≤ lastIdxFrom s c j ∧ lastIdxFrom s c j < j := by
  induction j with
  | zero => simp [lastIdxFrom]
  | succ k ih =>
    unfold lastIdxFrom
    split <;> omega

theorem lastIndexByte_bounds (s : List w8) (c : w8) :
    -1 ≤ lastIndexByte s c ∧ lastIndexByte s c < s.length :=
  lastIdxFrom_bounds s c s.length

/-- The backtracking loop of a `..` element: `for w > dotdot && o[w] != '/' { w-- }`, from `w`. -/
def backW (o : List w8) (dd : Nat) : Nat → Nat
  | 0 => 0
  | w + 1 => if dd < w + 1 ∧ o.getD (w + 1) 0 ≠ slash then backW o dd w else w + 1

/-- The copy of a real element: `for ; r < n && p[r] != '/'; r++ { o.append(p[r]) }`, with fuel
`f` (`copyElem` gives it enough). -/
def copyElemF (p : List w8) : Nat → Nat → List w8 → Nat × List w8
  | 0, r, o => (r, o)
  | f + 1, r, o =>
    if r < p.length ∧ p.getD r 0 ≠ slash then copyElemF p f (r + 1) (o ++ [p.getD r 0]) else (r, o)

/-- The copy of a real element from `r`. -/
def copyElem (p : List w8) (r : Nat) (o : List w8) : Nat × List w8 :=
  copyElemF p (p.length - r) r o

/-- One round of `Clean`'s main loop at `r < len(p)`: the next state. -/
def cleanStep (p : List w8) (rooted : Bool) (r : Nat) (o : List w8) (dd : Nat) :
    Nat × List w8 × Nat :=
  if p.getD r 0 = slash then (r + 1, o, dd)
  else if p.getD r 0 = dot ∧ (r + 1 = p.length ∨ p.getD (r + 1) 0 = slash) then (r + 1, o, dd)
  else if p.getD r 0 = dot ∧ p.getD (r + 1) 0 = dot ∧
      (r + 2 = p.length ∨ p.getD (r + 2) 0 = slash) then
    if dd < o.length then (r + 2, o.take (backW o dd (o.length - 1)), dd)
    else if !rooted then
      (r + 2, (if 0 < o.length then o ++ [slash] else o) ++ [dot, dot],
        ((if 0 < o.length then o ++ [slash] else o) ++ [dot, dot]).length)
    else (r + 2, o, dd)
  else
    let ce := copyElem p r
      (if (rooted ∧ o.length ≠ 1) ∨ (!rooted ∧ o.length ≠ 0) then o ++ [slash] else o)
    (ce.1, ce.2, dd)

/-- `Clean`'s main loop, from the read index `r`, the output `o` and `dotdot` (`dd`), with fuel
`f` (each round reads a byte at least; `cleanLoop` gives it enough). -/
def cleanLoopF (p : List w8) (rooted : Bool) : Nat → Nat → List w8 → Nat → List w8
  | 0, _, o, _ => o
  | f + 1, r, o, dd =>
    if r < p.length then
      let st := cleanStep p rooted r o dd
      cleanLoopF p rooted f st.1 st.2.1 st.2.2
    else o

/-- `Clean`'s main loop from `r`. -/
def cleanLoop (p : List w8) (rooted : Bool) (r : Nat) (o : List w8) (dd : Nat) : List w8 :=
  cleanLoopF p rooted (p.length - r) r o dd

/-! ### Unfolding the loops -/

theorem copyElemF_fst_ge (p : List w8) (f r : Nat) (o : List w8) : r ≤ (copyElemF p f r o).1 := by
  induction f generalizing r o with
  | zero => simp [copyElemF]
  | succ f ih =>
    simp only [copyElemF]
    split
    · have := ih (r + 1) (o ++ [p.getD r 0]); omega
    · simp

/-- One round of the copy loop. -/
theorem copyElem_step (p : List w8) (r : Nat) (o : List w8) (h : r < p.length)
    (hs : p.getD r 0 ≠ slash) : copyElem p r o = copyElem p (r + 1) (o ++ [p.getD r 0]) := by
  unfold copyElem
  obtain ⟨f, hf⟩ : ∃ f, p.length - r = f + 1 := ⟨p.length - r - 1, by omega⟩
  rw [hf, copyElemF, if_pos ⟨h, hs⟩]
  congr 1; omega

/-- The end of the copy loop. -/
theorem copyElem_stop (p : List w8) (r : Nat) (o : List w8)
    (h : ¬ (r < p.length ∧ p.getD r 0 ≠ slash)) : copyElem p r o = (r, o) := by
  unfold copyElem
  cases hf : p.length - r with
  | zero => rfl
  | succ f => rw [copyElemF, if_neg h]

theorem copyElem_fst_gt (p : List w8) (r : Nat) (o : List w8) (h : r < p.length)
    (hs : p.getD r 0 ≠ slash) : r < (copyElem p r o).1 := by
  rw [copyElem_step p r o h hs]
  have := copyElemF_fst_ge p (p.length - (r + 1)) (r + 1) (o ++ [p.getD r 0])
  unfold copyElem; omega

theorem copyElem_fst_le (p : List w8) (r : Nat) (o : List w8) (h : r ≤ p.length) :
    (copyElem p r o).1 ≤ p.length := by
  unfold copyElem
  generalize hf : p.length - r = f
  induction f generalizing r o with
  | zero => simp [copyElemF]; omega
  | succ f ih =>
    simp only [copyElemF]
    split
    · exact ih (r + 1) _ (by omega) (by omega)
    · simp; omega

/-- A round of the main loop reads a byte at least. -/
theorem cleanStep_fst_gt (p : List w8) (rooted : Bool) (r : Nat) (o : List w8) (dd : Nat)
    (h : r < p.length) : r < (cleanStep p rooted r o dd).1 := by
  unfold cleanStep
  split
  · simp
  split
  · simp
  split
  · split
    · simp
    split <;> simp
  · next h1 h2 h3 => exact copyElem_fst_gt p r _ h h1

theorem cleanLoopF_fuel (p : List w8) (rooted : Bool) (f g r : Nat) (o : List w8) (dd : Nat)
    (hf : p.length - r ≤ f) (hg : p.length - r ≤ g) :
    cleanLoopF p rooted f r o dd = cleanLoopF p rooted g r o dd := by
  induction f generalizing g r o dd with
  | zero =>
    cases g with
    | zero => rfl
    | succ g => simp only [cleanLoopF]; rw [if_neg (by omega)]
  | succ f ih =>
    cases g with
    | zero => simp only [cleanLoopF]; rw [if_neg (by omega)]
    | succ g =>
      simp only [cleanLoopF]
      split
      · next h =>
        have := cleanStep_fst_gt p rooted r o dd h
        exact ih g _ _ _ (by omega) (by omega)
      · rfl

/-- One round of the main loop. -/
theorem cleanLoop_step (p : List w8) (rooted : Bool) (r : Nat) (o : List w8) (dd : Nat)
    (h : r < p.length) :
    cleanLoop p rooted r o dd =
      cleanLoop p rooted (cleanStep p rooted r o dd).1 (cleanStep p rooted r o dd).2.1
        (cleanStep p rooted r o dd).2.2 := by
  unfold cleanLoop
  obtain ⟨f, hf⟩ : ∃ f, p.length - r = f + 1 := ⟨p.length - r - 1, by omega⟩
  rw [hf, cleanLoopF, if_pos h]
  have := cleanStep_fst_gt p rooted r o dd h
  exact cleanLoopF_fuel p rooted _ _ _ _ _ (by omega) (by omega)

/-- The end of the main loop. -/
theorem cleanLoop_stop (p : List w8) (rooted : Bool) (r : Nat) (o : List w8) (dd : Nat)
    (h : ¬ r < p.length) : cleanLoop p rooted r o dd = o := by
  unfold cleanLoop
  cases hf : p.length - r with
  | zero => rfl
  | succ f => rw [cleanLoopF, if_neg h]

/-- One round of the backtracking loop. -/
theorem backW_step (o : List w8) (dd k : Nat) (h : dd < k + 1 ∧ o.getD (k + 1) 0 ≠ slash) :
    backW o dd (k + 1) = backW o dd k := by
  rw [backW, if_pos h]

theorem backW_stop (o : List w8) (dd k : Nat) (h : ¬ (dd < k ∧ o.getD k 0 ≠ slash)) :
    backW o dd k = k := by
  cases k with
  | zero => rfl
  | succ k => rw [backW, if_neg h]

theorem backW_bounds (o : List w8) (dd k : Nat) (h : dd ≤ k) :
    dd ≤ backW o dd k ∧ backW o dd k ≤ k := by
  induction k with
  | zero => simp [backW]; omega
  | succ k ih =>
    rw [backW]
    split
    · next h' => have := ih (by omega); omega
    · omega

/-- `Clean(p)`. -/
def cleanModel (p : List w8) : List w8 :=
  if p = [] then go!"." else
  let rooted := decide (p.getD 0 0 = slash)
  let o := cleanLoop p rooted (if rooted then 1 else 0) (if rooted then [slash] else [])
    (if rooted then 1 else 0)
  if o = [] then go!"." else o

/-- `Split(p)`: `p[:i+1]`, `p[i+1:]` for `i` the last index of `/`. -/
def splitModel (p : List w8) : List w8 × List w8 :=
  ((p.take (lastIndexByte p slash + 1).toNat), (p.drop (lastIndexByte p slash + 1).toNat))

/-- `Join(elem...)`'s buffer: the elements from the first non-empty one, joined with `/`. -/
def joinBuf : List (List w8) → List w8 → List w8
  | [], buf => buf
  | e :: es, buf =>
    joinBuf es (if buf.length > 0 ∨ e ≠ [] then (if buf.length > 0 then buf ++ [slash] else buf) ++ e
      else buf)

/-- One element of `Join`'s buffer loop. -/
def joinStep (b e : List w8) : List w8 :=
  if b.length > 0 ∨ e ≠ [] then (if b.length > 0 then b ++ [slash] else b) ++ e else b

theorem joinBuf_eq (es : List (List w8)) (buf : List w8) : joinBuf es buf = es.foldl joinStep buf := by
  induction es generalizing buf with
  | nil => rfl
  | cons e es ih => simp only [joinBuf, List.foldl_cons, ih, joinStep]

theorem joinBuf_take_succ (es : List (List w8)) (n : Nat) (h : n < es.length) :
    joinBuf (es.take (n + 1)) [] = joinStep (joinBuf (es.take n) []) es[n] := by
  rw [joinBuf_eq, joinBuf_eq, List.take_succ, List.foldl_append, List.getElem?_eq_getElem h]
  rfl

/-- `Join(elem...)`. -/
def joinModel (es : List (List w8)) : List w8 :=
  if (es.map List.length).sum = 0 then [] else cleanModel (joinBuf es [])

/-- `p` without its trailing slashes. -/
def stripSlashes (p : List w8) : List w8 :=
  (p.reverse.dropWhile (· = slash)).reverse

theorem stripSlashes_nil : stripSlashes [] = [] := rfl

theorem stripSlashes_snoc_slash (q : List w8) : stripSlashes (q ++ [slash]) = stripSlashes q := by
  simp [stripSlashes, List.reverse_append, List.dropWhile]

theorem stripSlashes_snoc_ne (q : List w8) (x : w8) (h : x ≠ slash) :
    stripSlashes (q ++ [x]) = q ++ [x] := by
  unfold stripSlashes
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append, List.dropWhile_cons]
  split
  · next hx => exact absurd (of_decide_eq_true hx) h
  · simp

/-- `Base(p)`. -/
def baseModel (p : List w8) : List w8 :=
  if p = [] then go!"." else
  let q := stripSlashes p
  let q' := if 0 ≤ lastIndexByte q slash then q.drop (lastIndexByte q slash + 1).toNat else q
  if q' = [] then go!"/" else q'

/-- `Dir(p)`. -/
def dirModel (p : List w8) : List w8 := cleanModel (splitModel p).1

example : cleanModel go!"/raft/stream" = go!"/raft/stream" := by decide
example : cleanModel go!"a//b/./c/../d/" = go!"a/b/d" := by decide
example : cleanModel go!"/../a/.." = go!"/" := by decide
example : cleanModel go!"../../x" = go!"../../x" := by decide
example : joinModel [go!"/raft", go!"stream"] = go!"/raft/stream" := by decide
example : baseModel go!"/raft/stream/msgapp/1f" = go!"1f" := by decide
example : dirModel go!"/raft/stream/msgapp/1f" = go!"/raft/stream/msgapp" := by decide

end path
end EtcdGrove
end Perennial
