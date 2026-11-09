/-
Lean-first (no Rocq counterpart).

# Reading a state: the loops over its servers (layer C's invariants, 2026-11-09)

The invariants of `invariants.go` loop over `s.Server` (`for _, i := range s.Server`) and read
`s.S[i]`; the transcription (`Tla/Invariants.lean`) folds `List.all` or `List.allM` (in `EvalM`,
where `Committed` may fail) over `st.server`. The laws here are what those proofs share: a server
of the state read through `stateRO`'s map (`servers_at`), and a loop's invariant "the first `n`
servers passed" stepped (`all_take_step`, `allM_take_step`) and closed (`all_take_end`,
`allM_take_end`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Rep

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

open Iris Iris.BI Iris.ProofMode

/-! ## The loops, purely -/

/-- `allM` past a prefix that passed. -/
theorem allM_ok_append {α : Type} (f : α → EvalM Bool) :
    ∀ (l1 l2 : List α), l1.allM f = .ok true → (l1 ++ l2).allM f = l2.allM f
  | [], _, _ => rfl
  | a :: rest, l2, h => by
    rw [List.allM_cons] at h
    rw [List.cons_append, List.allM_cons]
    cases hfa : f a with
    | error e => simp only [hfa, bind, Except.bind] at h; cases h
    | ok c =>
      simp only [hfa, bind, Except.bind] at h ⊢
      cases c with
      | false => simp only [Bool.false_eq_true, ite_false] at h; cases h
      | true => simp only [ite_true] at h ⊢; exact allM_ok_append f rest l2 h

/-- One step of an `allM` loop: the first `n` elements passed, the whole list evaluates to `b`, so
the `n`-th evaluates (to `c`): `false` decides `b`, `true` passes the first `n + 1`. -/
theorem allM_take_step {α : Type} (f : α → EvalM Bool) (l : List α) (n : Nat) (y : α) (b : Bool)
    (hy : l[n]? = some y) (h1 : (l.take n).allM f = .ok true) (h : l.allM f = .ok b) :
    ∃ c, f y = .ok c ∧ (c = false → b = false) ∧ (c = true → (l.take (n + 1)).allM f = .ok true) := by
  have hn : n < l.length := (List.getElem?_eq_some_iff.1 hy).1
  have hyn : l[n] = y := (List.getElem?_eq_some_iff.1 hy).2
  have hl : l = l.take n ++ y :: l.drop (n + 1) := by
    conv => lhs; rw [← List.take_append_drop n l]
    rw [List.drop_eq_getElem_cons hn, hyn]
  rw [hl, allM_ok_append f _ _ h1, List.allM_cons] at h
  cases hfy : f y with
  | error e => simp only [hfy, bind, Except.bind] at h; cases h
  | ok c =>
    simp only [hfy, bind, Except.bind] at h
    refine ⟨c, rfl, ?_, ?_⟩
    · rintro rfl; simp only [Bool.false_eq_true, ite_false] at h; cases h; rfl
    · rintro rfl
      rw [List.take_add_one, hy, Option.toList_some, allM_ok_append f _ _ h1, List.allM_cons]
      simp only [hfy, bind, Except.bind, ite_true, List.allM_nil]; rfl

/-- The end of an `allM` loop: every element passed, so the whole list evaluates to `true`. -/
theorem allM_take_end {α : Type} (f : α → EvalM Bool) (l : List α) (n : Nat) (b : Bool)
    (hn : l.length ≤ n) (h1 : (l.take n).allM f = .ok true) (h : l.allM f = .ok b) : b = true := by
  rw [List.take_of_length_le hn, h] at h1
  cases h1; rfl

/-- Two evaluations and a result: both evaluated. -/
theorem bind2_ok {α β : Type} (a : EvalM α) (b : EvalM β) (f : α → β → Bool) (c : Bool)
    (h : (do let x ← a; let y ← b; return f x y) = Except.ok (ε := EvalError) c) :
    ∃ x y, a = .ok x ∧ b = .ok y ∧ c = f x y := by
  cases ha : a with
  | error e => rw [ha] at h; cases h
  | ok x =>
    cases hb : b with
    | error e => rw [ha, hb] at h; cases h
    | ok y => rw [ha, hb] at h; cases h; exact ⟨x, y, rfl, rfl, rfl⟩

/-- One step of an `all` loop. -/
theorem all_take_step {α : Type} (f : α → Bool) (l : List α) (n : Nat) (y : α)
    (hy : l[n]? = some y) (h1 : (l.take n).all f = true) :
    (f y = false → l.all f = false) ∧ (f y = true → (l.take (n + 1)).all f = true) := by
  refine ⟨fun hf => ?_, fun hf => ?_⟩
  · rw [List.all_eq_false]; exact ⟨y, List.mem_of_getElem? hy, by simp [hf]⟩
  · rw [List.take_add_one, hy, Option.toList_some, List.all_append, h1]; simp [hf]

/-- The end of an `all` loop. -/
theorem all_take_end {α : Type} (f : α → Bool) (l : List α) (n : Nat)
    (hn : l.length ≤ n) (h1 : (l.take n).all f = true) : l.all f = true := by
  rwa [List.take_of_length_le hn] at h1

/-- The `n`-th id of a set's slice is the set's `n`-th element. -/
theorem set_getElem {xs : List w64} {s : SetIds} (hmap : xs.map (fun x => uint.nat x) = s) {n : Nat}
    {y : w64} (hy : xs[n]? = some y) : s[n]? = some (uint.nat y) := by
  rw [← hmap, List.getElem?_map, hy]; rfl

/-- An id below `2^64`, as a word and back. -/
theorem W64_uint_nat (y : w64) : W64 (Int.ofNat (uint.nat y)) = y := by
  apply BitVec.eq_of_toNat_eq; simp

/-- Go `==` on ids is `=` on the servers they denote. -/
theorem id_eq_iff (x y : w64) : x = y ↔ uint.nat x = uint.nat y :=
  ⟨fun h => h ▸ rfl, fun h => by rw [← W64_uint_nat x, ← W64_uint_nat y, h]⟩

/-- Go `==` on `int`s is `=` on the numbers they denote. -/
theorem int_eq_iff (a b : w64) : a = b ↔ sint.Z a = sint.Z b :=
  ⟨fun h => h ▸ rfl, fun h => BitVec.toInt_inj.1 h⟩

/-- The role constant `Leader`. -/
theorem strRel_leader [GooseExts] : strRel (go!"StateLeader") leader := by
  unfold strRel leader; decide

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

/-- Server `y` of the state, through its map: `stateRO`'s servers at a member. -/
theorem servers_at (st : State) (sm : GMap w64 Loc) (y : w64) (hy : uint.nat y ∈ st.server) :
    ([∗list] i ∈ st.server, ∃ q : Loc, ⌜sm !! (W64 (Int.ofNat i)) = some q⌝ ∗
        serverRO (GF := GF) q (st.s i)) ⊢
      ∃ q : Loc, ⌜sm !! y = some q⌝ ∗ serverRO q (st.s (uint.nat y)) := by
  obtain ⟨k, hk, hki⟩ := List.mem_iff_getElem.1 hy
  iintro #H
  icases (BigSepL.bigSepL_lookup (Φ := fun _ j => iprop(∃ q : Loc, ⌜sm !! (W64 (Int.ofNat j)) = some q⌝ ∗
      serverRO (GF := GF) q (st.s j))) (List.getElem?_eq_some_iff.2 ⟨hk, hki⟩)) $$ H with ⟨%q, %Hq, #Hsv⟩
  rw [W64_uint_nat] at Hq
  iexists q
  iframe Hsv
  ipureintro; exact Hq

end defs

end Etcdraft
end EtcdGrove
end Perennial
