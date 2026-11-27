/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/jsoncodec/ScanSteps.lean (lab master 915f964;
namespace `VsrJson` there).
-/
/-
One-step equations of `goL` (the scanner's loop), by its state and next byte.
-/
module

public import Net.Proof.models_lab.jsoncodec.Scan.Def

@[expose] public section

namespace JsonScan

open Perennial

variable (i : Nat) (stk : List w8) (st : Nat) (eOK eof : Bool)

theorem goL_nil : goL [] i stk st eOK eof = (1, i) := by
  rw [goL.eq_def]

theorem goL_space (c : w8) (r : List w8) (hc : spB c = true) :
    goL (c :: r) i stk st eOK eof = goL r (i + 1) stk st eOK eof := by
  rw [goL.eq_def]; simp [hc]

theorem goL_open (c : w8) (r : List w8) (hc : c = 91#8 ∨ c = 123#8)
    (hd : stk.length < maxDepth) :
    goL (c :: r) i stk 0 eOK eof =
      goL r (i + 1) (c :: stk) (if c = 123#8 then 2 else 0) true eof := by
  rw [goL.eq_def]
  have hs : spB c = false := by rcases hc with rfl | rfl <;> decide
  simp [hs, hc, show ¬ maxDepth ≤ stk.length by omega]

theorem goL_scalar (c : w8) (r : List w8) (hs : spB c = false) (hc1 : c ≠ 91#8)
    (hc2 : c ≠ 123#8) (hc3 : c ≠ 93#8) :
    goL (c :: r) i stk 0 eOK eof =
      (let p := scalarL (c :: r) i (eof && stk.isEmpty)
       if p.1 ≠ 0 then p
       else if stk = [] then (0, p.2)
       else goL (r.drop (p.2 - i - 1)) p.2 stk 1 false eof) := by
  rw [goL.eq_def]
  simp only [hs, hc1, hc2, hc3, false_or, false_and, ite_false, Bool.false_eq_true]
  rfl

theorem goL_close0 (r stk' : List w8) :
    goL (93#8 :: r) i (91#8 :: stk') 0 true eof =
      if stk' = [] then (0, i + 1) else goL r (i + 1) stk' 1 false eof := by
  rw [goL.eq_def]; simp [spB]; try rfl

theorem goL_comma (r : List w8) (top : w8) (stk' : List w8) :
    goL (44#8 :: r) i (top :: stk') 1 eOK eof =
      goL r (i + 1) (top :: stk') (if top = 123#8 then 2 else 0) eOK eof := by
  rw [goL.eq_def]; simp [spB]; try rfl

theorem goL_close1 (c : w8) (r : List w8) (top : w8) (stk' : List w8)
    (hc : (c = 93#8 ∧ top = 91#8) ∨ (c = 125#8 ∧ top = 123#8)) :
    goL (c :: r) i (top :: stk') 1 eOK eof =
      if stk' = [] then (0, i + 1) else goL r (i + 1) stk' 1 eOK eof := by
  rw [goL.eq_def]
  have hs : spB c = false := by rcases hc with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  have hc' : c ≠ 44#8 := by rcases hc with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  simp [hs, hc, hc']

theorem goL_close2 (r : List w8) (top : w8) (stk' : List w8) :
    goL (125#8 :: r) i (top :: stk') 2 true eof =
      if stk' = [] then (0, i + 1) else goL r (i + 1) stk' 1 false eof := by
  rw [goL.eq_def]; simp [spB]; try rfl

theorem goL_key (r : List w8) :
    goL (34#8 :: r) i stk 2 eOK eof =
      (let p := strL r (i + 1)
       if p.1 ≠ 0 then p else goL (r.drop (p.2 - i - 1)) p.2 stk 3 false eof) := by
  rw [goL.eq_def]; simp [spB]; try rfl

theorem goL_colon (r : List w8) :
    goL (58#8 :: r) i stk 3 eOK eof = goL r (i + 1) stk 0 eOK eof := by
  rw [goL.eq_def]; simp [spB]; try rfl

end JsonScan
