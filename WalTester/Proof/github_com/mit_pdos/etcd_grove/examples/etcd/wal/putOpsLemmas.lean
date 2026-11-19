/-
`flatMap_take_succ`, `flatMap_take_length` and `w64_of_length`, out of `putOps.lean`'s proof so that the
tester's lemmas import them without the proof (import tiers, 2026-11-18).
-/
module

public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.putOps
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.putHS
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.putU64

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.wal

/-- One more element of a `flatMap` over a prefix. -/
theorem flatMap_take_succ {α β : Type} (l : List α) (f : α → List β) (i : Nat) (x : α)
    (h : l[i]? = some x) : (l.take (i + 1)).flatMap f = (l.take i).flatMap f ++ f x := by
  rw [List.take_add_one, h]; simp

/-- A `flatMap` over the whole list. -/
theorem flatMap_take_length {α β : Type} (l : List α) (f : α → List β) (i : Nat)
    (h : i = l.length) : (l.take i).flatMap f = l.flatMap f := by
  rw [h, List.take_length]

/-- A slice's length as a word. -/
theorem w64_of_length {α : Type} (l : List α) (n : w64) (h : l.length = sint.nat n ∧ 0 ≤ sint.Z n) :
    W64 l.length = n := by
  rw [h.1]; word

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions]

end proof

end etcd_wal
end EtcdGrove
end Perennial
