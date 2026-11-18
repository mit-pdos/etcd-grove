/-
The pure lemmas of `entData.lean`'s proof (`tEntSalt`, `tEntPat`, `tEntData_eq`, ...), in a module of
their own so that the lemmas of `toRaft` import them without the proof (import tiers, 2026-11-18).
-/
module

public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.entData

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.wal

section pure
variable [GooseExts]

/-- The salt's `k`-th byte. -/
def tEntSalt (e : TEnt) (k : Nat) : w8 := W8 (uint.Z (e.salt' >>> W64 (8 * (k : Int))))

/-- The pattern's byte at position `k`. -/
def tEntPat (e : TEnt) (k : Nat) : w8 :=
  W8 (uint.Z ((e.index' + W64 3 * e.term' + W64 (k : Int)) % W64 251))

theorem tEntData_eq (e : TEnt) :
    tEntData e = (List.range (min 8 (uint.nat e.size'))).map (tEntSalt e) ++
      (List.range' 8 (uint.nat e.size' - 8)).map (tEntPat e) := rfl

theorem range_map_succ (f : Nat → w8) (k : Nat) :
    (List.range (k + 1)).map f = (List.range k).map f ++ [f k] := by
  rw [List.range_succ, List.map_append]; rfl

theorem range'_map_succ (f : Nat → w8) (m : Nat) :
    (List.range' 8 (m + 1)).map f = (List.range' 8 m).map f ++ [f (8 + m)] := by
  rw [List.range'_concat, List.map_append]; simp

end pure
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
