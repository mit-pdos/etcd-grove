/-
The proofs of `examples/crashlog` (one generation): the crash invariant of the file `dir/log`
and the specs of `Boot` and its helpers.
-/
module

public import GeneratedProof.github_com.mit_pdos.etcd_grove.examples.crashlog
public import Spec.os.Crash
public import Spec.os.File__ReadAt
public import Spec.os.File__Stat
public import Spec.os.fileStat__Size
public import Spec.os.File__Fd
public import Spec.os.File__Close

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace crashlog

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.crashlog

/-- The data the flag guards (`newData`). -/
def dataC : List w8 := [W8 0xde, W8 0xad, W8 0xbe, W8 0xef, W8 0x01, W8 0x23, W8 0x45, W8 0x67]

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.crashlog.Assumptions]

theorem wp_dataOk (sl : GoSlice) (dq : DFrac) (vs : List w8) (h : vs.take 8 = dataC) :
    {{ (sl ↦*{dq} vs : IProp GF) }}
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.crashlog.dataOk)) (Val #sl))
    {{ RET #true; sl ↦*{dq} vs }} := by
  wp_start as Hs
  icases ownSlice_len sl dq vs $$ Hs with %Hlen
  have hl : 8 ≤ vs.length := by
    have := congrArg List.length h; simp [dataC] at this; omega
  have hv : ∀ i : Nat, i < 8 → vs[i]? = dataC[i]? := by
    intro i hi
    rw [← h, List.getElem?_take_of_lt hi]
  have hs8' : (8 : Int) ≤ sint.Z sl.len := by
    have h1 := Hlen.1; simp only [sint.nat, sint.Z] at h1 ⊢; omega
  have hs8 : sint.Z (W64 8) ≤ sint.Z sl.len := by
    rw [show sint.Z (W64 8) = 8 from rfl]; exact hs8'
  try wp_auto
  rw [decide_eq_true hs8]
  try wp_auto
  rw [if_pos (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z sl.len by
    rw [show sint.Z (W64 0) = 0 from rfl]; omega)]
  wp_apply wp_load_slice_index sl (sint.Z (W64 0)) vs dq (W8 0xde) (by decide) $$ [Hs] as Hs
  · iframe; ipureintro; rw [show (sint.Z (W64 0)).toNat = 0 from rfl]; exact hv 0 (by decide)
  try wp_auto
  rw [if_pos (show 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) < sint.Z sl.len by
    rw [show sint.Z (W64 1) = 1 from rfl]; omega)]
  wp_apply wp_load_slice_index sl (sint.Z (W64 1)) vs dq (W8 0xad) (by decide) $$ [Hs] as Hs
  · iframe; ipureintro; rw [show (sint.Z (W64 1)).toNat = 1 from rfl]; exact hv 1 (by decide)
  try wp_auto
  rw [if_pos (show 0 ≤ sint.Z (W64 2) ∧ sint.Z (W64 2) < sint.Z sl.len by
    rw [show sint.Z (W64 2) = 2 from rfl]; omega)]
  wp_apply wp_load_slice_index sl (sint.Z (W64 2)) vs dq (W8 0xbe) (by decide) $$ [Hs] as Hs
  · iframe; ipureintro; rw [show (sint.Z (W64 2)).toNat = 2 from rfl]; exact hv 2 (by decide)
  try wp_auto
  rw [if_pos (show 0 ≤ sint.Z (W64 3) ∧ sint.Z (W64 3) < sint.Z sl.len by
    rw [show sint.Z (W64 3) = 3 from rfl]; omega)]
  wp_apply wp_load_slice_index sl (sint.Z (W64 3)) vs dq (W8 0xef) (by decide) $$ [Hs] as Hs
  · iframe; ipureintro; rw [show (sint.Z (W64 3)).toNat = 3 from rfl]; exact hv 3 (by decide)
  try wp_auto
  rw [if_pos (show 0 ≤ sint.Z (W64 4) ∧ sint.Z (W64 4) < sint.Z sl.len by
    rw [show sint.Z (W64 4) = 4 from rfl]; omega)]
  wp_apply wp_load_slice_index sl (sint.Z (W64 4)) vs dq (W8 0x01) (by decide) $$ [Hs] as Hs
  · iframe; ipureintro; rw [show (sint.Z (W64 4)).toNat = 4 from rfl]; exact hv 4 (by decide)
  try wp_auto
  rw [if_pos (show 0 ≤ sint.Z (W64 5) ∧ sint.Z (W64 5) < sint.Z sl.len by
    rw [show sint.Z (W64 5) = 5 from rfl]; omega)]
  wp_apply wp_load_slice_index sl (sint.Z (W64 5)) vs dq (W8 0x23) (by decide) $$ [Hs] as Hs
  · iframe; ipureintro; rw [show (sint.Z (W64 5)).toNat = 5 from rfl]; exact hv 5 (by decide)
  try wp_auto
  rw [if_pos (show 0 ≤ sint.Z (W64 6) ∧ sint.Z (W64 6) < sint.Z sl.len by
    rw [show sint.Z (W64 6) = 6 from rfl]; omega)]
  wp_apply wp_load_slice_index sl (sint.Z (W64 6)) vs dq (W8 0x45) (by decide) $$ [Hs] as Hs
  · iframe; ipureintro; rw [show (sint.Z (W64 6)).toNat = 6 from rfl]; exact hv 6 (by decide)
  try wp_auto
  rw [if_pos (show 0 ≤ sint.Z (W64 7) ∧ sint.Z (W64 7) < sint.Z sl.len by
    rw [show sint.Z (W64 7) = 7 from rfl]; omega)]
  wp_apply wp_load_slice_index sl (sint.Z (W64 7)) vs dq (W8 0x67) (by decide) $$ [Hs] as Hs
  · iframe; ipureintro; rw [show (sint.Z (W64 7)).toNat = 7 from rfl]; exact hv 7 (by decide)
  try wp_auto
  iapply HΦ
  iframe

end proof

end crashlog
end EtcdGrove
end Perennial
