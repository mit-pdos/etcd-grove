/-
Lean-first (no Rocq counterpart): the proof of `stateMachineEventType.String`
(`Spec/go_etcd_io/raft/v3/stateMachineEventType__String.lean`).
-/
module

public import Spec.go_etcd_io.raft.v3.stateMachineEventType__String

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem stateMachineEventType.String.wp_proof :
    stateMachineEventType.String.spec (GF := GF) (hG := hG) := by
  intro e He
  wp_start
  wp_auto
  wp_apply wp_slice_literal (V := GoString) evtNames
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  simp only [go.arrayLiteralSize, List.foldl, Int.reduceAdd]
  rw [show (max (max (19 : Int) 0) 0) = 19 from rfl]
  wp_auto
  have He' : uint.nat e < 19 := He
  obtain ⟨str, Hstr⟩ : ∃ str, evtNames[uint.nat e]? = some str :=
    ⟨_, List.getElem?_eq_getElem He⟩
  rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z e ∧ sint.Z e < sint.Z (W64 19) by
    constructor <;> word))]
  wp_apply wp_load_slice_index _ (sint.Z e) evtNames _ str (by word) $$ [Hsl] as Hsl
  · iframe; ipureintro
    rw [show (sint.Z e).toNat = uint.nat e by word]; exact Hstr
  try wp_auto
  iapply HΦ
  ipureintro; exact Hstr

end proof

end EtcdGrove
end Perennial
