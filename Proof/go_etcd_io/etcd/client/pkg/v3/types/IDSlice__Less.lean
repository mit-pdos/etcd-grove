/-
The proof of `types.IDSlice.Less` (`id.go`; claim #34, stage 2, 2026-11-25), the sort of
`membership.RaftCluster.MemberIDs`. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.client.pkg.v3.types.IDSlice__Less

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.pkg.v3.types.Assumptions]

theorem types.IDSlice.Less.wp_proof :
    types.IDSlice.Less.spec (GF := GF) (hG := hG) := by
  intro sl ids dq i j a b hi0 hj0 ha hb
  wp_start as Hs
  wp_auto
  ihave %Hl := ownSlice_len _ _ _ $$ Hs
  have hilt : sint.nat i < ids.length := (List.getElem?_eq_some_iff.1 ha).1
  have hjlt : sint.nat j < ids.length := (List.getElem?_eq_some_iff.1 hb).1
  have Hbi : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sl.len := by have := Hl.1; refine ⟨hi0, ?_⟩; word
  have Hbj : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len := by have := Hl.1; refine ⟨hj0, ?_⟩; word
  try simp only [Hbi, _root_.and_self, ite_true]
  (try wp_auto)
  try simp only [Hbi, _root_.and_self, ite_true]
  wp_apply wp_load_slice_index sl (sint.Z i) ids dq a hi0 $$ [Hs] as Hs
  · iframe; ipureintro; exact ha
  (try wp_auto)
  try simp only [Hbj, _root_.and_self, ite_true]
  wp_apply wp_load_slice_index sl (sint.Z j) ids dq b hj0 $$ [Hs] as Hs
  · iframe; ipureintro; exact hb
  (try wp_auto)
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
