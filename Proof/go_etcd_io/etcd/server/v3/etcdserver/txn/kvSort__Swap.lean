/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.kvSort__Swap

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.server.v3.etcdserver.txn
  go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

theorem txn.kvSort.Swap.wp_proof : txn.kvSort.Swap.spec (GF := GF) (hG := hG) := by
  intro ks sl ps i j a b
  wp_start as ⟨#Hf, Hs, %Hij⟩
  wp_auto
  obtain ⟨hi0, hj0, ha, hb⟩ := Hij
  ihave %Hl := ownSlice_len _ _ _ $$ Hs
  have hilt : sint.nat i < ps.length := (List.getElem?_eq_some_iff.1 ha).1
  have hjlt : sint.nat j < ps.length := (List.getElem?_eq_some_iff.1 hb).1
  have Hbi : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sl.len := by
    have := Hl.1; refine ⟨hi0, ?_⟩; word
  have Hbj : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len := by
    have := Hl.1; refine ⟨hj0, ?_⟩; word
  simp only [Hbi, Hbj, _root_.and_self, ite_true]
  wp_apply wp_load_slice_index sl (sint.Z i) ps (DFrac.own 1) a hi0 $$ [Hs] as Hs
  · iframe; ipureintro; exact ha
  simp only [Hbj, _root_.and_self, ite_true]
  wp_apply wp_load_slice_index sl (sint.Z j) ps (DFrac.own 1) b hj0 $$ [Hs] as Hs
  · iframe; ipureintro; exact hb
  simp only [Hbi, _root_.and_self, ite_true]
  wp_apply wp_store_slice_index sl (sint.Z i) ps b $$ [Hs] as Hs
  · iframe; ipureintro; exact ⟨hi0, by have := Hl.1; word⟩
  simp only [Hbj, _root_.and_self, ite_true]
  wp_apply wp_store_slice_index sl (sint.Z j) _ a $$ [Hs] as Hs
  · iframe; ipureintro; exact ⟨hj0, by simp only [List.length_set]; have := Hl.1; word⟩
  iapply HΦ
  iexact Hs

end proof


end EtcdGrove
end Perennial
