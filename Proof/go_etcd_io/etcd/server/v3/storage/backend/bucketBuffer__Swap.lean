/-
Proof of `Spec/.../backend/bucketBuffer__Swap.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.bucketBuffer__Swap
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.RangeLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend backend

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

theorem backend.bucketBuffer.Swap.wp_proof : backend.bucketBuffer.Swap.spec (GF := GF) (hG := hG) := by
  intro bb es i j a b hi hj ha hb
  wp_start as H
  iunfold ownBB at H
  icases H with ⟨%p, H, %Hok⟩
  iunfold bbAt at H
  icases H with ⟨Hbb, Hs, Hcap, #Hro, #Hin⟩
  wp_auto
  ihave %Hl := ownSlice_len _ _ _ $$ Hs
  have hilt : sint.nat i < es.length := (List.getElem?_eq_some_iff.1 ha).1
  have hjlt : sint.nat j < es.length := (List.getElem?_eq_some_iff.1 hb).1
  have Hbi : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z p.buf.len := by
    have := Hl.1; have := Hok.1; refine ⟨hi, ?_⟩; word
  have Hbj : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z p.buf.len := by
    have := Hl.1; have := Hok.1; refine ⟨hj, ?_⟩; word
  list_elem p.kvs (sint.nat i) as xi
  list_elem p.kvs (sint.nat j) as xj
  try simp only [Hbj, _root_.and_self, ite_true]
  wp_apply wp_load_slice_index p.buf (sint.Z j) p.kvs (DFrac.own 1) xj hj $$ [Hs] as Hs
  · iframe; ipureintro; exact Hxj_lookup
  try simp only [Hbi, _root_.and_self, ite_true]
  wp_apply wp_load_slice_index p.buf (sint.Z i) p.kvs (DFrac.own 1) xi hi $$ [Hs] as Hs
  · iframe; ipureintro; exact Hxi_lookup
  try simp only [Hbi, _root_.and_self, ite_true]
  wp_apply wp_store_slice_index p.buf (sint.Z i) p.kvs xj $$ [Hs] as Hs
  · iframe; ipureintro; exact ⟨hi, by have := Hl.1; word⟩
  try simp only [Hbj, _root_.and_self, ite_true]
  wp_apply wp_store_slice_index p.buf (sint.Z j) _ xi $$ [Hs] as Hs
  · iframe; ipureintro; exact ⟨hj, by simp only [List.length_set]; have := Hl.1; word⟩
  ihave #Hro' := slotsRO_swap _ _ _ _ _ Hxi_lookup Hxj_lookup $$ Hro
  ihave #Hin' := entsIn_swap _ _ _ _ _ _ _ _ Hxi_lookup Hxj_lookup ha hb $$ Hin
  iapply HΦ
  iunfold ownBB
  iexists { buf := p.buf, kvs := (p.kvs.set (sint.nat i) xj).set (sint.nat j) xi }
  iunfold bbAt
  simp only [List.length_set]
  iframe # ∗
  ipureintro
  unfold bbOk at Hok ⊢
  simp only [List.length_set]
  exact Hok

end proof

end EtcdGrove
end Perennial
