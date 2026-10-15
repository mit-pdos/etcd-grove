/-
Proof of `Spec/.../backend/bucketBuffer__Less.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.bucketBuffer__Less
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

theorem backend.bucketBuffer.Less.wp_proof : backend.bucketBuffer.Less.spec (GF := GF) (hG := hG) := by
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
  simp only [Hbi, _root_.and_self, ite_true]
  list_elem p.kvs (sint.nat i) as xi
  icases ownSlice_elem_acc (sint.Z i) xi p.buf _ p.kvs hi Hxi_lookup $$ Hs with ⟨Hel, Hback⟩
  wp_auto
  ihave Hs := Hback $$ Hel
  rw [list_set_lookup_self _ _ _ Hxi_lookup]
  have Hbj : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z p.buf.len := by
    have := Hl.1; have := Hok.1; refine ⟨hj, ?_⟩; word
  simp only [Hbj, _root_.and_self, ite_true]
  list_elem p.kvs (sint.nat j) as xj
  icases ownSlice_elem_acc (sint.Z j) xj p.buf _ p.kvs hj Hxj_lookup $$ Hs with ⟨Hel, Hback⟩
  wp_auto
  ihave Hs := Hback $$ Hel
  rw [list_set_lookup_self _ _ _ Hxj_lookup]
  ihave ⟨#Hka, -⟩ := entsIn_lookup _ _ _ _ _ Hxi_lookup ha $$ Hin
  ihave ⟨#Hkb, -⟩ := entsIn_lookup _ _ _ _ _ Hxj_lookup hb $$ Hin
  wp_apply (bytes.wp_Compare _ _ DFrac.discard DFrac.discard a.1 b.1) $$ [$Hka $Hkb] as ⟨-, -⟩
  rw [compareResult_neg]
  iapply HΦ
  iunfold ownBB
  iexists p
  iunfold bbAt
  iframe # ∗
  ipureintro; exact Hok

end proof

end EtcdGrove
end Perennial
