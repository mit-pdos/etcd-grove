/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.filterRangeResults
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.pruneKVs

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

theorem txn.filterRangeResults.wp_proof (hPrune : txn.pruneKVs.spec (GF := GF) (hG := hG)) :
    txn.filterRangeResults.spec (GF := GF) (hG := hG) := by
  intro rr r o rev count vs
  wp_start as ⟨Hres, #Hr⟩
  ihave #Hr2 := Hr
  iunfold txn.rangeRequestIs at Hr2
  icases Hr2 with ⟨%Hnn, %ksl, %esl, %k, %e, %rv, %limit, %order, %target, %ser, %ko, %co, %minM, %maxM, %minC, %maxC, #Hk, #Hks, #He, #Hes, #Hlim, #Hrev, #Hord, #Htgt, #Hser, #Hko, #Hco, #HminM, #HmaxM, #HminC, #HmaxC, %Ho⟩
  wp_auto
  ipersist r
  wp_join iprop(rr_ptr ↦ rr ∗ txn.rangeResultIs rr rev count (vs.filter (fun v => decide (maxM = W64 0) || decide (sint.Z v.modRev ≤ sint.Z maxM)))) with [Hres rr] as ⟨rr, Hres⟩
  · rw [show List.filter (fun v => true || decide (sint.Z v.modRev ≤ sint.Z (W64 0))) vs = vs by simp]
    iframe
  · wp_apply (hPrune rr rev count vs _ (fun v => decide (sint.Z maxM < sint.Z v.modRev))) $$ [$Hres] as Hres
    · imodintro
      iintro %p %v
      wp_start as Hkv
      simp only [txn.kvAt, mvcc.kvPtrIs, ↓reduceIte]
      icases Hkv with ⟨%ks1, %st1, %uf1, %sc1, #Hk1, %vs1, #Hv1, Hp1⟩
      wp_auto
      iapply HΦ; iexists ks1, st1, uf1, sc1; iframe Hk1; iexists vs1; iframe Hv1; iexact Hp1
    isplitr
    · ipureintro; rfl
    iframe rr
    iExactEq Hres
    congr 1
    apply List.filter_congr
    intro v _
    by_cases h : sint.Z maxM < sint.Z v.modRev <;> simp [h] <;> omega
  wp_join iprop(rr_ptr ↦ rr ∗ txn.rangeResultIs rr rev count ((vs.filter (fun v => decide (maxM = W64 0) || decide (sint.Z v.modRev ≤ sint.Z maxM))).filter (fun v => decide (minM = W64 0) || decide (sint.Z minM ≤ sint.Z v.modRev)))) with [Hres rr] as ⟨rr, Hres⟩
  · iframe rr; iExactEq Hres; simp
  · wp_apply (hPrune rr rev count (vs.filter (fun v => decide (maxM = W64 0) || decide (sint.Z v.modRev ≤ sint.Z maxM))) _ (fun v => decide (sint.Z v.modRev < sint.Z minM))) $$ [$Hres] as Hres
    · imodintro
      iintro %p %v
      wp_start as Hkv
      simp only [txn.kvAt, mvcc.kvPtrIs, ↓reduceIte]
      icases Hkv with ⟨%ks1, %st1, %uf1, %sc1, #Hk1, %vs1, #Hv1, Hp1⟩
      wp_auto
      iapply HΦ; iexists ks1, st1, uf1, sc1; iframe Hk1; iexists vs1; iframe Hv1; iexact Hp1
    isplitr
    · ipureintro; rfl
    iframe rr
    iExactEq Hres
    congr 1
    apply List.filter_congr
    intro v _
    by_cases h : sint.Z v.modRev < sint.Z minM <;> simp [h] <;> omega
  wp_join iprop(rr_ptr ↦ rr ∗ txn.rangeResultIs rr rev count (((vs.filter (fun v => decide (maxM = W64 0) || decide (sint.Z v.modRev ≤ sint.Z maxM))).filter (fun v => decide (minM = W64 0) || decide (sint.Z minM ≤ sint.Z v.modRev))).filter (fun v => decide (maxC = W64 0) || decide (sint.Z v.createRev ≤ sint.Z maxC)))) with [Hres rr] as ⟨rr, Hres⟩
  · iframe rr; iExactEq Hres; simp
  · wp_apply (hPrune rr rev count ((vs.filter (fun v => decide (maxM = W64 0) || decide (sint.Z v.modRev ≤ sint.Z maxM))).filter (fun v => decide (minM = W64 0) || decide (sint.Z minM ≤ sint.Z v.modRev))) _ (fun v => decide (sint.Z maxC < sint.Z v.createRev))) $$ [$Hres] as Hres
    · imodintro
      iintro %p %v
      wp_start as Hkv
      simp only [txn.kvAt, mvcc.kvPtrIs, ↓reduceIte]
      icases Hkv with ⟨%ks1, %st1, %uf1, %sc1, #Hk1, %vs1, #Hv1, Hp1⟩
      wp_auto
      iapply HΦ; iexists ks1, st1, uf1, sc1; iframe Hk1; iexists vs1; iframe Hv1; iexact Hp1
    isplitr
    · ipureintro; rfl
    iframe rr
    iExactEq Hres
    congr 1
    apply List.filter_congr
    intro v _
    by_cases h : sint.Z maxC < sint.Z v.createRev <;> simp [h] <;> omega
  wp_join iprop(rr_ptr ↦ rr ∗ txn.rangeResultIs rr rev count ((((vs.filter (fun v => decide (maxM = W64 0) || decide (sint.Z v.modRev ≤ sint.Z maxM))).filter (fun v => decide (minM = W64 0) || decide (sint.Z minM ≤ sint.Z v.modRev))).filter (fun v => decide (maxC = W64 0) || decide (sint.Z v.createRev ≤ sint.Z maxC))).filter (fun v => decide (minC = W64 0) || decide (sint.Z minC ≤ sint.Z v.createRev)))) with [Hres rr] as ⟨rr, Hres⟩
  · iframe rr; iExactEq Hres; simp
  · wp_apply (hPrune rr rev count (((vs.filter (fun v => decide (maxM = W64 0) || decide (sint.Z v.modRev ≤ sint.Z maxM))).filter (fun v => decide (minM = W64 0) || decide (sint.Z minM ≤ sint.Z v.modRev))).filter (fun v => decide (maxC = W64 0) || decide (sint.Z v.createRev ≤ sint.Z maxC))) _ (fun v => decide (sint.Z v.createRev < sint.Z minC))) $$ [$Hres] as Hres
    · imodintro
      iintro %p %v
      wp_start as Hkv
      simp only [txn.kvAt, mvcc.kvPtrIs, ↓reduceIte]
      icases Hkv with ⟨%ks1, %st1, %uf1, %sc1, #Hk1, %vs1, #Hv1, Hp1⟩
      wp_auto
      iapply HΦ; iexists ks1, st1, uf1, sc1; iframe Hk1; iexists vs1; iframe Hv1; iexact Hp1
    isplitr
    · ipureintro; rfl
    iframe rr
    iExactEq Hres
    congr 1
    apply List.filter_congr
    intro v _
    by_cases h : sint.Z v.createRev < sint.Z minC <;> simp [h] <;> omega
  iapply HΦ
  iExactEq Hres
  congr 1
  subst Ho
  simp only [List.filter_filter]
  apply List.filter_congr
  intro v _
  simp only [kvFilterOk, txn.rangeOpOf]
  simp only [Bool.and_comm, Bool.and_left_comm]
  congr 1 <;> congr 1 <;> congr 1

end proof

end EtcdGrove
end Perennial
