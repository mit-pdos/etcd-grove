/-
Proof of `Spec/.../backend/bucketBuffer__CopyUsed.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.bucketBuffer__CopyUsed
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

theorem backend.bucketBuffer.CopyUsed.wp_proof
    (hAssert : verify.Assert.spec (GF := GF) (hG := hG)) :
    backend.bucketBuffer.CopyUsed.spec (GF := GF) (hG := hG) := by
  intro bb dq p es
  wp_start as H
  iunfold bbAt at H
  icases H with ⟨Hbb, Hs, Hcap, #Hro, #Hin⟩
  icases bb_fields_acc _ _ _ $$ Hbb with ⟨Hbuf, Hused, Hbb⟩
  ihave #Hin2 := Hin
  iunfold entsIn at Hin2
  icases Hin2 with ⟨%Hle, -⟩
  ihave %Hl := ownSlice_len _ _ _ $$ Hs
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hs
  have Hlen : sint.Z (W64 (es.length : Int)) = es.length := by have := Hl.1; have := Hl.2; word
  wp_auto
  wp_apply wp_slice_literal
  try (isplitr; (ipureintro; rfl))
  iintro %sl ⟨-, -⟩
  wp_auto
  rw [_root_.decide_eq_true (show sint.Z (W64 (es.length : Int)) ≤ sint.Z p.buf.len by
    have := Hl.1; word)]
  wp_apply hAssert
  wp_apply (wp_slice_make2 (V := kv) (W64 (es.length : Int))) as %nsl ⟨Hn, Hncap⟩
  · ipureintro; word
  have Hb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (W64 (es.length : Int)) ∧
      sint.Z (W64 (es.length : Int)) ≤ sint.Z p.buf.len := by
    have := Hl.1; refine ⟨by decide, by word, by word⟩
  icases (ownSlice_slice (W64 0) (W64 (es.length : Int)) p.buf dq p.kvs Hb).1 $$ Hs
    with ⟨Hs0, Hsm, Hs1⟩
  have Hbc : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (W64 (es.length : Int)) ∧
      sint.Z (W64 (es.length : Int)) ≤ sint.Z p.buf.cap := by
    have := Hl.1; have := Hwf; refine ⟨by decide, by word, by word⟩
  simp only [Hbc]
  wp_apply (wp_slice_copy nsl _ _ _ dq) $$ [Hn Hsm] as %nc ⟨-, Hn, Hsm⟩
  · iframe
  ihave Hs := (ownSlice_slice (W64 0) (W64 (es.length : Int)) p.buf dq p.kvs Hb).2 $$ [Hs0 Hsm Hs1]
  · iframe
  ihave Hbb := Hbb $$ Hbuf Hused
  have Hn0 : sint.nat (W64 0) = 0 := rfl
  have Hnl : sint.nat (W64 (es.length : Int)) = es.length := by have := Hl.1; word
  rw [Hn0, Hnl, subslice_take_drop, List.drop_zero, List.length_replicate,
    List.take_of_length_le (l := List.take es.length p.kvs)
      (by simp only [List.length_take]; exact Nat.min_le_left _ _),
    List.drop_of_length_le (l := List.replicate es.length (zero_val kv)) (by simp; omega),
    List.append_nil]
  ihave #Hro' := slotsRO_take _ es.length $$ Hro
  ihave #Hin' := entsIn_take_kvs _ _ es.length (Nat.le_refl _) $$ Hin
  iapply HΦ
  isplitl [Hbb Hs Hcap]
  · iunfold bbAt
    iframe # ∗
  iexists { buf := nsl, kvs := p.kvs.take es.length }
  iunfold bbAt
  simp only [List.length_take]
  iframe # ∗
  ipureintro; omega

end proof

end EtcdGrove
end Perennial
