/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/bucketBuffer__add.lean`.
Lean-first (no Rocq counterpart).

The entry goes into the free slot `used` (`entsIn_set_snoc`); when that fills the slice, a new
one of `3/2` its length gets the slots, the rest zero (`nil` slices: `slotsRO_append_zero`). The growth leaves a free slot because a writable buffer
has at least two slots (`bbOk`): `3 * 1 / 2 = 1` would not.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.bucketBuffer__add
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.MergeLemmas

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

theorem backend.bucketBuffer.add.wp_proof : backend.bucketBuffer.add.spec (GF := GF) (hG := hG) := by
  intro bb es k v kb vb Hbound
  wp_start as ⟨Hbb, #Hk, #Hv⟩
  iunfold ownBB at Hbb
  icases Hbb with ⟨%p, Hbb, %Hok⟩
  iunfold bbAt at Hbb
  icases Hbb with ⟨Hbb, Hbuf, Hcap, #Hro, #Hents⟩
  ihave %Hl := ownSlice_len _ _ _ $$ Hbuf
  have hB : es.length < 2 ^ 60 := Hbound
  have hnL : es.length < p.kvs.length := Hok.1
  have hLb : p.kvs.length ≤ 2 ^ 61 := Hok.2.2
  have hL2 : 2 ≤ p.kvs.length := Hok.2.1
  have hbn : 0 ≤ sint.Z (W64 (es.length : Int)) ∧ sint.Z (W64 (es.length : Int)) < sint.Z p.buf.len := by
    have h1 := Hl.1
    clear Hok Hbound
    constructor <;> word
  have hnn : sint.nat (W64 (es.length : Int)) = es.length := by word
  wp_auto
  simp only [hbn, _root_.and_self, ite_true]
  list_elem p.kvs es.length as x0
  icases ownSlice_elem_acc (sint.Z (W64 (es.length : Int))) x0 p.buf _ p.kvs hbn.1
    (by rw [show (sint.Z (W64 (es.length : Int))).toNat = es.length from hnn]; exact Hx0_lookup)
    $$ Hbuf with ⟨Hel, Hback⟩
  wp_auto
  simp only [hbn, _root_.and_self, ite_true]
  wp_auto
  ihave Hbuf := Hback $$ %({ key' := k, val' := v } : kv) Hel
  rw [show (sint.Z (W64 (es.length : Int))).toNat = es.length from hnn]
  obtain ⟨ks1, hks1⟩ : ∃ ks1, ks1 = p.kvs.set es.length ({ key' := k, val' := v } : kv) := ⟨_, rfl⟩
  rw [← hks1]
  have hks1l : ks1.length = p.kvs.length := by rw [hks1, List.length_set]
  ihave #Hro1 : slotsRO ks1 $$ []
  · rw [hks1]
    iapply slotsRO_set
    iframe Hro
    iexists kb, vb
    iframe Hk Hv
  ihave #Hents1 : entsIn ks1 (es ++ [(kb, vb)]) $$ []
  · rw [hks1]
    have := entsIn_set_snoc (GF := GF) p.kvs es es.length ({ key' := k, val' := v } : kv) (kb, vb)
      (Nat.le_refl _) hnL
    rw [List.take_length] at this
    iapply this
    iframe Hents Hk Hv
  iclear Hro Hents
  have hused : W64 (es.length : Int) + W64 1 = W64 ((es ++ [(kb, vb)]).length : Int) := by
    rw [List.length_append, List.length_singleton]
    clear Hok Hbound hks1
    word
  rw [hused]
  wp_if_destruct
  · -- the buffer is full: grown to `3/2` of its length
    have hLn : p.kvs.length = es.length + 1 := by
      have h1 := Hl.1
      rw [List.length_append, List.length_singleton] at Hif
      clear Hok Hbound hks1 hused Hx0_lookup
      word
    obtain ⟨M, hM⟩ : ∃ M : w64, M = BitVec.sdiv (W64 3 * p.buf.len) (W64 2) := ⟨_, rfl⟩
    rw [← hM]
    have hMZ : sint.Z M = ((3 * p.kvs.length / 2 : Nat) : Int) := by
      have h1 := Hl.1; have h2 := Hl.2
      rw [hM]
      clear Hok Hbound hks1 hused Hx0_lookup hM Hif
      word
    have hMn : sint.nat M = 3 * p.kvs.length / 2 := by
      show (sint.Z M).toNat = _; rw [hMZ]; omega
    wp_apply (wp_slice_make2 (V := kv) M) $$ [] as %nb ⟨Hnb, Hnbcap⟩
    · ipureintro; rw [hMZ]; omega
    wp_apply (wp_slice_copy nb _ p.buf ks1 (DFrac.own 1)) $$ [Hnb Hbuf] as %n0 ⟨-, Hnb, -⟩
    · iframe
    have hnew : ks1.take (List.replicate (sint.nat M) (zero_val kv)).length ++
        (List.replicate (sint.nat M) (zero_val kv)).drop ks1.length =
        ks1 ++ List.replicate (sint.nat M - ks1.length) (zero_val kv) := by
      rw [List.length_replicate, List.take_of_length_le (by rw [hMn, hks1l]; omega),
        List.drop_replicate]
    rw [hnew]
    wp_auto
    iapply HΦ
    iunfold ownBB
    iexists { buf := nb, kvs := ks1 ++ List.replicate (sint.nat M - ks1.length) (zero_val kv) }
    iunfold bbAt
    ihave #Hro2 := slotsRO_append_zero ks1 (sint.nat M - ks1.length) $$ Hro1
    ihave #Hents2 := entsIn_append_slots ks1 (List.replicate (sint.nat M - ks1.length) (zero_val kv))
      (es ++ [(kb, vb)]) $$ Hents1
    iframe
    iframe Hro2 Hents2
    ipureintro
    unfold bbOk
    simp only [List.length_append, List.length_replicate, List.length_singleton]
    rw [hMn, hks1l]
    omega
  · iapply HΦ
    iunfold ownBB
    iexists { buf := p.buf, kvs := ks1 }
    iunfold bbAt
    iframe
    iframe Hro1 Hents1
    ipureintro
    unfold bbOk
    simp only [List.length_append, List.length_singleton]
    rw [hks1l]
    refine ⟨?_, by omega, hLb⟩
    have h1 := Hl.1
    rw [List.length_append, List.length_singleton] at Hif
    clear Hok Hbound hks1 hused Hx0_lookup
    word

end proof

end EtcdGrove
end Perennial
