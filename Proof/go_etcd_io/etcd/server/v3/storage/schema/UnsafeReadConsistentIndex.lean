/-
Proof of `Spec/schema_UnsafeReadConsistentIndex.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.UnsafeReadConsistentIndex
public import Spec.encoding.binary.bigEndian__Uint64

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.cindex
  go_etcd_io.etcd.server.v3.storage

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

theorem schema.UnsafeReadConsistentIndex.wp_proof
    (hU : binary.bigEndian.Uint64.spec (GF := GF) (hG := hG)) :
    schema.UnsafeReadConsistentIndex.spec (GF := GF) (hG := hG) := by
  intro r E View
  wp_start as #Hrd
  ihave Hsi : (schema.schemaInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hsi with ⟨⟨%mb, #Hmb⟩, ⟨%ck, #Hck, #Hckb⟩, ⟨%tk, #Htk, #Htkb⟩⟩
  unfold metaReader
  icases Hrd with ⟨#Hri, #Hrt⟩
  unfold metaRangeSpec
  wp_auto
  wp_bind (App (App (App (App (Val #(methods r.ty go!"UnsafeRange" r.v)) (Val #mb)) (Val #ck))
    (Val #(slice.nil))) (Val #(W64 0)))
  iapply Hri $$ %mb %ck %_ Hmb Hckb
  unfold readCIAU
  iapply readAU_wand $$ HΦ
  iintro %m Hm %ks %vs #Hvs
  wp_auto
  unfold metaVals
  by_cases h0 : m.1 = W64 0
  · simp only [h0, ↓reduceIte]
    ihave %Hlen := ownSlice_len _ _ _ $$ Hvs
    have hl : vs.len = W64 0 := by simp only [List.length_nil] at Hlen; word
    wp_if_destruct
    · iexact Hm
    · exact absurd hl Hif
  · simp only [h0, ↓reduceIte]
    icases Hvs with ⟨%s, #Hvs, #Hs⟩
    ihave %Hlen := ownSlice_len _ _ _ $$ Hvs
    have hl : vs.len = W64 1 := by simp only [List.length_singleton] at Hlen; word
    wp_if_destruct
    · simp [hl] at Hif
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by rw [hl]; decide))]
    wp_apply wp_load_slice_index vs (sint.Z (W64 0)) [s] DFrac.discard s (by decide) $$ [Hvs] as _
    · iframe Hvs; ipureintro; rfl
    wp_apply wp_beUint64 hU s m.fst DFrac.discard $$ [$Hs] as _
    wp_bind (App (App (App (App (Val #(methods r.ty go!"UnsafeRange" r.v)) (Val #mb)) (Val #tk))
      (Val #(slice.nil))) (Val #(W64 0)))
    iapply Hrt $$ %mb %tk %_ Hmb Htkb
    iapply readAU_wand $$ Hm
    iintro %m' Hm' %ks' %ts Hts
    wp_auto
    by_cases h1 : m'.2 = W64 0
    · simp only [h1, ↓reduceIte]
      ihave %Hlen' := ownSlice_len _ _ _ $$ Hts
      have hl' : ts.len = W64 0 := by simp only [List.length_nil] at Hlen'; word
      wp_if_destruct
      · rw [← h1]; iexact Hm'
      · exact absurd hl' Hif
    · simp only [h1, ↓reduceIte]
      icases Hts with ⟨%s', #Hts, #Hs'⟩
      ihave %Hlen' := ownSlice_len _ _ _ $$ Hts
      have hl' : ts.len = W64 1 := by simp only [List.length_singleton] at Hlen'; word
      wp_if_destruct
      · simp [hl'] at Hif
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by rw [hl']; decide))]
      wp_apply wp_load_slice_index ts (sint.Z (W64 0)) [s'] DFrac.discard s' (by decide) $$ [Hts] as _
      · iframe Hts; ipureintro; rfl
      wp_apply wp_beUint64 hU s' m'.snd DFrac.discard $$ [$Hs'] as _
      iexact Hm'

end proof

end EtcdGrove
end Perennial
