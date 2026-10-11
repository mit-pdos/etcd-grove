/-
Proof of `Spec/schema_unsafeUpdateConsistentIndex.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.unsafeUpdateConsistentIndex
public import Spec.encoding.binary.bigEndian__PutUint64
public import Spec.go_etcd_io.etcd.client.pkg.v3.verify.Verify
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.UnsafeReadConsistentIndex

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

theorem schema.unsafeUpdateConsistentIndex.wp_proof
    (hP : binary.bigEndian.PutUint64.spec (GF := GF) (hG := hG))
    (hV : verify.Verify.spec (GF := GF) (hG := hG))
    (hR : schema.UnsafeReadConsistentIndex.spec (GF := GF) (hG := hG)) :
    schema.unsafeUpdateConsistentIndex.spec (GF := GF) (hG := hG) := by
  intro tx TM m index term allowDecreasing
  wp_start as ⟨#Hw, HTM, %Hmono⟩
  ihave Hsi : (schema.schemaInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hsi with ⟨⟨%mb, #Hmb⟩, ⟨%ck, #Hck, #Hckb⟩, ⟨%tk, #Htk, #Htkb⟩, -⟩
  unfold metaWriter
  icases Hw with ⟨#Hrd, #Hput, #Hputt⟩
  wp_auto
  wp_if_destruct
  · iapply HΦ
    simp only [metaAfterSave, ↓reduceIte]
    iexact HTM
  have hidx : index ≠ W64 0 := Hif
  wp_apply (wp_slice_make2 (V := w8) (t := go.byte)) as %bs1 ⟨Hbs1, -⟩
  · ipureintro; decide
  wp_apply wp_bePutUint64 hP bs1 _ index (by simp) $$ [$Hbs1] as Hbs1
  cases allowDecreasing
  · wp_auto
    ihave #Hvpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.verify $$ []
    · iPkgInit
    wp_apply hV _ _ iprop(index_ptr ↦ index ∗ tx_ptr ↦ GoInterface.ok tx ∗ TM m) $$
      [index tx HTM] as ⟨index, tx, HTM⟩
    · isplitl [index tx HTM]
      · iframe
      iintro ⟨index, tx, HTM⟩
      wp_auto
      wp_apply_core (hR tx ⊤ TM) $$ [] [HTM index tx]
      · iframe Hpkg Hrd
      unfold readCIAU readAU
      imodintro
      iexists m
      iframe HTM
      iintro HTM
      imodintro
      by_cases h0 : m.1 = W64 0
      · simp only [h0, ↓reduceIte]
        wp_auto
        wp_apply (wp_map_make1 (K := GoString) (V := GoInterface) go.string go.any) as %mref Hm
        wp_apply (wp_mapInsert (K := GoString) (V := GoInterface) go.string mref _ _ _) $$ [$Hm] as Hm
        (try wp_auto)
        wp_apply (wp_mapInsert (K := GoString) (V := GoInterface) go.string mref _ _ _) $$ [$Hm] as Hm
        (try wp_auto)
        iexists #mref
        iframe
        ipureintro
        simp
      · simp only [h0, ↓reduceIte]
        imodintro
        iexists m
        iframe HTM
        iintro HTM
        imodintro
        wp_auto
        wp_apply (wp_map_make1 (K := GoString) (V := GoInterface) go.string go.any) as %mref Hm
        wp_apply (wp_mapInsert (K := GoString) (V := GoInterface) go.string mref _ _ _) $$ [$Hm] as Hm
        (try wp_auto)
        wp_apply (wp_mapInsert (K := GoString) (V := GoInterface) go.string mref _ _ _) $$ [$Hm] as Hm
        (try wp_auto)
        iexists #mref
        iframe
        ipureintro
        have := Hmono rfl hidx
        simp [this]
    unfold metaPutSpec
    ihave #Hp := Hput $$ %mb %ck %bs1 %m %index
    wp_bind (App (App (App (Val #(methods tx.ty go!"UnsafePut" tx.v)) (Val #mb)) (Val #ck)) (Val #bs1))
    iapply Hp $$ [Hbs1 HTM]
    · iframe Hmb Hckb Hbs1 HTM
    inext
    iintro HTM
    wp_auto
    wp_if_destruct
    · wp_apply (wp_slice_make2 (V := w8) (t := go.byte)) as %bs2 ⟨Hbs2, -⟩
      · ipureintro; decide
      wp_apply wp_bePutUint64 hP bs2 _ term (by simp) $$ [$Hbs2] as Hbs2
      ihave #Hpt := Hputt $$ %mb %tk %bs2 %(index, m.2) %term
      wp_bind (App (App (App (Val #(methods tx.ty go!"UnsafePut" tx.v)) (Val #mb)) (Val #tk)) (Val #bs2))
      iapply Hpt $$ [Hbs2 HTM]
      · iframe Hmb Htkb Hbs2 HTM
      inext
      iintro HTM
      (try wp_auto)
      iapply HΦ
      have ht : term ≠ W64 0 := by intro h; subst h; simp at Hif
      simp only [metaAfterSave, hidx, ht, ↓reduceIte]
      iexact HTM
    · iapply HΦ
      have ht : term = W64 0 := by word
      simp only [metaAfterSave, hidx, ht, ↓reduceIte]
      iexact HTM
  · wp_auto
    unfold metaPutSpec
    ihave #Hp := Hput $$ %mb %ck %bs1 %m %index
    wp_bind (App (App (App (Val #(methods tx.ty go!"UnsafePut" tx.v)) (Val #mb)) (Val #ck)) (Val #bs1))
    iapply Hp $$ [Hbs1 HTM]
    · iframe Hmb Hckb Hbs1 HTM
    inext
    iintro HTM
    wp_auto
    wp_if_destruct
    · wp_apply (wp_slice_make2 (V := w8) (t := go.byte)) as %bs2 ⟨Hbs2, -⟩
      · ipureintro; decide
      wp_apply wp_bePutUint64 hP bs2 _ term (by simp) $$ [$Hbs2] as Hbs2
      ihave #Hpt := Hputt $$ %mb %tk %bs2 %(index, m.2) %term
      wp_bind (App (App (App (Val #(methods tx.ty go!"UnsafePut" tx.v)) (Val #mb)) (Val #tk)) (Val #bs2))
      iapply Hpt $$ [Hbs2 HTM]
      · iframe Hmb Htkb Hbs2 HTM
      inext
      iintro HTM
      (try wp_auto)
      iapply HΦ
      have ht : term ≠ W64 0 := by intro h; subst h; simp at Hif
      simp only [metaAfterSave, hidx, ht, ↓reduceIte]
      iexact HTM
    · iapply HΦ
      have ht : term = W64 0 := by word
      simp only [metaAfterSave, hidx, ht, ↓reduceIte]
      iexact HTM

end proof

end EtcdGrove
end Perennial
