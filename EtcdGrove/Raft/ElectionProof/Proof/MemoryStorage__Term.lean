/-
Port of election_proof/proof_MemoryStorage__Term.v.
-/
import EtcdGrove.Raft.ElectionProof.Spec.MemoryStorage__Term

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem MemoryStorage.Term.wp_proof :
    MemoryStorage.Term.spec (GF := GF) (hG := hG) := by
  intro ms prev ents ss i0
  wp_start as ⟨Hms, %Hrange⟩
  iunfold ownMemoryStorage at Hms
  icases Hms with ⟨%γ, Hms⟩
  iNamed Hms
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
  iunfold memstorageInv at Hinv
  icases Hinv with ⟨%prev0, %ents0, %ss0, Hinv⟩
  iNamedSuffix Hinv "_inv"
  iunfold memstorageFields at Hfields_inv
  icases Hfields_inv with ⟨%hs, %snap, %es, %dummy, %cs, %voters, Hfields_inv⟩
  iNamed Hfields_inv
  icombine Hgs Hgs_inv gives % ⟨_, Heq⟩
  simp only [Prod.mk.injEq] at Heq
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := Heq
  wp_auto
  icases Hents with #Hents
  ihave %Hlen := ownSlice_len $$ Hents
  icases ownSlice_elem_acc 0 dummy es _ (dummy :: ents) (by omega) rfl $$ Hents with ⟨#He, -⟩
  obtain ⟨Hlen1, Hlen2⟩ := Hlen
  simp only [List.length_cons] at Hlen1
  have H0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z es.len := by
    constructor <;> word
  simp only [H0, and_self, ↓reduceIte]
  word_lit_simp
  -- Lean: field loads through a struct points-to at a fraction other than `1` are
  -- not found by `wp_load` (see `pbEntryID`); split the entry into its fields
  iStructNamedSuffix He "_0"
  wp_auto
  obtain ⟨Hd0, Hd1⟩ := Hdummy
  wp_if_destruct
  · exfalso; rw [Hd0] at Hif; word
  wp_if_destruct
  · exfalso; rw [Hd0] at Hif; word
  have Hn : sint.Z (i0 - dummy.Index') = uint.Z i0 - uint.Z prev.index' := by
    rw [Hd0]; word
  rw [Hn]
  have Hlt : (uint.Z i0 - uint.Z prev.index').toNat < (dummy :: ents).length := by
    simp only [List.length_cons]; omega
  obtain ⟨e, He⟩ : ∃ e, (dummy :: ents)[(uint.Z i0 - uint.Z prev.index').toNat]? = some e :=
    ⟨_, List.getElem?_eq_getElem Hlt⟩
  icases ownSlice_elem_acc (uint.Z i0 - uint.Z prev.index') e es _ (dummy :: ents)
    (by omega) He $$ Hents with ⟨#He1, -⟩
  have H1 : 0 ≤ uint.Z i0 - uint.Z prev.index' ∧
      uint.Z i0 - uint.Z prev.index' < sint.Z es.len := by
    constructor <;> word
  simp only [H1, and_self, ↓reduceIte]
  iStructNamedSuffix He1 "_1"
  wp_auto
  have Hterm : termAt prev ents i0 = some e.Term' := by
    unfold termAt
    by_cases Hi : uint.Z i0 = uint.Z prev.index'
    · simp only [Hi, ↓reduceIte]
      have H0 : (uint.Z i0 - uint.Z prev.index').toNat = 0 := by omega
      rw [H0] at He
      simp only [List.getElem?_cons_zero, Option.some.injEq] at He
      subst He
      rw [Hd1]
    · simp only [Hi, ↓reduceIte]
      have HS : (uint.Z i0 - uint.Z prev.index').toNat =
          (uint.Z i0 - uint.Z prev.index' - 1).toNat + 1 := by omega
      rw [HS] at He
      simp only [List.getElem?_cons_succ] at He
      rw [He]
      rfl
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hgs_inv HhardState Hsnapshot Hvoters Hents_f HcallStats]
  · inext
    unfold memstorageInv memstorageFields
    iexists prev, ents, ss
    iframe Hgs_inv
    iexists hs, snap, es, dummy, _, voters
    iframe # ∗
    ipureintro; exact ⟨Hsnap_id, Hd0, Hd1⟩
  iapply HΦ
  isplitr
  · ipureintro; exact Hterm
  unfold ownMemoryStorage
  iexists γ
  iframe # ∗
  ipureintro; exact ⟨Hbounded, Hss⟩

end proof

end EtcdGrove
end Perennial
