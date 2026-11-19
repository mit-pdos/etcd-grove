/-
`schema.Schema.FindNamedType`:
not proved yet (`sorry`): Draft of the `schema` package's per-function specs (notes/smd-plan.md,
"The call DAG"); proved in the stage's Prove step, after the freeze.

Lean-first (2026-11-19).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.schema.Schema__FindNamedType
public import Perennial.Spec.sync.Once__Do
public import Perennial.Proof.sync
public import Proof.sigs_k8s_io.structured_merge_diff.v7.schema.LawProofs

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : schema.Assumptions]

theorem schema.Schema.FindNamedType.wp_proof
    (h_sync_Once_Do : _root_.Perennial.sync.Once.Do.spec (GF := GF)) :
    schema.Schema.FindNamedType.spec (GF := GF) := by
  intro sc S n
  wp_start as ⟨#HS, %Hnd⟩
  icases LawProofs.isSchema_open sc S $$ HS with ⟨%tys, %tds, #Ht, #Hs, #Hlk, #Ho⟩
  wp_auto
  ipersist s
  wp_func_lits
  wp_apply h_sync_Once_Do
  · isplitr
    · iexact Ho
    iintro !> %Φ2 HP HΦ2
    wp_auto
    wp_apply wp_map_make2 (V := schema.TypeDef) as %mm Hmm
    ihave %Hlen := ownSlice_len $$ Hs
    ihave IH : iprop(∃ (k : w64) (M : GMap GoString schema.TypeDef) (tv : schema.TypeDef),
        "i" ∷ i_ptr ↦ k ∗ "Hmm" ∷ mm ↦$ M ∗ "t" ∷ t_ptr ↦ tv ∗
        "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z tys.len ∧
          ∀ n, M !! n = lastNamed (·.Name') n (tds.take (sint.nat k))⌝) $$ [i Hmm t]
    · iexists W64 0, ∅, _
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      intro n'
      rw [show sint.nat (W64 0) = 0 by rfl, List.take_zero, LawProofs.lastNamed_nil]
      rfl
    wp_for IH
    wp_if_destruct
    · have Hlt : sint.nat k < tds.length := by word
      obtain ⟨td, Htd⟩ : ∃ td, tds[sint.nat k]? = some td := ⟨_, List.getElem?_eq_getElem Hlt⟩
      have Hbnd : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z tys.len := ⟨Hk.1, Hif⟩
      simp only [Hbnd, and_self, ↓reduceIte]
      wp_apply wp_load_slice_index tys (sint.Z k) tds DFrac.discard td Hk.1 $$ [] as _
      · iframe #; ipureintro; exact Htd
      wp_apply wp_mapInsert $$ [$Hmm] as Hmm
      wp_for_post
      iframe
      iexists k + W64 1, _, td
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      intro n'
      rw [show sint.nat (k + W64 1) = sint.nat k + 1 by word, List.take_add_one, Htd,
        Option.toList_some, LawProofs.lastNamed_snoc, GMap.lookup_insert_eq_iff, Hk.2.2]
    · have HkN : sint.nat k = tds.length := by word
      have HM := Hk.2.2
      rw [HkN, List.take_length] at HM
      ihave Hown := LawProofs.ownPointer_zero (GF := GF) (T' := GoMap) _ $$ HP
      wp_bind (App (Val #(methods _ _ _)) (Val #sm_ptr))
      iapply (sync.atomic.Pointer.wp_Store (T' := GoMap) (go.string.MapType schema.TypeDef.ty)
        sc.[schema.Schema, go!"m"] sm_ptr)
      · iPkgInit
      iapply fupd_mask_intro Std.LawfulSet.empty_subset
      iintro Hmask
      inext
      iexists null
      iframe Hown
      iintro Hown
      imod Hmask with -
      imod LawProofs.ownPointer_persist _ _ _ $$ Hown with #Hown
      imod ownMap_persist _ _ _ $$ Hmm with #Hmm
      ipersist sm
      imodintro
      wp_auto
      iapply HΦ2
      iexists sm_ptr, mm, M
      iframe #
      ipureintro; exact HM
  iintro HQ
  icases HQ with ⟨%mp, %mm, %M, #Hp, #Hmp, #Hmm, %HM⟩
  wp_auto
  wp_bind (App (Val #(methods _ _ _)) (Val #()))
  iapply (sync.atomic.Pointer.wp_Load (T' := GoMap) (go.string.MapType schema.TypeDef.ty)
    sc.[schema.Schema, go!"m"] DFrac.discard)
  · iPkgInit
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists mp
  iframe #
  iintro _
  imod Hmask with -
  imodintro
  wp_auto
  wp_apply wp_map_lookup2 $$ [$Hmm] as _
  rw [HM n]
  ihave Hl := Hlk $$ %n %Hnd
  cases hf : S.find n with
  | none =>
    icases Hl with %hl
    rw [hl]
    iapply HΦ
    ipureintro; exact ⟨rfl, rfl⟩
  | some A =>
    icases Hl with ⟨%td, %hl, #Ha⟩
    rw [hl.1, Option.getD_some]
    iapply HΦ
    isplitr
    · ipureintro; exact ⟨rfl, hl.2⟩
    · iexact Ha

end proof

end smd
end EtcdGrove
end Perennial
