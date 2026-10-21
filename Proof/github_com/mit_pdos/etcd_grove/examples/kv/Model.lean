/-
Lean-first (no Rocq counterpart).

The proof of `Model`: the four closures meet `initSpec`, `stepSpec`, `equalSpec` and
`hashSpec` of `kvS`; `Partition` and `StepContext` are `nil`. A state value is a read-only map
(`kvRep`): `Init` persists the fresh empty map; `Step` returns its input state for a `Get`, and
otherwise a copy (`copyMap`) with the key set, persisted. The type assertions go through by
`kvRep` and `ioOk` (a boxed map, `Input` and string), and the verdict is `kvM_step_box`'s.
`Equal`'s two `within`s make the maps agree at every key (a missing key reads `""`), so the
states are equal.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.Model
public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.copyMap
public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.within
public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.hashMap

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kv

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode go_etcd_io.raft.v3
open github_com.anishathalye.porcupine

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]

theorem Model.wp_proof
    (wp_copyMap : copyMap.spec (GF := GF) (hG := hG))
    (wp_within : within.spec (GF := GF) (hG := hG))
    (wp_hashMap : hashMap.spec (GF := GF) (hG := hG)) :
    Model.spec (GF := GF) (hG := hG) := by
  wp_start
  have Hrep : ∀ (l : Loc) (m : GMap GoString GoString) (s' : KVMap), (∀ k, (m !! k).getD [] = s' k) →
      ⊢ (iprop(l ↦$□ m) -∗ (iprop(∃ (l' : Loc) (m' : GMap GoString GoString),
        ⌜boxM l = boxM l'⌝ ∗ l' ↦$□ m' ∗ ⌜∀ k, (m' !! k).getD [] = s' k⌝) : IProp GF)) := by
    intro l m s' Hs'
    iintro #Hl
    iexists l, m
    isplitr
    · ipureintro; rfl
    isplitr
    · iexact Hl
    ipureintro; exact Hs'
  wp_func_lits
  wp_auto
  iapply HΦ
  unfold isModel isEqHash
  simp only
  isplitr
  · ipureintro; trivial
  isplitr
  · -- Init
    unfold initSpec
    iintro !> %Φ' _ HΦ'
    wp_auto
    wp_bind (App (Val #(functions go.make1 _)) _)
    iapply (wp_map_make1 (K := GoString) (V := GoString))
    · ipureintro; trivial
    iintro !> %l Hl
    imod ownMap_persist $$ Hl with #Hl
    wp_auto
    iapply HΦ'
    simp only [kvS, kvM]
    unfold kvRep
    iexists l, ∅
    isplitr
    · ipureintro; rfl
    isplitr
    · iexact Hl
    ipureintro
    intro k; rfl
  isplitr
  · -- Step
    iright
    isplitr
    · ipureintro; exact ⟨trivial, nofun⟩
    unfold stepSpec
    iintro %k %v %s %i %o
    iintro !> %Φ' Hpre HΦ'
    simp only [kvS]
    icases Hpre with ⟨-, #Hrep, %Hio⟩
    obtain ⟨⟨x, rfl⟩, str, rfl⟩ := Hio
    unfold kvRep
    icases Hrep with ⟨%l, %m, %Hv, #Hl, %Hm⟩
    subst Hv
    wp_auto
    have Hz : (zero_val GoString) = ([] : GoString) := rfl
    wp_if_destruct
    · -- Get
      replace Hif : x.Kind' = opGetB := Hif
      wp_apply wp_map_lookup1 $$ Hl as _
      simp only [Hz]
      iapply HΦ'
      have Hstep := kvM_step_box s x str
      have Hout : inOut x s = s x.Key' := by unfold inOut; rw [if_pos Hif]
      have Hst : inStep x s = s := by unfold inStep; rw [if_pos Hif]
      rw [Hout, Hst] at Hstep
      isplitl
      · iapply Hrep l m s Hm $$ Hl
      isplitr
      · ipureintro
        rw [Hstep, ← Hm]
        by_cases h : str = (m !! x.Key').getD []
        · simp [h]
        · simp [h]
      unfold github_com.anishathalye.porcupine.stepPost
      rw [Hstep]
      by_cases h : str = (m !! x.Key').getD []
      · rw [Hm] at h
        simp only [h, ↓reduceIte]
        iapply Hrep l m s Hm $$ Hl
      · rw [Hm] at h
        simp only [h, ↓reduceIte]
        ipureintro; trivial
    have Hng : ¬ x.Kind' = opGetB := Hif
    wp_apply wp_copyMap $$ [$Hl] as %c ⟨_, Hc⟩
    wp_if_destruct
    · -- Put
      replace Hif : x.Kind' = opPutB := Hif
      wp_bind (App (App (App (Val (map.insert go.string)) _) _) _)
      iapply wp_mapInsert $$ Hc
      iintro !> Hc
      imod ownMap_persist $$ Hc with #Hc
      wp_auto
      have Hst : ∀ k, ((<[x.Key' := x.Val']> m) !! k).getD [] = inStep x s k := by
        intro k
        unfold inStep; rw [if_neg Hng, if_pos Hif]
        unfold kvUpd
        rw [GMap.lookup_insert_eq_iff]
        by_cases h : x.Key' = k
        · subst h; simp
        · simp [h, Ne.symm h, Hm]
      iapply HΦ'
      have Hstep := kvM_step_box s x str
      have Hout : inOut x s = [] := by unfold inOut; rw [if_neg Hng]
      rw [Hout] at Hstep
      isplitl
      · iapply Hrep l m s Hm $$ Hl
      isplitr
      · ipureintro; rw [Hstep]; by_cases h : str = [] <;> simp [h]
      unfold github_com.anishathalye.porcupine.stepPost
      rw [Hstep]
      by_cases h : str = []
      · simp only [h, ↓reduceIte]
        iapply Hrep c _ (inStep x s) Hst $$ Hc
      · simp only [h, ↓reduceIte]
        ipureintro; trivial
    · -- Append
      replace Hif : ¬ x.Kind' = opPutB := Hif
      wp_apply wp_map_lookup1 $$ Hl as _
      simp only [Hz]
      wp_bind (App (App (App (Val (map.insert go.string)) _) _) _)
      iapply wp_mapInsert $$ Hc
      iintro !> Hc
      imod ownMap_persist $$ Hc with #Hc
      wp_auto
      have Hst : ∀ k, ((<[x.Key' := (m !! x.Key').getD [] ++ x.Val']> m) !! k).getD [] =
          inStep x s k := by
        intro k
        unfold inStep; rw [if_neg Hng, if_neg Hif]
        unfold kvUpd
        rw [GMap.lookup_insert_eq_iff]
        by_cases h : x.Key' = k
        · subst h; simp only [↓reduceIte, Option.getD_some]; rw [← Hm]
        · simp [h, Ne.symm h, Hm]
      iapply HΦ'
      have Hstep := kvM_step_box s x str
      have Hout : inOut x s = [] := by unfold inOut; rw [if_neg Hng]
      rw [Hout] at Hstep
      isplitl
      · iapply Hrep l m s Hm $$ Hl
      isplitr
      · ipureintro; rw [Hstep]; by_cases h : str = [] <;> simp [h]
      unfold github_com.anishathalye.porcupine.stepPost
      rw [Hstep]
      by_cases h : str = []
      · simp only [h, ↓reduceIte]
        iapply Hrep c _ (inStep x s) Hst $$ Hc
      · simp only [h, ↓reduceIte]
        ipureintro; trivial
  isplitr
  · ipureintro; nofun
  isplitr
  · -- Equal
    unfold equalSpec
    iintro %k %j %v %w %s %t
    iintro !> %Φ' Hpre HΦ'
    simp only [kvS]
    icases Hpre with ⟨#Hv, #Hw⟩
    unfold kvRep
    icases Hv with ⟨%la, %ma, %Hva, #Hla, %Hma⟩
    icases Hw with ⟨%lb, %mb, %Hwb, #Hlb, %Hmb⟩
    subst Hva Hwb
    wp_auto
    wp_apply wp_within la lb ma mb DFrac.discard DFrac.discard $$ [$Hla $Hlb] as %b1 ⟨_, _, %Hb1⟩
    wp_if_destruct
    · iapply HΦ'
      isplitl
      · iapply Hrep la ma s Hma $$ Hla
      isplitl
      · iapply Hrep lb mb t Hmb $$ Hlb
      ipureintro
      nofun
    · wp_apply wp_within lb la mb ma DFrac.discard DFrac.discard $$ [$Hlb $Hla] as %b2 ⟨_, _, %Hb2⟩
      iapply HΦ'
      isplitl
      · iapply Hrep la ma s Hma $$ Hla
      isplitl
      · iapply Hrep lb mb t Hmb $$ Hlb
      ipureintro
      intro h2
      have H1 := Hb1.mp rfl
      have H2 := Hb2.mp h2
      funext k
      rw [← Hma, ← Hmb]
      cases ha : ma !! k with
      | some va => rw [H1 k va ha]; rfl
      | none =>
        cases hb : mb !! k with
        | some vb => have := H2 k vb hb; rw [ha] at this; simpa using this.symm
        | none => rfl
  iright
  unfold hashSpec
  iintro %k %v %s
  iintro !> %Φ' Hv HΦ'
  simp only [kvS]
  unfold kvRep
  icases Hv with ⟨%l, %m, %Hvl, #Hl, %Hm⟩
  subst Hvl
  wp_auto
  wp_apply wp_hashMap $$ [$Hl] as %h _
  iapply HΦ'
  iapply Hrep l m s Hm $$ Hl

end proof

end kv
end EtcdGrove
end Perennial
