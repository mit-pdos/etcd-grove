/- Lean-first (no Rocq counterpart).

`checkSingle(ctx, model, history, computePartial)`: the search loop, against the abstract
search of `Theory` (`searchInv`, `Search.lean`; one `Theory` lemma per branch).
-/
module

public import Spec.github_com.anishathalye.porcupine.checkSingle
public import Spec.github_com.anishathalye.porcupine.makeLinkedEntries
public import Spec.github_com.anishathalye.porcupine.insertBefore
public import Spec.github_com.anishathalye.porcupine.newBitset
public import Spec.github_com.anishathalye.porcupine.bitset__set
public import Spec.github_com.anishathalye.porcupine.bitset__clear
public import Spec.github_com.anishathalye.porcupine.bitset__clone
public import Spec.github_com.anishathalye.porcupine.cacheKey
public import Spec.github_com.anishathalye.porcupine.cacheContains
public import Spec.github_com.anishathalye.porcupine.lift
public import Spec.github_com.anishathalye.porcupine.unlift
public import Proof.github_com.anishathalye.porcupine.Search

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace porcupine

open Iris Iris.BI Iris.ProofMode github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

set_option hygiene false in
/-- `if ctx.Err() != nil { return false, longest }`: a non-`nil` error makes the context done
(`isContext`'s `Err()`), which `checkSingle`'s postcondition allows. -/
macro "ctx_check" : tactic => `(tactic| (
  wp_apply HErrU as %err Herr
  cases err
  · simp only [reduceCtorEq, ↓reduceIte]
    icases Herr with ⟨#HPD, -⟩
    wp_auto
    wp_for_post
    iapply HΦ
    iframe
    iright; iright; iexact HPD
  iclear Herr
  wp_auto))

set_option maxHeartbeats 4000000 in
theorem checkSingle.wp_proof
    (wp_makeLinkedEntries : makeLinkedEntries.spec (GF := GF) (hG := hG))
    (wp_insertBefore : insertBefore.spec (GF := GF) (hG := hG))
    (wp_newBitset : newBitset.spec (GF := GF) (hG := hG))
    (wp_set : bitset.set.spec (GF := GF) (hG := hG))
    (wp_clear : bitset.clear.spec (GF := GF) (hG := hG))
    (wp_clone : bitset.clone.spec (GF := GF) (hG := hG))
    (wp_cacheKey : cacheKey.spec (GF := GF) (hG := hG))
    (wp_cacheContains : cacheContains.spec (GF := GF) (hG := hG))
    (wp_lift : lift.spec (GF := GF) (hG := hG))
    (wp_unlift : unlift.spec (GF := GF) (hG := hG)) :
    checkSingle.spec (GF := GF) (hG := hG) := fun σ S m c cs hsl es dq h cp hes hlen => by
  wp_start as ⟨#Hctx, #Hm, Hsl, #Hio⟩
  iunfold histIoOk at Hio
  ihave %Hsl_len := ownSlice_len $$ Hsl
  obtain ⟨Hsl_len, Hsl_nn⟩ := Hsl_len
  have hes' := hes
  obtain ⟨hlen2, hok, hent⟩ := hes'
  have hnd : (es.map entryOf).Nodup := entriesOk_nodup hok (by simpa using hlen2)
  wp_auto
  wp_apply wp_makeLinkedEntries hsl es dq h hes hlen $$ [Hsl] as %root ⟨Hsl, %loc, Hl, %Hroot⟩
  · iframe
  obtain ⟨Hroot, Hlocnn⟩ := Hroot
  have hn : BitVec.sdiv hsl.len (W64 2) = W64 h.length :=
    sdiv_two _ _ (by have := Hsl_len; rw [hlen2] at this; word) hlen
  rw [hn]
  wp_apply wp_newBitset as %lsl Hlsl
  wp_apply (wp_map_make1 (K := w64) (V := GoSlice)) as %cm Hcm
  wp_apply wp_slice_make2 (V := Loc) $$ [] as %lgst ⟨Hlgst, -⟩
  · ipureintro; word
  ihave #Hm' := Hm
  iunfold isModelFilled at Hm'
  icases Hm' with ⟨#Hinit, #Hstep, #Heh⟩
  unfold initSpec
  wp_apply Hinit as %sv0 #Hsv0
  -- the head
  irename «$a0» => Hhd
  obtain ⟨hd, hhd⟩ : ∃ hd, «$a0_ptr» = hd := ⟨_, rfl⟩
  rw [hhd]
  clear hhd
  ihave %Hhdnn := typedPointsto_not_null $$ Hhd
  have wp_head :
      {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.anishathalye.porcupine ∗
          hd ↦ (⟨interface.nil, null, W64 (-1), null, null⟩ : node) ∗
          linked loc (valOf h) null (es.map entryOf) }}
        (App (App (Val (@! github_com.anishathalye.porcupine.insertBefore)) (Val #hd)) (Val #root))
      {{ RET #hd; nodesOwn hd loc (valOf h) (es.map entryOf) [] }} := by
    wp_start_folded as ⟨Hhd, Hl⟩
    cases haes : es.map entryOf with
    | nil =>
      rw [haes] at Hroot
      simp only [headLoc] at Hroot
      subst Hroot
      wp_apply wp_insertBefore hd _ null (zero_val node) $$ [Hhd] as (⟨-, Hhd⟩ | ⟨-, Hm⟩)
      · iframe; ileft; ipureintro; rfl
      · iapply HΦ
        rw [← haes]
        iapply linked_nodesOwn hd loc (valOf h) _ hnd ⟨Hhdnn, Hlocnn⟩
        rw [haes]
        simp only [headLoc, linked]
        iframe
      · ihave %Hc := typedPointsto_not_null $$ Hm
        exact absurd rfl Hc
    | cons e0 rest =>
      rw [haes] at Hroot
      simp only [headLoc] at Hroot
      subst Hroot
      simp only [linked]
      icases Hl with ⟨He0, Hl⟩
      wp_apply wp_insertBefore hd _ (loc e0) _ $$ [Hhd He0] as (⟨%Hc, -⟩ | ⟨Hhd, He0⟩)
      · iframe; iright; iframe; ipureintro; rfl
      · exact absurd Hc (Hlocnn e0 (by rw [haes]; simp))
      · iapply HΦ
        rw [← haes]
        iapply linked_nodesOwn hd loc (valOf h) _ hnd ⟨Hhdnn, Hlocnn⟩
        rw [haes]
        rw [linkedNode_prev]
        simp only [linked, headLoc]
        iframe
  wp_apply wp_head $$ [Hhd Hl] as Hnodes
  · iframe
  -- the loop invariant
  ihave HI : (∃ (fs : List (Frame σ)) (s : σ) (p : Nat) (cache : List ((Nat → Prop) × σ)),
      "Hs" ∷ searchInv S h (es.map entryOf) hd loc entry_ptr state_ptr linearized_ptr cm
        calls_ptr fs s p cache ∗
      "Hlongest" ∷ longestOwn lgst h.length : IProp GF)
      $$ [entry Hnodes state linearized Hlsl Hcm calls Hlgst]
  · iexists [], S.M.init, 0, []
    unfold searchInv
    simp only [named]
    isplitr [Hlgst]
    · iexists sv0, lsl, _, slice.nil, []
      simp only [ids, List.map_nil, rem_nil]
      rw [show curLoc loc (es.map entryOf) 0 = root by
        rw [Hroot]; unfold curLoc headLoc; cases es.map entryOf <;> rfl]
      iframe
      iframe Hsv0
      isplitl [Hcm]
      · unfold cacheOwn
        iexists ∅
        iframe
        iapply BigSepM.bigSepM_empty.2; iempintro
      isplitl []
      · iapply ownSlice_nil
      isplitl []
      · iapply ownSliceCap_nil
      isplitl []
      · unfold callsRep; simp only [List.reverse_nil]; iapply BigSepL2.bigSepL2_nil.2; iempintro
      · ipureintro
        refine ⟨⟨by rw [List.length_replicate]; congr 1; word, fun i => ?_⟩, inv_init _ _ _,
          fun hne => List.length_pos_iff.mpr hne⟩
        rw [bsBit_replicate]; simp
    · rw [show sint.nat (W64 h.length) = h.length by word]
      iapply longestOwn_replicate
      iexact Hlgst
  irename «ctx» => Hctxp
  ihave #Hctx2 := Hctx
  iNamed Hctx2
  ihave #HErrU := HErr $$ %Broadcast.Unknown
  iclear HDeadline HDone HValue HErrDone HDoneFresh HParentCC HClosedchan HErr
  wp_for HI
  iNamed Hs
  obtain ⟨Hws1, Hws2⟩ := Hws
  obtain ⟨Hinv, Hpb⟩ := Hinv
  iunfold nodesOwn at Hnodes
  icases Hnodes with ⟨HG, %Hnn⟩
  icases nodesG_read hnd mem_slots_none _ $$ HG with ⟨Hh, HG⟩
  simp only [slotLoc]
  wp_auto
  ihave HG := HG $$ Hh
  rw [nbrLoc_head hd loc hnd]
  wp_if_destruct
  · -- the loop body: the list is not empty
    have hne : curLoc loc (rem (es.map entryOf) (ids fs)) 0 ≠ null := by
      have := go.intoVal_inj Hif; simpa using this
    have hrem : rem (es.map entryOf) (ids fs) ≠ [] := by
      intro h'; apply hne; rw [h']; rfl
    have hpl := Hpb hrem
    obtain ⟨e, he⟩ : ∃ e, (rem (es.map entryOf) (ids fs))[p]? = some e :=
      ⟨_, List.getElem?_eq_getElem hpl⟩
    rw [curLoc_some he]
    ctx_check
    -- `entry.match`
    have hes_e : e ∈ es.map entryOf := rem_get_mem he
    icases nodesG_read hnd (mem_slots_some hes_e) _ $$ HG with ⟨He, HG⟩
    simp only [slotLoc]
    wp_auto
    obtain ⟨b, y⟩ := e
    cases b with
    | false =>
      -- a call: its operation `y`, its return later in the list
      have hy : y < h.length := (hok.2.1 _).mp hes_e
      obtain ⟨o, ho⟩ : ∃ o, h[y]? = some o := ⟨_, List.getElem?_eq_getElem hy⟩
      have hres : (⟨true, y⟩ : Entry) ∈ es.map entryOf := (hok.2.1 _).mpr hy
      obtain ⟨q, hpq, hq⟩ := rem_call_has_ret hok he
      have hrnn := Hlocnn _ hres
      have hval1 : valOf h ⟨false, y⟩ = o.val.1 := by simp [valOf, ho]
      have hval2 : valOf h ⟨true, y⟩ = o.val.2 := by simp [valOf, ho]
      simp only [Bool.false_eq_true, ↓reduceIte, hrnn, _root_.decide_false, Bool.not_false]
      wp_auto
      ihave HG := HG $$ He
      icases nodesG_read hnd (mem_slots_some hres) _ $$ HG with ⟨Hr, HG⟩
      simp only [slotLoc]
      wp_auto
      ihave HG := HG $$ Hr
      rw [hval1, hval2]
      ihave #Hioy := BigSepL.bigSepL_lookup (Φ := fun _ o => S.ioOk o.val.1 o.val.2) ho $$ Hio
      iunfold stepCtxSpec at Hstep
      wp_apply Hstep $$ %(GoInterface.ok c) %sv %s %o.val.1 %o.val.2 [$Hsv $Hioy]
        as %ok %nsv ⟨%Hok, #Hpost⟩
      ctx_check
      have hpq1 : p + 1 < (rem (es.map entryOf) (ids fs)).length :=
        Nat.lt_of_le_of_lt hpq (List.getElem?_eq_some_iff.mp hq).1
      cases hst : S.M.step s (o.val.1, o.val.2) with
      | none =>
        -- the model refuses the operation: skip it
        rw [hst] at Hok
        simp only [Option.isSome_none] at Hok
        subst Hok
        wp_auto
        icases nodesG_read hnd (mem_slots_some hes_e) _ $$ HG with ⟨He, HG⟩
        simp only [slotLoc]
        wp_auto
        ihave HG := HG $$ He
        rw [nbrLoc_next hd loc hnd he]
        wp_for_post
        iframe
        iexists fs, s, p + 1, cache
        iframe
        unfold searchInv
        simp only [named]
        iexists sv, lsl, ws, csl, ces
        iframe
        iframe Hsv Hces
        isplitl [HG]
        · iunfold nodesOwn; iframe; ipureintro; exact Hnn
        ipureintro
        refine ⟨⟨Hws1, Hws2⟩, ?_, fun _ => hpq1⟩
        refine inv_skip Hinv he (fun o' t' ho' hst' => ?_)
        rw [ho] at ho'; cases ho'
        rw [hst] at hst'; cases hst'
      | some t' =>
        rw [hst] at Hok
        simp only [Option.isSome_some] at Hok
        subst Hok
        trace_state
        sorry
    | true =>
      -- a return
      trace_state
      sorry
  · -- the loop's end: the list is empty
    have hnull : curLoc loc (rem (es.map entryOf) (ids fs)) 0 = null := by
      have : ¬ ((!decide (curLoc loc (rem (es.map entryOf) (ids fs)) 0 = null)) = true) :=
        fun h' => Hif (by rw [h'])
      simpa using this
    trace_state
    sorry

end proof

end porcupine
end EtcdGrove
end Perennial
