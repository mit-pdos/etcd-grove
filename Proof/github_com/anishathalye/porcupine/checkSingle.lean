/- Lean-first (no Rocq counterpart).

`checkSingle(ctx, model, history, computePartial)`: the search loop, against the abstract
search of `Theory` (`searchInv`, `Search.lean`; one `Theory` lemma per branch). The loop also
carries `⌜Inv …⌝ ∨ □ cs.PDone`: `StepContext` may answer `false` wrongly once the context is
done (`stepCtxSpec`), after which the search is no longer the abstract one, and an exit on
`len(calls) == 0` then answers `false` with the context done (which the spec allows).

The state values are shared in a pool `np` of non-atomic invariants allocated at the start
(`Shared.lean`), whose token the loop keeps: `Init`'s value is shared right after `Init`, a new
state's when it is pushed (`StepContext` returns it owned, and `cacheKey`/`cacheContains` take
it owned); `StepContext` on the current state opens its invariant with the later credit of a
pure step before the call, and closes it after.

A state value's index (`ModelSpec.rep`) is its depth on the stack: `Init`'s is `0`, the current
state's `|fs|`, the `i`-th oldest frame's `i` (`callsRep`); a cached value's is any. A step lifts
an operation not on the stack, so `|fs|` is below the history's length, below `2^60`
(`frames_length_lt`), as `stepCtxSpec` asks.
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
public import Proof.github_com.anishathalye.porcupine.Shared

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace porcupine

open Iris Iris.BI Iris.ProofMode github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NaInvG GF]
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

set_option hygiene false in
/-- `seq` made if `nil` (the copy of `calls`' ids) and `longest[entry.id] = &seq`, after `longest[entry.id] == nil` and after `len(*longest[entry.id]) < len(calls)`. -/
local macro "longest_update" : tactic => `(tactic| (
    -- `if seq == nil { seq = make(..); for i, v := range calls { seq[i] = v.entry.id } }`
    wp_join iprop((∃ (sl : GoSlice) (xs : List w64),
        ((seq_ptr ↦ sl ∗ sl ↦* xs) ∨ (seq_ptr ↦□ sl ∗ sl ↦*□ xs)) ∗ ⌜sl ≠ slice.nil⌝) ∗
        csl ↦* ces ∗ nodesG hd loc (valOf h) (es.map entryOf) (layout (es.map entryOf) (ids fs)) ∗
        calls_ptr ↦ csl) at next with [Hseq Hcalls HG calls] as ⟨Hseq, Hcalls, HG, calls⟩
    · icases Hseq with (Hs0 | ⟨%sl, %xs, #Hs, #Hsl, %Hslne⟩)
      · -- the copy, made now
        wp_auto
        wp_apply wp_slice_make2 (V := w64) $$ [] as %sq ⟨Hsq, -⟩
        · ipureintro; exact Hcsl2
        rename_i iu_ptr
        irename : (iu_ptr ↦ zero_val w64 : IProp GF) => Hiu
        ihave HF : (∃ (k' iv : w64) (vv' : callsEntry) (xs : List w64),
            "i" ∷ i_ptr ↦ k' ∗ "Hiu" ∷ iu_ptr ↦ iv ∗ "v" ∷ v_ptr ↦ vv' ∗ "Hsq" ∷ sq ↦* xs ∗
            "%Hk'" ∷ ⌜0 ≤ sint.Z k' ∧ sint.Z k' ≤ sint.Z csl.len ∧ xs.length = ces.length⌝ : IProp GF)
          $$ [i Hiu v Hsq]
        · iexists W64 0, _, _, _
          iframe
          ipureintro
          refine ⟨by decide, by word, ?_⟩
          rw [List.length_replicate]; word
        wp_for HF
        obtain ⟨Hk1', Hk2', Hk3'⟩ := Hk'
        (try simp only [if_decide_bool_eq_true, if_decide_bool_eq_false])
        wp_if_destruct
        · have Hb : 0 ≤ sint.Z k' ∧ sint.Z k' < sint.Z csl.len := ⟨Hk1', Hif⟩
          simp only [Hb, _root_.and_self, ↓reduceIte]
          list_elem ces (sint.nat k') as ce'
          have hkf' : sint.nat k' < fs.reverse.length := by rw [List.length_reverse, ← Hcl]; word
          list_elem fs.reverse (sint.nat k') as f'
          wp_apply wp_load_slice_index csl (sint.Z k') ces (DFrac.own 1) ce' Hk1' $$ [Hcalls] as Hcalls
          · iframe; ipureintro; exact Hce'_lookup
          ihave %Hcent' := callsRep_get S np loc ces fs Hce'_lookup Hf'_lookup $$ Hces
          have hfm' : f' ∈ fs := List.mem_reverse.mp (List.mem_of_getElem? Hf'_lookup)
          have hcm' : (⟨false, f'.id⟩ : Entry) ∈ es.map entryOf := framesPos_mem Hfp f' hfm'
          rw [Hcent']
          icases nodesG_read hnd (mem_slots_some hcm') _ $$ HG with ⟨Hc', HG⟩
          simp only [slotLoc]
          wp_auto
          ihave HG := HG $$ Hc'
          ihave %Hsql := ownSlice_len $$ Hsq
          obtain ⟨Hsql1, Hsql2⟩ := Hsql
          have Hb' : 0 ≤ sint.Z k' ∧ sint.Z k' < sint.Z sq.len := by
            constructor
            · exact Hk1'
            · have : xs.length = ces.length := Hk3'
              word
          simp only [Hb', _root_.and_self, ↓reduceIte]
          wp_apply wp_store_slice_index $$ [Hsq] as Hsq
          · iframe; ipureintro; constructor <;> word
          wp_for_post
          iframe
          iexists k' + W64 1, k', ce', _
          iframe
          ipureintro
          refine ⟨by word, by word, by simp [Hk3']⟩
        · -- the copy is made
          ihave %Hsql := ownSlice_len $$ Hsq
          obtain ⟨Hsql1, Hsql2⟩ := Hsql
          have hsqne : sq ≠ slice.nil := by
            intro h'
            subst h'
            have : xs.length = 0 := by simp [Hsql1, slice.nil]
            have : csl.len = W64 0 := len_zero_of _ (by rw [← Hcsl1, ← Hk3', this]) Hcsl2
            exact hlen0 this
          isplitr
          · itrivial
          iframe
          iexists sq, xs
          isplitl [Hs0 Hsq]
          · ileft; iframe
          ipureintro; exact hsqne
      · -- the copy, made before
        wp_auto
        simp only [Hslne, _root_.decide_false]
        wp_auto
        isplitr
        · ipureintro; rfl
        iframe
        iexists sl, xs
        isplitl []
        · iright; iframe Hs Hsl
        ipureintro; exact Hslne
    -- `longest[v.entry.id] = &seq`
    icases Hseq with ⟨%sl, %xs, Hsq, %Hslne⟩
    imod persist_or seq_ptr sl xs $$ Hsq with ⟨#Hs, #Hsl⟩
    rw [Hcent]
    icases nodesG_read hnd (mem_slots_some hcm) _ $$ HG with ⟨Hc, HG⟩
    simp only [slotLoc]
    wp_auto
    ihave HG := HG $$ Hc
    simp only [Hb2, _root_.and_self, ↓reduceIte]
    wp_apply wp_store_slice_index $$ [Hps] as Hps
    · iframe; ipureintro; constructor <;> word
    wp_for_post
    iframe
    iexists k + W64 1, ce, _
    iframe
    isplitl []
    · iapply longestElems_set ps _ seq_ptr (by word)
      iframe Hpse
      iright
      iexists sl, xs
      iframe Hs Hsl
    isplitl []
    · iright; iexists sl, xs; iframe Hs Hsl; ipureintro; exact Hslne
    ipureintro
    refine ⟨by word, by word, by simp [Hk3]⟩
  ))

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
  -- the pool of the state values' invariants
  imod (NonAtomicInvariant.alloc (GF := GF)) with ⟨%np, Htok⟩
  unfold initSpec
  wp_apply Hinit as %sv0 Hsv0
  imod shared_alloc S np ⊤ 0 sv0 S.M.init $$ Hsv0 with #Hsv0
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
      "#Hgood" ∷ (⌜Inv S.M h (es.map entryOf) fs s p cache⌝ ∨ □ cs.PDone) ∗
      "Htok" ∷ NonAtomicInvariant.own np ⊤ ∗
      "Hs" ∷ searchInv S np h (es.map entryOf) hd loc entry_ptr state_ptr linearized_ptr cm
        calls_ptr fs s p cache ∗
      "Hlongest" ∷ longestOwn lgst h.length : IProp GF)
      $$ [entry Hnodes state linearized Hlsl Hcm calls Hlgst Htok]
  · iexists [], S.M.init, 0, []
    isplitl []
    · ileft; ipureintro; exact inv_init _ _ _
    isplitl [Htok]
    · iexact Htok
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
        refine ⟨⟨by rw [List.length_replicate]; congr 1; word, fun i => ?_⟩, trivial,
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
  obtain ⟨Hfp, Hpb⟩ := Hinv
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
      wp_auto_lc 1
      ihave HG := HG $$ Hr
      rw [hval1, hval2]
      ihave #Hioy := BigSepL.bigSepL_lookup (Φ := fun _ o => S.ioOk o.val.1 o.val.2) ho $$ Hio
      iunfold stepCtxSpec at Hstep
      -- the state's index: the stack is shorter than the history
      have hyids : y ∉ ids fs := rem_get_not_mem he
      have hidsn : ∀ i ∈ ids fs, i < h.length := by
        intro i hi
        simp only [ids, List.mem_map] at hi
        obtain ⟨f, hf, rfl⟩ := hi
        exact (hok.2.1 _).mp (framesPos_mem Hfp f hf)
      have hfsl : fs.length < 2 ^ 60 := by
        have := frames_length_lt Hfp hyids hy hidsn
        omega
      ihave %Hcl0 := callsRep_length S np loc ces fs $$ Hces
      -- open the current state's invariant for the call, close it after
      imod shared_acc S np fs.length sv s $$ [$Hsv $Htok $Hlc1] with ⟨Hrep, Hclose⟩
      wp_apply Hstep $$ %c %cs %fs.length %sv %s %o.val.1 %o.val.2 [$Hctx $Hrep $Hioy]
        as %ok %nsv ⟨Hrep, Hres⟩
      · ipureintro; exact hfsl
      imod Hclose $$ Hrep with Htok
      ctx_check
      have hpq1 : p + 1 < (rem (es.map entryOf) (ids fs)).length :=
        Nat.lt_of_le_of_lt hpq (List.getElem?_eq_some_iff.mp hq).1
      cases ok with
      | false =>
        -- the step refuses the operation (the model does, or the context is done): skip it
        ihave #Hgood' : (⌜Inv S.M h (es.map entryOf) fs s (p + 1) cache⌝ ∨ □ cs.PDone : IProp GF) $$ [Hres]
        · icases Hres with (⟨%Hok, -⟩ | ⟨-, #HPD⟩)
          · icases Hgood with (%Hinv | #HPD)
            · ileft; ipureintro
              refine inv_skip Hinv he (fun o' t' ho' hst' => ?_)
              rw [ho] at ho'; cases ho'
              have hst'' : S.M.step s (o.val.1, o.val.2) = some t' := hst'
              rw [hst''] at Hok; cases Hok
            · iright; iexact HPD
          · iright; iexact HPD
        iclear Hgood
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
        isplitl []
        · iexact Hgood'
        iexists sv, lsl, ws, csl, ces
        iframe
        iframe Hsv Hces
        isplitl [HG]
        · iunfold nodesOwn; iframe; ipureintro; exact Hnn
        ipureintro
        exact ⟨⟨Hws1, Hws2⟩, Hfp, fun _ => hpq1⟩
      | true =>
        icases Hres with (⟨%Hok, Hpost⟩ | ⟨%Hc, -⟩)
        rotate_left
        · cases Hc
        obtain ⟨t', hst⟩ : ∃ t', S.M.step s (o.val.1, o.val.2) = some t' :=
          Option.isSome_iff_exists.mp Hok.symm
        iunfold stepPost at Hpost
        simp only [hst]
        wp_auto
        -- `linearized.set(uint(entry.id))`
        have hyn : y < 2 ^ 60 := by omega
        icases nodesG_read hnd (mem_slots_some hes_e) _ $$ HG with ⟨He, HG⟩
        simp only [slotLoc]
        wp_auto
        ihave HG := HG $$ He
        rw [method_unfold (t := go.GoType.PointerType bitset.ty) (m := go!"set")]
        wp_call
        wp_auto
        have hyb : uint.nat (W64 y) / 64 < ws.length := by
          rw [Hws1, show uint.nat (W64 y) = y by word]; exact bsChunks_gt _ _ hy
        wp_apply wp_set lsl ws (W64 y) hyb $$ [Hlin] as Hlin
        · iframe
        -- `key := cacheKey(model, linearized, newState)`, `bucket := cache[key]`
        wp_apply wp_cacheKey σ S m lsl (bsSet ws (W64 y)) (DFrac.own 1) (fs.length + 1) nsv t' $$ [$Heh $Hlin $Hpost]
          as %key ⟨Hlin, Hpost⟩
        iunfold cacheOwn at Hcache
        icases Hcache with ⟨%CM, Hcm, HB⟩
        wp_apply (wp_map_lookup1 (K := w64) (V := GoSlice)) $$ Hcm as Hcm
        rw [show zero_val GoSlice = slice.nil from rfl]
        icases buckets_read S np h.length cache CM key $$ HB with ⟨⟨%bces, #Hbk, #Hbces⟩, HB⟩
        -- `cacheContains(model, bucket, linearized, newState)`
        wp_apply wp_cacheContains σ S m np (cacheP h.length cache) _ bces DFrac.discard lsl _
          (DFrac.own 1) (fs.length + 1) nsv t' $$ [$Heh $Hbk $Hbces $Hlin $Hpost $Htok]
          as %hit ⟨-, Hlin, Hpost, Htok, %Hhit⟩
        have hyids : y ∉ ids fs := rem_get_not_mem he
        have hidsn : ∀ i ∈ ids fs, i < h.length := by
          intro i hi
          simp only [ids, List.mem_map] at hi
          obtain ⟨f, hf, rfl⟩ := hi
          exact (hok.2.1 _).mp (framesPos_mem Hfp f hf)
        have hbits1 : ∀ i, bsBit (bsSet ws (W64 y)) i = decide (i ∈ y :: ids fs) := by
          intro i
          rw [bsBit_set _ _ _ hyb, Hws2, show uint.nat (W64 y) = y by word]
          by_cases hiy : i = y <;> simp [hiy]
        cases hit
        · -- not in the cache: push
          wp_auto
          rw [method_unfold (t := go.GoType.PointerType bitset.ty) (m := go!"clone")]
          wp_call
          wp_auto
          wp_apply wp_clone lsl (bsSet ws (W64 y)) (DFrac.own 1) $$ [Hlin] as %lin2 ⟨Hlin, Hlin2⟩
          · iframe
          ipersist Hlin2
          -- the new state, shared
          imod shared_alloc S np ⊤ (fs.length + 1) nsv t' $$ Hpost with #Hpost
          -- the new cache entry, and the cache with its configuration
          let cnew : (Nat → Prop) × σ := (fun i => i ∈ y :: ids fs, t')
          have hcnew : cacheP h.length (cnew :: cache) (bsSet ws (W64 y)) t' := by
            refine ⟨cnew, List.mem_cons_self .., fun i => ?_, rfl⟩
            simp only [cnew, hbits1 i, decide_eq_true_eq]
            constructor
            · intro hi
              refine ⟨?_, hi⟩
              rcases List.mem_cons.mp hi with rfl | hi
              · exact hy
              · exact hidsn i hi
            · exact fun h' => h'.2
          ihave HB := buckets_cons S np h.length cache cnew CM $$ HB
          icases buckets_take S np h.length (cnew :: cache) CM key $$ HB with ⟨Hbo, HBback⟩
          iunfold bucketOwn at Hbo
          icases Hbo with ⟨%bces2, #Hbk2, Hbcap, #Hbces2⟩
          wp_apply wp_slice_literal
          isplitr
          · ipureintro; rfl
          iintro %litp ⟨Hlit, -⟩
          wp_apply wp_slice_append_persistent $$ [Hbk2 Hbcap Hlit] as %bk' ⟨#Hbk', Hbcap', -⟩
          · iframe Hbk2 Hbcap Hlit
          wp_auto
          wp_apply wp_mapInsert $$ Hcm as Hcm
          ihave HB := HBback $$ %bk' [Hbcap']
          · iunfold bucketOwn
            iexists bces2 ++ [⟨lin2, nsv⟩]
            iframe Hbk' Hbcap'
            iapply BigSepL.bigSepL_snoc.2
            iframe Hbces2
            iunfold cacheEntryOk
            iexists bsSet ws (W64 y), t', fs.length + 1
            iframe Hlin2 Hpost
            ipureintro; exact hcnew
          -- `calls = append(calls, callsEntry{entry, state})`
          wp_apply wp_slice_literal
          isplitr
          · ipureintro; rfl
          iintro %litc ⟨Hlitc, -⟩
          wp_apply wp_slice_append $$ [Hcalls Hcap Hlitc] as %csl' ⟨Hcalls, Hcap, -⟩
          · iframe Hcalls Hcap Hlitc
          wp_auto
          -- `lift(entry)`
          wp_apply wp_lift hd loc (valOf h) (es.map entryOf) (ids fs) p q y hnd he hpq hq $$ [HG]
            as Hnodes
          · iunfold nodesOwn; iframe; ipureintro; exact Hnn
          -- `entry = headEntry.next`
          iunfold nodesOwn at Hnodes
          icases Hnodes with ⟨HG, %Hnn'⟩
          icases nodesG_read hnd mem_slots_none _ $$ HG with ⟨Hh, HG⟩
          simp only [slotLoc]
          wp_auto
          ihave HG := HG $$ Hh
          rw [nbrLoc_head' hd loc hnd]
          ihave #Hgood' : (⌜Inv S.M h (es.map entryOf) (⟨y, s, p⟩ :: fs) t' 0 (cnew :: cache)⌝ ∨
              □ cs.PDone : IProp GF) $$ []
          · icases Hgood with (%Hinv | #HPD)
            · ileft; ipureintro; exact inv_push Hinv he ho (by simpa using hst)
            · iright; iexact HPD
          iclear Hgood
          wp_for_post
          iframe
          iexists ⟨y, s, p⟩ :: fs, t', 0, cnew :: cache
          iframe
          unfold searchInv
          simp only [named]
          isplitl []
          · iexact Hgood'
          iexists nsv, lsl, bsSet ws (W64 y), csl', ces ++ [⟨loc ⟨false, y⟩, sv⟩]
          iframe
          iframe Hpost
          isplitl [HG]
          · iunfold nodesOwn; iframe; ipureintro; exact Hnn'
          isplitl [Hcm HB]
          · iunfold cacheOwn; iexists _; iframe
          isplitl []
          · simp only [callsRep, List.reverse_cons]
            iapply BigSepL2.bigSepL2_snoc.2
            rw [Hcl0]
            iframe Hces Hsv
            ipureintro; rfl
          ipureintro
          exact ⟨⟨by rw [bsSet_length]; exact Hws1, hbits1⟩, ⟨Hfp, he⟩, fun hne => List.length_pos_iff.mpr hne⟩
        · -- in the cache: skip
          wp_auto
          icases nodesG_read hnd (mem_slots_some hes_e) _ $$ HG with ⟨He, HG⟩
          simp only [slotLoc]
          wp_auto
          ihave HG := HG $$ He
          rw [method_unfold (t := go.GoType.PointerType bitset.ty) (m := go!"clear")]
          wp_call
          wp_auto
          have hyb' : uint.nat (W64 y) / 64 < (bsSet ws (W64 y)).length := by rw [bsSet_length]; exact hyb
          wp_apply wp_clear lsl (bsSet ws (W64 y)) (W64 y) hyb' $$ [Hlin] as Hlin
          · iframe
          icases nodesG_read hnd (mem_slots_some hes_e) _ $$ HG with ⟨He, HG⟩
          simp only [slotLoc]
          wp_auto
          ihave HG := HG $$ He
          rw [nbrLoc_next hd loc hnd he]
          ihave #Hgood' : (⌜Inv S.M h (es.map entryOf) fs s (p + 1) cache⌝ ∨ □ cs.PDone : IProp GF) $$ []
          · icases Hgood with (%Hinv | #HPD)
            · ileft; ipureintro
              refine inv_skip Hinv he (fun o' t'' ho' hst' => ?_)
              rw [ho] at ho'; cases ho'
              rw [hst] at hst'; cases hst'
              obtain ⟨c', hc', h1, h2⟩ := Hhit rfl
              refine ⟨c', hc', fun i => ?_, h2⟩
              rw [h1 i, hbits1 i]
              constructor
              · rintro ⟨_, hb⟩; simpa using hb
              · intro hi
                have : i < h.length := by
                  rcases List.mem_cons.mp hi with rfl | hi
                  · exact hy
                  · exact hidsn i hi
                exact ⟨this, by simpa using hi⟩
            · iright; iexact HPD
          iclear Hgood
          wp_for_post
          iframe
          iexists fs, s, p + 1, cache
          iframe
          unfold searchInv
          simp only [named]
          isplitl []
          · iexact Hgood'
          iexists sv, lsl, _, csl, ces
          iframe
          iframe Hsv Hces
          isplitl [HG]
          · iunfold nodesOwn; iframe; ipureintro; exact Hnn
          isplitl [Hcm HB]
          · iunfold cacheOwn; iexists CM; iframe
          ipureintro
          refine ⟨⟨by rw [bsClear_length, bsSet_length]; exact Hws1, fun i => ?_⟩, Hfp, fun _ => hpq1⟩
          rw [bsBit_clear _ _ _ hyb', hbits1, show uint.nat (W64 y) = y by word]
          by_cases hiy : i = y
          · subst hiy; simp [hyids]
          · simp [hiy]
    | true =>
      -- a return
      simp only [↓reduceIte, _root_.decide_true, Bool.not_true]
      wp_auto
      ihave HG := HG $$ He
      ihave %Hcl := callsRep_length S np loc ces fs $$ Hces
      ihave %Hcsl := ownSlice_len $$ Hcalls
      obtain ⟨Hcsl1, Hcsl2⟩ := Hcsl
      wp_if_destruct
      · -- `len(calls) == 0`: not linearizable
        have hfs : fs = [] := by
          apply List.eq_nil_of_length_eq_zero; rw [← Hcl, Hcsl1]; word
        subst hfs
        wp_for_post
        iapply HΦ
        iframe
        icases Hgood with (%Hinv | #HPD)
        · iright; ileft; ipureintro
          exact inv_fail hok Hinv he rfl
        · iright; iright; iexact HPD
      -- `if computePartial { ... }`: memory safety only
      wp_join iprop(longestOwn lgst h.length ∗ csl ↦* ces ∗
          nodesG hd loc (valOf h) (es.map entryOf) (layout (es.map entryOf) (ids fs)) ∗
          longest_ptr ↦ lgst ∗ calls_ptr ↦ csl)
        with [Hlongest Hcalls HG longest calls] as ⟨Hlongest, Hcalls, HG, longest, calls⟩
      · -- `computePartial`
        ihave %Hcl := callsRep_length S np loc ces fs $$ Hces
        ihave %Hcsl := ownSlice_len $$ Hcalls
        obtain ⟨Hcsl1, Hcsl2⟩ := Hcsl
        iunfold longestOwn at Hlongest
        icases Hlongest with ⟨%ps0, Hps, %Hps0, #Hpse⟩
        ihave %Hlgl := ownSlice_len $$ Hps
        obtain ⟨Hlgl1, Hlgl2⟩ := Hlgl
        irename : (seq_ptr ↦ slice.nil : IProp GF) => Hseq0
        ihave HP : (∃ (k : w64) (vv : callsEntry) (ps : List Loc),
            "i" ∷ i_ptr ↦ k ∗ "v" ∷ v_ptr ↦ vv ∗ "Hps" ∷ lgst ↦* ps ∗
            "#Hpse" ∷ ([∗list] p ∈ ps, longestElem (GF := GF) p) ∗
            "Hseq" ∷ (seq_ptr ↦ slice.nil ∨
              ∃ (sl : GoSlice) (xs : List w64), seq_ptr ↦□ sl ∗ sl ↦*□ xs ∗ ⌜sl ≠ slice.nil⌝) ∗
            "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z csl.len ∧ ps.length = h.length⌝ : IProp GF)
          $$ [i v Hps Hseq0]
        · iexists W64 0, _, ps0
          iframe
          iframe Hpse
          isplitl [Hseq0]
          · ileft; iexact Hseq0
          ipureintro
          exact ⟨by decide, by word, Hps0⟩
        have hlen0 : csl.len ≠ W64 0 := Hif
        clear Hif
        wp_for HP
        obtain ⟨Hk1, Hk2, Hk3⟩ := Hk
        (try simp only [if_decide_bool_eq_true, if_decide_bool_eq_false])
        wp_if_destruct
        · have Hb : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z csl.len := ⟨Hk1, Hif⟩
          simp only [Hb, _root_.and_self, ↓reduceIte]
          list_elem ces (sint.nat k) as ce
          have hkf : sint.nat k < fs.reverse.length := by rw [List.length_reverse, ← Hcl]; word
          list_elem fs.reverse (sint.nat k) as f
          wp_apply wp_load_slice_index csl (sint.Z k) ces (DFrac.own 1) ce Hk1 $$ [Hcalls] as Hcalls
          · iframe; ipureintro; exact Hce_lookup
          ihave %Hcent := callsRep_get S np loc ces fs Hce_lookup Hf_lookup $$ Hces
          have hfm : f ∈ fs := List.mem_reverse.mp (List.mem_of_getElem? Hf_lookup)
          have hcm : (⟨false, f.id⟩ : Entry) ∈ es.map entryOf := framesPos_mem Hfp f hfm
          have hfid : f.id < h.length := (hok.2.1 _).mp hcm
          rw [Hcent]
          icases nodesG_read hnd (mem_slots_some hcm) _ $$ HG with ⟨Hc, HG⟩
          simp only [slotLoc]
          wp_auto
          ihave HG := HG $$ Hc
          ihave %Hpsl := ownSlice_len $$ Hps
          obtain ⟨Hpsl1, Hpsl2⟩ := Hpsl
          have hfidw : sint.Z (W64 f.id) = (f.id : Int) := by word
          have Hb2 : 0 ≤ sint.Z (W64 f.id) ∧ sint.Z (W64 f.id) < sint.Z lgst.len := by
            rw [hfidw]; constructor
            · omega
            · have : f.id < ps.length := by rw [Hk3]; exact hfid
              word
          simp only [Hb2, _root_.and_self, ↓reduceIte]
          list_elem ps f.id as p0
          wp_apply wp_load_slice_index lgst (sint.Z (W64 f.id)) ps _ p0 Hb2.1 $$ [Hps] as Hps
          · iframe; ipureintro; rw [hfidw]; simpa using Hp0_lookup
          ihave #Hp0 := longestElems_get ps f.id p0 Hp0_lookup $$ Hpse
          by_cases hp0 : p0 = null
          · simp only [hp0, _root_.decide_true]
            wp_auto
            longest_update
          · simp only [hp0, _root_.decide_false]
            wp_auto
            rw [Hcent]
            icases nodesG_read hnd (mem_slots_some hcm) _ $$ HG with ⟨Hc, HG⟩
            simp only [slotLoc]
            wp_auto
            ihave HG := HG $$ Hc
            simp only [Hb2, _root_.and_self, ↓reduceIte]
            wp_apply wp_load_slice_index lgst (sint.Z (W64 f.id)) ps _ p0 Hb2.1 $$ [Hps] as Hps
            · iframe; ipureintro; rw [hfidw]; simpa using Hp0_lookup
            icases Hp0 with (%hn | ⟨%sl0, %xs0, #Hp0s, #Hsl0⟩)
            · exact absurd hn hp0
            wp_auto
            by_cases hlt : sint.Z sl0.len < sint.Z csl.len
            · simp only [hlt, _root_.decide_true]
              wp_auto
              longest_update
            · simp only [hlt, _root_.decide_false]
              wp_auto
              wp_for_post
              iframe
              iexists k + W64 1, ce, ps
              iframe
              iframe Hpse
              ipureintro
              refine ⟨by word, by word, Hk3⟩
        · -- the loop's end
          iframe
          iunfold longestOwn
          iexists ps
          iframe Hps Hpse
          ipureintro; exact Hk3
      -- `callsTop := calls[len(calls)-1]`
      have hlen0 : csl.len ≠ W64 0 := Hif
      have hfs : fs ≠ [] := by
        intro h'; rw [h'] at Hcl; apply hlen0; simp at Hcl; rw [Hcl] at Hcsl1
        exact len_zero_of _ Hcsl1 Hcsl2
      obtain ⟨f, fs', rfl⟩ := List.exists_cons_of_ne_nil hfs
      icases callsRep_pop S np loc ces f fs' $$ Hces with ⟨%ces', %ce, %Hce, #Hcsv, #Hces'⟩
      obtain ⟨rfl, Hcent⟩ := Hce
      have hcl' : ces'.length = fs'.length := by simpa using Hcl
      have hlen1 : sint.Z (csl.len - W64 1) = ces'.length := by
        have : (ces'.length + 1 : Nat) = sint.nat csl.len := by simpa using Hcsl1
        word
      have Hb : 0 ≤ sint.Z (csl.len - W64 1) ∧ sint.Z (csl.len - W64 1) < sint.Z csl.len := by
        constructor <;> word
      simp only [Hb, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index csl _ (ces' ++ [ce]) (DFrac.own 1) ce Hb.1 $$ [Hcalls] as Hcalls
      · iframe; ipureintro; rw [hlen1]; simp
      -- the frame's call
      obtain ⟨hfr, hpos⟩ := Hfp
      have hcm : (⟨false, f.id⟩ : Entry) ∈ es.map entryOf := rem_get_mem hpos
      have hfid : f.id < h.length := (hok.2.1 _).mp hcm
      have hfnot : f.id ∉ ids fs' := rem_get_not_mem hpos
      obtain ⟨q', hpq', hq'⟩ := rem_call_has_ret hok hpos
      rw [Hcent]
      icases nodesG_read hnd (mem_slots_some hcm) _ $$ HG with ⟨Hc, HG⟩
      simp only [slotLoc]
      wp_auto
      ihave HG := HG $$ Hc
      -- `linearized.clear(uint(entry.id))`
      rw [method_unfold (t := go.GoType.PointerType bitset.ty) (m := go!"clear")]
      wp_call
      wp_auto
      have hfb : uint.nat (W64 f.id) / 64 < ws.length := by
        rw [Hws1, show uint.nat (W64 f.id) = f.id by word]; exact bsChunks_gt _ _ hfid
      wp_apply wp_clear lsl ws (W64 f.id) hfb $$ [Hlin] as Hlin
      · iframe
      -- `calls = calls[:len(calls)-1]`
      ihave %Hwf := ownSlice_wf $$ Hcalls
      obtain ⟨Hwf1, Hwf2⟩ := Hwf
      have Hb2 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (csl.len - W64 1) ∧
          sint.Z (csl.len - W64 1) ≤ sint.Z csl.cap := by
        refine ⟨by decide, by word, by word⟩
      simp only [Hb2, _root_.and_self, ↓reduceIte]
      icases ownSlice_slice_with_cap (W64 0) (csl.len - W64 1) csl (ces' ++ [ce])
        ⟨by decide, by word, by word⟩ $$ [Hcalls Hcap] with ⟨-, Hcalls, Hcap⟩
      · iframe
      have hsub : subslice (sint.nat (W64 0)) (sint.nat (csl.len - W64 1)) (ces' ++ [ce]) = ces' := by
        rw [show sint.nat (W64 0) = 0 from rfl, show sint.nat (csl.len - W64 1) = ces'.length by word]
        simp [subslice]
      rw [hsub]
      wp_auto
      -- `unlift(entry)`
      wp_apply wp_unlift hd loc (valOf h) (es.map entryOf) (ids fs') f.pos q' f.id hnd hpos hpq' hq'
        $$ [HG] as Hnodes
      · iunfold nodesOwn; iframe; ipureintro; exact Hnn
      -- `entry = entry.next`
      iunfold nodesOwn at Hnodes
      icases Hnodes with ⟨HG, %Hnn'⟩
      icases nodesG_read hnd (mem_slots_some hcm) _ $$ HG with ⟨Hc, HG⟩
      simp only [slotLoc]
      wp_auto
      ihave HG := HG $$ Hc
      rw [nbrLoc_next hd loc hnd hpos]
      ihave #Hgood' : (⌜Inv S.M h (es.map entryOf) fs' f.pre (f.pos + 1) cache⌝ ∨ □ cs.PDone : IProp GF) $$ []
      · icases Hgood with (%Hinv | #HPD)
        · ileft; ipureintro; exact inv_pop hok Hinv he rfl
        · iright; iexact HPD
      iclear Hgood
      wp_for_post
      iframe
      iexists fs', f.pre, f.pos + 1, cache
      iframe
      unfold searchInv
      simp only [named]
      isplitl []
      · iexact Hgood'
      iexists ce.state', lsl, bsClear ws (W64 f.id), _, ces'
      iframe
      iframe Hcsv Hces'
      isplitl [HG]
      · iunfold nodesOwn; iframe; ipureintro; exact Hnn'
      ipureintro
      refine ⟨⟨by rw [bsClear_length]; exact Hws1, fun i => ?_⟩, hfr, fun _ => ?_⟩
      · rw [bsBit_clear _ _ _ hfb, Hws2, show uint.nat (W64 f.id) = f.id by word]
        by_cases hif : i = f.id
        · subst hif; simp [hfnot]
        · simp [ids, hif]
      · exact Nat.lt_of_le_of_lt hpq' (List.getElem?_eq_some_iff.mp hq').1
  · -- the loop's end: the list is empty
    have hnull : curLoc loc (rem (es.map entryOf) (ids fs)) 0 = null := by
      have : ¬ ((!decide (curLoc loc (rem (es.map entryOf) (ids fs)) 0 = null)) = true) :=
        fun h' => Hif (by rw [h'])
      simpa using this
    rw [hnull]
    simp only [_root_.decide_true, Bool.not_true, ↓reduceIte]
    wp_auto
    ihave %Hcl := callsRep_length S np loc ces fs $$ Hces
    ihave %Hcsl := ownSlice_len $$ Hcalls
    obtain ⟨Hcsl1, Hcsl2⟩ := Hcsl
    wp_apply wp_slice_make2 (V := w64) $$ [] as %sq ⟨Hsq, -⟩
    · ipureintro; exact Hcsl2
    rename_i iu_ptr
    irename : (iu_ptr ↦ zero_val w64 : IProp GF) => Hiu
    ihave HF : (∃ (k iv : w64) (vv : callsEntry) (xs : List w64),
        "i" ∷ i_ptr ↦ k ∗ "Hiu" ∷ iu_ptr ↦ iv ∗ "v" ∷ v_ptr ↦ vv ∗ "Hsq" ∷ sq ↦* xs ∗
        "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z csl.len ∧ xs.length = ces.length⌝ : IProp GF)
      $$ [i Hiu v Hsq]
    · iexists W64 0, _, _, _
      iframe
      ipureintro
      refine ⟨by decide, by word, ?_⟩
      rw [List.length_replicate]; word
    wp_for HF
    obtain ⟨Hk1, Hk2, Hk3⟩ := Hk
    (try simp only [if_decide_bool_eq_true, if_decide_bool_eq_false])
    wp_if_destruct
    · have Hb : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z csl.len := ⟨Hk1, Hif⟩
      simp only [Hb, _root_.and_self, ↓reduceIte]
      list_elem ces (sint.nat k) as ce
      have hkf : sint.nat k < fs.reverse.length := by rw [List.length_reverse, ← Hcl]; word
      list_elem fs.reverse (sint.nat k) as f
      wp_apply wp_load_slice_index csl (sint.Z k) ces (DFrac.own 1) ce Hk1 $$ [Hcalls] as Hcalls
      · iframe; ipureintro; exact Hce_lookup
      ihave %Hcent := callsRep_get S np loc ces fs Hce_lookup Hf_lookup $$ Hces
      have hfm : f ∈ fs := List.mem_reverse.mp (List.mem_of_getElem? Hf_lookup)
      have hcm : (⟨false, f.id⟩ : Entry) ∈ es.map entryOf := framesPos_mem Hfp f hfm
      rw [Hcent]
      icases nodesG_read hnd (mem_slots_some hcm) _ $$ HG with ⟨Hc, HG⟩
      simp only [slotLoc]
      wp_auto
      ihave HG := HG $$ Hc
      ihave %Hsql := ownSlice_len $$ Hsq
      obtain ⟨Hsql1, Hsql2⟩ := Hsql
      have Hb' : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z sq.len := by
        constructor
        · exact Hk1
        · have : xs.length = ces.length := Hk3
          word
      simp only [Hb', _root_.and_self, ↓reduceIte]
      wp_apply wp_store_slice_index $$ [Hsq] as Hsq
      · iframe; ipureintro; constructor <;> word
      wp_for_post
      iframe
      iexists k + W64 1, k, ce, _
      iframe
      ipureintro
      refine ⟨by word, by word, by simp [Hk3]⟩
    · -- the copy loop exit
      -- the copy is made: read-only from now on; every `longest[i]` points to it
      ipersist seq
      ipersist Hsq
      iunfold longestOwn at Hlongest
      icases Hlongest with ⟨%ps, Hps, %Hpsl, #Hpse⟩
      ihave HL : (∃ (k : w64) (ps' : List Loc),
          "i" ∷ i_ptr ↦ k ∗ "Hps" ∷ lgst ↦* ps' ∗ "#Hpse" ∷ ([∗list] p ∈ ps', longestElem (GF := GF) p) ∗
          "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ h.length ∧ ps'.length = h.length⌝ : IProp GF)
        $$ [i Hps]
      · iexists W64 0, ps
        iframe
        iframe Hpse
        ipureintro
        exact ⟨by decide, by word, Hpsl⟩
      wp_for HL
      obtain ⟨Hk1, Hk2, Hk3⟩ := Hk
      ihave %Hpsl' := ownSlice_len $$ Hps
      obtain ⟨Hpsl1, Hpsl2⟩ := Hpsl'
      (try simp only [if_decide_bool_eq_true, if_decide_bool_eq_false])
      wp_if_destruct
      · have Hb : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z lgst.len := by
          constructor
          · exact Hk1
          · exact idx_lt_of k lgst.len h.length hlen Hif (Hk3.symm.trans Hpsl1) Hpsl2
        simp only [Hb, _root_.and_self, ↓reduceIte]
        wp_apply wp_store_slice_index $$ [Hps] as Hps
        · iframe; ipureintro; constructor <;> word
        wp_for_post
        iframe
        iexists k + W64 1, _
        iframe
        isplitl []
        · iapply longestElems_set ps' (sint.Z k).toNat seq_ptr (by word)
          iframe Hpse
          iright
          iexists sq, xs
          iframe seq Hsq
        ipureintro
        refine ⟨by word, by word, by simp [Hk3]⟩
      · iapply HΦ
        isplitl []
        · ileft; ipureintro; rfl
        iunfold longestOwn
        iexists ps'
        iframe Hps Hpse
        ipureintro; exact Hk3

end proof

end porcupine
end EtcdGrove
end Perennial
