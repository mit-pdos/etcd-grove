/- Lean-first (no Rocq counterpart).

`(*client).lift(ctx, model, consistency, oldState, cache, serialized)` (dag.go, PR #46): the model's
step through `consistency.Valid.Step` (`RVal.Step`, which calls the model's `StepContext` on the
shared current state, opened with the later credit of a pure step), then v1.3.1's cache steps: the
bit set, the bucket's loop (each entry's state opened for `Equal`, as v1.3.1's `cacheContains`), and
on a miss the new entry appended (the new state shared in the pool) and the head moved on. On a hit
the bit is cleared again, which gives the words back (`bsClear_bsSet`: the bit was clear).
-/
module

public import PorcupineDag.Spec.github_com.anishathalye.porcupine.client__lift
public import PorcupineDag.Spec.github_com.anishathalye.porcupine.bitset__set
public import PorcupineDag.Spec.github_com.anishathalye.porcupine.bitset__hash
public import PorcupineDag.Spec.github_com.anishathalye.porcupine.bitset__equal
public import PorcupineDag.Spec.github_com.anishathalye.porcupine.bitset__clear
public import PorcupineDag.Spec.github_com.anishathalye.porcupine.bitset__clone
public import PorcupineDag.Proof.github_com.anishathalye.porcupine.SearchLemmas
public import PorcupineDag.Proof.github_com.anishathalye.porcupine.DagLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace porcupine

open Iris Iris.BI Iris.ProofMode github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

set_option hygiene false in
/-- The cache miss: `cache[hash] = append(cache[hash], cacheEntry{serialized.clone(), newState})`,
`c.head++`, `return newState, true`. -/
local macro "lift_tail" : tactic => `(tactic| (
  wp_apply (wp_map_lookup1 (K := w64) (V := GoSlice)) $$ Hcm as Hcm
  rw [method_unfold (t := go.GoType.PointerType bitset.ty) (m := go!"clone")]
  wp_call
  wp_auto
  wp_apply wp_clone lsl (bsSet ws co.id') (DFrac.own 1) $$ [Hlin] as %lin2 ⟨Hlin, Hlin2⟩
  · iframe
  ipersist Hlin2
  imod shared_alloc S np ⊤ (k + 1) nsv t' $$ Hpost with #Hpost
  ihave HB := buckets_cons S np h.length cache (fun i => i ∈ y :: B, t') CM $$ HB
  icases buckets_take S np h.length ((fun i => i ∈ y :: B, t') :: cache) CM key $$ HB
    with ⟨Hbo, HBback⟩
  iunfold bucketOwn at Hbo
  icases Hbo with ⟨%bces2, #Hbk2, Hbcap, #Hbces2⟩
  rw [show zero_val GoSlice = slice.nil from rfl]
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
    iexists bsSet ws co.id', t', k + 1
    iframe Hlin2 Hpost
    ipureintro; exact hcnew
  try wp_auto
  iapply HΦ
  iframe
  iright
  isplitr
  · ipureintro; rfl
  iexists t', bsSet ws co.id'
  iframe Hpost
  isplitr
  · ipureintro; first | rfl | exact hst
  iframe
  isplitl
  · iunfold cacheOwn; iexists _; iframe
  ipureintro; exact ⟨bsSet_length _ _, hbits1⟩))

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NaInvG GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

theorem client.lift.wp_proof
    (wp_set : bitset.set.spec (GF := GF) (hG := hG))
    (wp_hash : bitset.hash.spec (GF := GF) (hG := hG))
    (wp_equal : bitset.equal.spec (GF := GF) (hG := hG))
    (wp_clear : bitset.clear.spec (GF := GF) (hG := hG))
    (wp_clone : bitset.clone.spec (GF := GF) (hG := hG)) :
    client.lift.spec (GF := GF) (hG := hG) := by
  intro σ S m ctx ctxd cons np h cp cv cos dq co y o B k sv s cm lin_ptr lsl ws cache
    hhd hco hcoid hy hin hout hyB hB hyl hk hhl hws1 hws2
  wp_start as ⟨#Hctx, #Hm, #Hcons, #Hio, Hc, Hcos, #Hsv, Htok, Hcache, lin, Hlin⟩
  ihave %Hcosl := ownSlice_len $$ Hcos
  have hhdl : sint.nat cv.head' < cos.length := (List.getElem?_eq_some_iff.mp hco).1
  wp_auto
  have Hb : 0 ≤ sint.Z cv.head' ∧ sint.Z cv.head' < sint.Z cv.cltOps'.len := by
    obtain ⟨h1, h2⟩ := Hcosl; rw [snat_eq] at hhdl h1; omega
  simp only [Hb, _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index cv.cltOps' _ cos dq co Hb.1 $$ [Hcos] as Hcos
  · iframe; ipureintro; rw [← snat_eq]; exact hco
  -- `consistency.Valid.Step`: `RVal.Step`, the model's `StepContext`
  ihave #Hcons' := Hcons
  iunfold isLinearizability at Hcons'
  icases Hcons' with ⟨-, %Hval⟩
  rw [Hval, show rvalV.Step' = rvStepV from rfl, rvStepV_val]
  wp_auto_lc 1
  ihave #Hm' := Hm
  iunfold isModelFilled at Hm'
  icases Hm' with ⟨-, #Hstep, #Heh⟩
  iunfold stepCtxSpec at Hstep
  imod shared_acc S np k sv s $$ [$Hsv $Htok $Hlc1] with ⟨Hrep, Hclose⟩
  rw [hin, hout]
  wp_apply Hstep $$ %ctx %ctxd %k %sv %s %o.val.1 %o.val.2 [$Hctx $Hrep $Hio]
    as %ok %nsv ⟨Hrep, Hres⟩
  · ipureintro; omega
  imod Hclose $$ Hrep with Htok
  cases ok with
  | false =>
    -- refused: the model refuses, or the context is done
    wp_auto
    iapply HΦ
    iframe
    ileft
    iframe
    isplitr
    · ipureintro; rfl
    icases Hres with (⟨%Hok, -⟩ | ⟨-, #HPD⟩)
    · ileft; ipureintro
      cases hst : S.M.step s o.val with
      | none => rfl
      | some t' => exact absurd (hst ▸ Hok : false = (some t').isSome) (by simp)
    · iright; ileft; iexact HPD
  | true =>
    icases Hres with (⟨%Hok, Hpost⟩ | ⟨%Hc, -⟩)
    rotate_left
    · cases Hc
    obtain ⟨t', hst⟩ : ∃ t', S.M.step s o.val = some t' :=
      Option.isSome_iff_exists.mp Hok.symm
    iunfold stepPost at Hpost
    simp only [hst]
    wp_auto
    -- `serialized.set(uint(cltOp.id))`
    have hyw : uint.nat co.id' = y := by
      have := hcoid; have := hyl; have := hhl; word
    have hyb : uint.nat co.id' / 64 < ws.length := by
      rw [hyw, hws1]; exact bsChunks_gt _ _ hyl
    rw [method_unfold (t := go.GoType.PointerType bitset.ty) (m := go!"set")]
    wp_call
    wp_auto
    wp_apply wp_set lsl ws co.id' hyb $$ [Hlin] as Hlin
    · iframe
    have hbits1 : ∀ i, bsBit (bsSet ws co.id') i = decide (i ∈ y :: B) := by
      intro i
      rw [bsBit_set _ _ _ hyb, hws2, hyw]
      by_cases hiy : i = y <;> simp [hiy]
    -- `hash := serialized.hash()`
    rw [method_unfold (t := go.GoType.PointerType bitset.ty) (m := go!"hash")]
    wp_call
    wp_auto
    wp_apply wp_hash lsl (bsSet ws co.id') (DFrac.own 1) $$ [Hlin] as %key Hlin
    · iframe
    -- `entries, ok := cache[hash]`
    iunfold cacheOwn at Hcache
    icases Hcache with ⟨%CM, Hcm, HB⟩
    wp_apply (wp_map_lookup2 (K := w64) (V := GoSlice)) $$ Hcm as Hcm
    icases buckets_read S np h.length cache CM key $$ HB with ⟨⟨%bces, #Hbk, #Hbces⟩, HB⟩
    have hidsn : ∀ i ∈ y :: B, i < h.length := by
      intro i hi; rcases List.mem_cons.mp hi with rfl | hi
      · exact hyl
      · exact hB i hi
    have hcnew : cacheP h.length ((fun i => i ∈ y :: B, t') :: cache) (bsSet ws co.id') t' := by
      refine ⟨_, List.mem_cons_self .., fun i => ?_, rfl⟩
      simp only [hbits1 i, decide_eq_true_eq]
      exact ⟨fun hi => ⟨hidsn i hi, hi⟩, fun h' => h'.2⟩
    wp_if_destruct
    · -- the bucket's loop (v1.3.1's `cacheContains`)
      rw [show zero_val GoSlice = slice.nil from rfl]
      ihave %Hbkl := ownSlice_len $$ Hbk
      ihave HI : (∃ (iv : w64) (e : cacheEntry),
          "i" ∷ i_ptr ↦ iv ∗ "elem" ∷ elem_ptr ↦ e ∗
          "%Hi" ∷ ⌜0 ≤ sint.Z iv ∧ sint.Z iv ≤ sint.Z ((CM !! key).getD slice.nil).len⌝ : IProp GF)
        $$ [i elem]
      · iexists W64 0, _
        iframe
        ipureintro; obtain ⟨_, h2⟩ := Hbkl; exact ⟨by decide, by simpa using h2⟩
      wp_for HI
      wp_if_destruct
      · have Hb' : 0 ≤ sint.Z iv ∧ sint.Z iv < sint.Z ((CM !! key).getD slice.nil).len := ⟨Hi.1, Hif⟩
        simp only [Hb', _root_.and_self, ↓reduceIte]
        list_elem bces (sint.nat iv) as ce
        wp_apply wp_load_slice_index _ (sint.Z iv) bces DFrac.discard ce Hi.1 $$ [Hbk] as -
        · iframe Hbk; ipureintro; exact Hce_lookup
        ihave #Hce := BigSepL.bigSepL_lookup (Φ := fun _ ce => cacheEntryOk S np (cacheP h.length cache) ce)
          Hce_lookup $$ Hbces
        unfold cacheEntryOk
        icases Hce with ⟨%ws', %t'', %k', #Hws', #Ht'', %HP⟩
        rw [method_unfold (t := go.GoType.PointerType bitset.ty) (m := go!"equal")]
        wp_call
        wp_auto
        wp_apply wp_equal $$ [$Hlin $Hws'] as ⟨Hlin, -⟩
        by_cases hw : bsSet ws co.id' = ws'
        · subst hw
          simp only [_root_.decide_true]
          wp_auto_lc 1
          unfold isEqHash equalSpec
          icases Heh with ⟨-, #Heq, -⟩
          imod shared_acc S np k' ce.state' t'' $$ [$Ht'' $Htok $Hlc1] with ⟨Hrep, Hclose⟩
          wp_apply Heq $$ %(k + 1) %k' %nsv %ce.state' %t' %t'' [$Hpost $Hrep] as %b ⟨Hpost, Hrep, %Hb⟩
          imod Hclose $$ Hrep with Htok
          cases b
          · wp_auto
            wp_for_post
            iframe
            iexists iv + W64 1, _
            iframe
            ipureintro; constructor <;> word
          · -- a cached configuration: clear the bit again
            wp_auto
            rw [method_unfold (t := go.GoType.PointerType bitset.ty) (m := go!"clear")]
            wp_call
            wp_auto
            have hyb' : uint.nat co.id' / 64 < (bsSet ws co.id').length := by
              rw [bsSet_length]; exact hyb
            wp_apply wp_clear lsl (bsSet ws co.id') co.id' hyb' $$ [Hlin] as Hlin
            · iframe
            rw [bsClear_bsSet ws co.id' hyb (by rw [hws2, hyw]; simpa using hyB)]
            wp_for_post
            iapply HΦ
            iframe
            ileft
            iframe
            isplitr
            · ipureintro; rfl
            isplitl [Hcm HB]
            · iunfold cacheOwn; iexists CM; iframe
            iright; iright
            ipureintro
            obtain ⟨c', hc', h1, h2⟩ := HP
            refine ⟨t', rfl, c', hc', fun i => ?_, by rw [h2, Hb rfl]⟩
            rw [h1 i, hbits1 i]
            simp only [decide_eq_true_eq]
            exact ⟨fun h' => h'.2, fun hi => ⟨hidsn i hi, hi⟩⟩
        · simp only [hw, _root_.decide_false]
          wp_auto
          wp_for_post
          iframe
          iexists iv + W64 1, _
          iframe
          ipureintro; constructor <;> word
      · -- the loop's end: a miss
        lift_tail
    · -- no bucket: insert
      lift_tail

end proof

end porcupine
end EtcdGrove
end Perennial
