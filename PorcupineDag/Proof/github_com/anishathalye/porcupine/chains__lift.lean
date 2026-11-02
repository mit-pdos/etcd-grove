/- Lean-first (no Rocq counterpart).

`(*chains).lift(ctx, model, consistency, oldState, stack, cache, serialized, liftFrom)` (dag.go,
PR #46): the frontier loop from `liftFrom` down, with `Bad` at the cursor (or the context done)
moving down past each candidate that could not be lifted (`DagTheory.bad_down`, the step refused
`succBad_of_none` or cached `succBad_of_cached`). On a success at position `q` (client `i`, head
`y`): the frame pushed, `computeFirstUnk(i)`, `removeFromFrontier(i)`, `nDeps[i]` recounted
(`cnt`), `addToFrontier(i)` if it is `0`, then the loop over `j` (`LiftInv`, `LiftLemmas.lean`):
the chains' invariant at `y :: ids fs`, the frontier its candidate list; `struct_push`, `bad_push`.
-/
module

public import PorcupineDag.Spec.github_com.anishathalye.porcupine.chains__lift
public import PorcupineDag.Spec.github_com.anishathalye.porcupine.client__lift
public import PorcupineDag.Spec.github_com.anishathalye.porcupine.chains__computeFirstUnk
public import PorcupineDag.Spec.github_com.anishathalye.porcupine.chains__removeFromFrontier
public import PorcupineDag.Spec.github_com.anishathalye.porcupine.chains__addToFrontier
public import PorcupineDag.Proof.github_com.anishathalye.porcupine.SearchLemmas
public import PorcupineDag.Proof.github_com.anishathalye.porcupine.LiftLemmas

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

theorem chains.lift.wp_proof
    (wp_client_lift : client.lift.spec (GF := GF) (hG := hG))
    (wp_computeFirstUnk : chains.computeFirstUnk.spec (GF := GF) (hG := hG))
    (wp_removeFromFrontier : chains.removeFromFrontier.spec (GF := GF) (hG := hG))
    (wp_addToFrontier : chains.addToFrontier.spec (GF := GF) (hG := hG)) :
    chains.lift.spec (GF := GF) (hG := hG) := by
  intro σ S m ctx ctxd cons np h cs ch stp lin_ptr cm fs fr cache sv s lf
    hok hwf halloc hst hinc
  wp_start as ⟨#Hctx, #Hm, #Hcons, #Hio, Hs, #Hsv, Htok, #Hbad⟩
  have hcs : (cs.length : Int) ≤ 2 ^ 45 := by
    have := halloc; unfold AllocOk maxAllocBytes at this
    have hm : (cs.length : Int) * 1 ≤ cs.length * ((max h.length 6 : Nat) : Int) :=
      Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
    omega
  have hcall : CallLeRet h := hwf.2
  wp_auto
  -- the frontier loop
  ihave HI : (∃ (iv : w64),
      "idx" ∷ idx_ptr ↦ iv ∗ "Hs" ∷ searchOwn S np h cs ch stp lin_ptr cm fs fr cache ∗
      "Htok" ∷ NonAtomicInvariant.own np ⊤ ∗
      "#Hbad" ∷ (⌜Bad S.M h (Before h cs) fs s fr (sint.Z iv) cache⌝ ∨ □ ctxd.PDone) ∗
      "%Hiv" ∷ ⌜-1 ≤ sint.Z iv ∧ sint.Z iv < fr.length⌝ : IProp GF) $$ [idx Hs Htok]
  · iexists lf
    iframe
    iframe Hbad
    ipureintro; exact ⟨hst.2.2.2.1, hst.2.2.2.2⟩
  wp_for HI
  wp_if_destruct
  · -- the body: the candidate at position `idx`
    have hiv0 : 0 ≤ sint.Z iv := by have := Hif; rw [show sint.Z (W64 0) = 0 from rfl] at this; exact this
    obtain ⟨q, hq⟩ : ∃ q : Nat, sint.Z iv = q := ⟨(sint.Z iv).toNat, by omega⟩
    iunfold searchOwn at Hs
    icases Hs with ⟨%st, %ssl, %ses, %lsl, %ws, Hch, %Hci, Hstk, Hstack, Hscap, #Hses, Hlinp, Hlin, %Hws,
      Hcache⟩
    simp only [named]
    obtain ⟨Hci, Hfr⟩ := Hci
    obtain ⟨Hws1, Hws2⟩ := Hws
    have hqf : q < st.frontier.length := by
      have := Hiv.2; rw [hq, ← Hfr] at this; unfold frOf at this; simpa using this
    obtain ⟨i, Hi_lookup⟩ : ∃ i, st.frontier[q]? = some i := ⟨_, List.getElem?_eq_getElem hqf⟩
    have hlc : LiftCtx h cs st (ids fs) i (hdOp cs st i) := by
      have hfi : i ∈ st.frontier := List.mem_of_getElem? Hi_lookup
      have := Hci.2.2.2.2.2.2.2.2.2.1 i hfi
      exact ⟨hok, hcall, Hci, this.1, this.2, rfl, hfi⟩
    have hil := hlc.2.2.2.1
    have hiz : sint.Z (W64 (i : Int)) = (i : Int) := by have := hil; word
    -- `i := ch.frontier[idx]`
    icases chainsOwn_cl ch h cs st $$ Hch with ⟨%cl, Hch⟩
    iunfold chainsOwnCl at Hch
    icases Hch with ⟨%chV, Hchp, %Hcl, Hr⟩
    icases chainsRepr_frontier chV h cs st $$ Hr with ⟨Hfrs, Hrback⟩
    ihave %Hfrl := ownSlice_len $$ Hfrs
    wp_auto
    rw [hq]
    have hbq : 0 ≤ (q : Int) ∧ (q : Int) < sint.Z chV.frontier'.len := by
      obtain ⟨h1, h2⟩ := Hfrl; simp only [List.length_map] at h1; rw [snat_eq] at h1; omega
    simp only [hbq, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index chV.frontier' (q : Int) _ _ (W64 (i : Int)) (by omega) $$ [Hfrs] as Hfrs
    · iframe; ipureintro; simp [Hi_lookup]
    ihave Hr := Hrback $$ Hfrs
    -- client `i`
    icases chainsRepr_acc chV h cs st i hil $$ Hr with ⟨%Hlen, %cv, He, Hc, Hback⟩
    iunfold clientOwn at Hc
    icases Hc with ⟨%Hcv, %cos, Hcos, %Hcok, Hfus⟩
    obtain ⟨Hcv1, Hcv2, Hcv3⟩ := Hcv
    ihave %Hcosl := ownSlice_len $$ Hcos
    have hbi : 0 ≤ (i : Int) ∧ (i : Int) < sint.Z chV.clients'.len := by omega
    repeat ((try simp only [hiz, hbi, _root_.and_self, ↓reduceIte]); wp_auto)
    -- its head operation `y`
    have hk0l : st.head i < cos.length := by rw [Hcok.1]; exact hlc.2.2.2.2.1
    obtain ⟨co, Hco⟩ : ∃ co, cos[st.head i]? = some co := ⟨_, List.getElem?_eq_getElem hk0l⟩
    obtain ⟨y', o, hy', ho, hcoid, hin, hout, -, -, -⟩ := Hcok.2 _ co Hco
    have hyy : y' = hdOp cs st i := by
      have := hlc.yget; rw [hy'] at this; exact Option.some.inj this
    subst hyy
    have hbk : 0 ≤ sint.Z cv.head' ∧ sint.Z cv.head' < sint.Z cv.cltOps'.len := by
      obtain ⟨h1, h2⟩ := Hcosl; rw [snat_eq] at h1; omega
    icases ownSlice_elem_acc (sint.Z cv.head') co _ _ cos hbk.1 (by rw [Hcv2]; simpa using Hco) $$ Hcos
      with ⟨Hco, Hcos⟩
    repeat ((try simp only [hiz, hbi, hbk, _root_.and_self, ↓reduceIte]); wp_auto)
    ihave Hcos := Hcos $$ %co Hco
    have hset : cos.set (sint.Z cv.head').toNat co = cos := by
      rw [Hcv2]; simp only [Int.toNat_natCast]
      obtain ⟨hl, he⟩ := List.getElem?_eq_some_iff.mp Hco
      rw [← he]; exact List.set_getElem_self hl
    rw [hset]
    -- `ch.clients[i].lift(...)`
    have hcand := hlc.cand
    have hnd : (ids fs).Nodup := framesStruct_nodup hst.2.1
    have hfsl : fs.length < h.length := by
      have hsub : hdOp cs st i :: ids fs ⊆ List.range h.length := by
        intro x hx'; rcases List.mem_cons.mp hx' with rfl | hx'
        · exact List.mem_range.mpr hlc.ylt
        · exact List.mem_range.mpr (Hci.2.2.2.2.2.1 x hx')
      have := List.Nodup.length_le_of_subset (List.nodup_cons.mpr ⟨hcand.2.1, hnd⟩) hsub
      simp [ids] at this; omega
    iunfold histIoOk at Hio
    ihave #Hioy := BigSepL.bigSepL_lookup (Φ := fun _ o => S.ioOk o.val.1 o.val.2) ho $$ Hio
    wp_apply wp_client_lift σ S m ctx ctxd cons np h _ cv cos (DFrac.own 1) co (hdOp cs st i) o (ids fs)
      fs.length sv s cm lin_ptr lsl ws cache hbk.1 (by rw [snat_eq, Hcv2]; simpa using Hco) hcoid ho hin hout
      hcand.2.1 Hci.2.2.2.2.2.1 hlc.ylt (by have := hwf.1; omega) hwf.1 Hws1 Hws2
      $$ [$Hctx $Hm $Hcons $Hioy $He $Hcos $Hsv $Htok $Hcache $Hlinp $Hlin] as %nsv %ok ⟨Hcos, Htok, Hlinp, Hres⟩
    have hfrq : fr[q]? = some (hdOp cs st i) := by
      rw [← Hfr]; unfold frOf; simp [Hi_lookup]
    icases Hres with (⟨%Hok, He, Hcache, Hlin, #Hwhy⟩ |
      ⟨%Hok, %t', %ws', %Hst', He, Hcache, Hlin, %Hws', #Hnsv⟩)
    · -- not lifted: the cursor moves down
      subst Hok
      wp_auto
      ihave Hr := Hback $$ %st %cv [] He [Hcos Hfus]
      · ipureintro; exact ⟨fun _ _ => ⟨rfl, rfl, rfl, rfl⟩, rfl⟩
      · iunfold clientOwn
        isplitr
        · ipureintro; exact ⟨Hcv1, Hcv2, Hcv3⟩
        iexists cos; iframe; ipureintro; exact Hcok
      wp_for_post
      iframe
      isplitl [Hchp Hr Hstk Hstack Hscap Hlinp Hlin Hcache]
      · iunfold searchOwn
        iexists st, ssl, ses, lsl, ws
        simp only [named]
        iframe Hses
        isplitl [Hchp Hr]
        · iapply chainsOwnCl_weaken ch cl h cs st
          iapply chainsOwnCl_fold ch chV cl h cs st Hcl
          iframe
        iframe
        ipureintro; exact ⟨⟨Hci, Hfr⟩, Hws1, Hws2⟩
      have hiv1 : sint.Z (iv - W64 1) = (q : Int) - 1 := by
        have := Hiv.2; have := hiv0; rw [← hq]; word
      rw [hiv1]
      isplitr
      · icases Hbad with (%Hb | #HPD)
        · icases Hwhy with (%Hnone | #HPD | %Hcached)
          · ileft; ipureintro
            refine bad_down (hq ▸ Hb) hfrq (succBad_of_none fun o' ho' => ?_)
            rw [ho] at ho'; cases ho'; exact Hnone
          · iright; iexact HPD
          · ileft; ipureintro
            refine bad_down (hq ▸ Hb) hfrq (succBad_of_cached Hb.2.2 hcand.2.1 fun o' t'' ho' hst'' => ?_)
            rw [ho] at ho'; cases ho'
            obtain ⟨t3, h3, hc⟩ := Hcached
            rw [hst''] at h3; cases h3; exact hc
        · iright; iexact HPD
      ipureintro; constructor <;> omega
    · -- lifted
      subst Hok
      -- `*stack = append(*stack, e)`
      wp_pures
      wp_load
      wp_load
      wp_pures
      wp_load
      wp_pures
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %lite ⟨Hlite, -⟩
      wp_apply wp_slice_append $$ [Hstack Hscap Hlite] as %ssl' ⟨Hstack, Hscap, -⟩
      · iframe Hstack Hscap Hlite
      wp_auto
      -- the chains at the new heads
      have hhl : (chain cs i).length < 2 ^ 60 := by
        have := chain_length_le hok i; have := hwf.1; omega
      obtain ⟨st1, hst1⟩ : ∃ st1 : ChSt,
          st1 = ChSt.mk (st.heads.set i (st.head i + 1)) st.nDeps st.frontier st.vis st.fu := ⟨_, rfl⟩
      have hhd1 : sint.Z (cv.head' + W64 1) = (st1.head i : Int) := by
        have h1 := hlc.2.2.2.2.1
        have h2 : st1.head i = st.head i + 1 := by
          unfold ChSt.head; rw [hst1]; simp only; rw [← ChSt.head, hlc.H'_getD, if_pos rfl]
        rw [h2]; push_cast; rw [← Hcv2]; have := Hcv2; word
      ihave Hr := Hback $$ %st1 %_ [] He [Hcos Hfus]
      · ipureintro
        refine ⟨fun c' hc' => ⟨?_, by rw [hst1], by rw [hst1], by rw [hst1]⟩, by rw [hst1]⟩
        unfold ChSt.head; rw [hst1]; simp only; rw [← ChSt.head, hlc.H'_getD, if_neg hc']
      · iunfold clientOwn
        isplitr
        · ipureintro
          refine ⟨Hcv1, hhd1, by rw [hst1, Hcv3]⟩
        iexists cos
        rw [hst1]
        iframe
        ipureintro; exact Hcok
      ihave Hch := chainsOwnCl_fold ch chV cl h cs st1 Hcl $$ [Hchp Hr]
      · iframe
      -- `computeFirstUnk(i)`
      have hinw : sint.nat (W64 (i : Int)) = i := by rw [snat_eq, hiz]; simp
      have hsh1 : ShapeOk cs st1 := by
        obtain ⟨h1, h2, h3, h4, h5⟩ := Hci.1
        rw [hst1]; exact ⟨by simp [h1], h2, h3, h4, h5⟩
      have hvis1 : 0 < st1.head i → st1.head i < (chain cs i).length →
          st1.visAt i (st1.head i - 1) = true := by
        intro _ _
        have h2 : st1.head i = st.head i + 1 := by
          unfold ChSt.head; rw [hst1]; simp only; rw [← ChSt.head, hlc.H'_getD, if_pos rfl]
        rw [h2, Nat.add_sub_cancel, hst1]
        exact Hci.2.2.2.2.2.2.2.1 i (st.head i) hlc.2.2.2.2.1 (Nat.le_refl _)
      wp_apply wp_computeFirstUnk ch cl h cs st1 (W64 (i : Int)) cons hok hwf hsh1
        (by rw [hst1]; exact Hci.2.2.2.2.2.2.1) (by rw [hst1]; exact hlc.push.2) (by omega)
        (by rw [hinw]; exact hil) (by rw [hinw]; exact hvis1) $$ [Hch] as ⟨%st2, Hch, %Hst2⟩
      · iframe; iframe Hcons
      rw [hinw] at Hst2
      obtain ⟨h2h, h2n, h2f, h2sh, h2fu, h2vis⟩ := Hst2
      have hlc2 : LiftCtx2 h cs st st2 (ids fs) i (hdOp cs st i) := by
        refine ⟨hlc, by rw [h2h, hst1], by rw [h2n, hst1], h2sh, h2fu, fun c' k => ?_⟩
        rw [h2vis c' k, hst1]; rfl
      -- `removeFromFrontier(i)`
      wp_apply wp_removeFromFrontier ch cl h cs st2 (W64 (i : Int)) (by omega)
        (fun v hv => by rw [h2f, hst1] at hv; exact (Hci.2.2.2.2.2.2.2.2.2.1 v hv).1) (by omega)
        $$ [Hch] as Hch
      · iframe
      rw [hinw]
      obtain ⟨st3, hst3⟩ : ∃ st3 : ChSt,
          st3 = ChSt.mk st2.heads st2.nDeps (st2.frontier.erase i) st2.vis st2.fu := ⟨_, rfl⟩
      rw [show ({ st2 with frontier := st2.frontier.erase i } : ChSt) = st3 by rw [hst3]]
      have h3head : ∀ d, st3.head d = st2.head d := fun d => by unfold ChSt.head; rw [hst3]
      have hhi2 := hlc2.head2_i
      -- `if ch.clients[i].head < len(ch.clients[i].cltOps) { ... }`, joined at the `j`-loop's start
      wp_join iprop(∃ stc : ChSt, ch_ptr ↦ ch ∗ i_ptr ↦ W64 (i : Int) ∗ consistency_ptr ↦ cons ∗
          chainsOwnCl ch cl h cs stc ∗ ⌜LiftInv h cs st st2 i 0 stc⌝) at next
        with [Hch ch i consistency] as ⟨%stc, ch, i, consistency, Hch, %Hinv0⟩
      · iunfold chainsOwnCl at Hch
        icases Hch with ⟨%chV2, Hchp, %Hcl2, Hr⟩
        icases chainsRepr_open chV2 h cs st3 i hil $$ Hr with ⟨%cvs, %cvi, %Hcvs, He, Hc, Hrest⟩
        obtain ⟨Hcvi, Hcvsl, Hlen2⟩ := Hcvs
        iunfold clientOwn at Hc
        icases Hc with ⟨%Hcv, %cos3, Hcos3, %Hcok3, Hfus3⟩
        obtain ⟨Hcvi1, Hcvi2, Hcvi3⟩ := Hcv
        ihave %Hcos3l := ownSlice_len $$ Hcos3
        have hbi2 : 0 ≤ (i : Int) ∧ (i : Int) < sint.Z chV2.clients'.len := by omega
        repeat ((try simp only [hiz, hbi2, _root_.and_self, ↓reduceIte]); wp_auto)
        have hk2 : sint.Z cvi.head' = ((st.head i + 1 : Nat) : Int) := by
          rw [Hcvi2, h3head, hhi2]
        have hcos3 : cos3.length = (chain cs i).length := Hcok3.1
        have h3n : st3.nDeps = st.nDeps := by rw [hst3]; exact hlc2.2.2.1
        have h3fr : st3.frontier = st.frontier.erase i := by rw [hst3]; simp only; rw [h2f, hst1]
        wp_if_destruct
        · -- client `i` unfinished: recount its `nDeps`
          have hk2l : st.head i + 1 < (chain cs i).length := by
            have := Hcos3l; rw [snat_eq] at this; rw [hk2] at Hif; omega
          obtain ⟨co2, Hco2⟩ : ∃ co2, cos3[st.head i + 1]? = some co2 :=
            ⟨_, List.getElem?_eq_getElem (by omega)⟩
          have hbk2 : 0 ≤ sint.Z cvi.head' ∧ sint.Z cvi.head' < sint.Z cvi.cltOps'.len := by
            constructor
            · rw [hk2]; omega
            · exact Hif
          repeat ((try simp only [hiz, hbi2, hbk2, _root_.and_self, ↓reduceIte]); wp_auto)
          simp only [hbk2, _root_.and_self, ↓reduceIte]
          wp_apply wp_load_slice_index cvi.cltOps' (sint.Z cvi.head') cos3 _ co2 hbk2.1 $$ [Hcos3] as Hcos3
          · iframe; ipureintro; rw [hk2]; simpa using Hco2
          repeat ((try simp only [hiz, hbi2, hbk2, _root_.and_self, ↓reduceIte]); wp_auto)
          -- `nDeps[i] = 0`, then the recount loop with client `i` kept out of the chains
          have hk2v : st2.visAt i (st.head i + 1) = true := by
            rw [h2vis]; apply Bool.or_eq_true_iff.mpr; right; apply decide_eq_true
            refine ⟨rfl, ?_, hk2l⟩
            unfold ChSt.head; rw [hst1]; simp only; rw [← ChSt.head, hlc.H'_getD, if_pos rfl]
          have hk2s : st2.head i = st.head i + 1 := hhi2
          obtain ⟨fu2, Hfu2⟩ : ∃ fu2, fu2 = st3.fuAt i (st.head i + 1) := ⟨_, rfl⟩
          have hfu2l : fu2.length = cs.length := by
            rw [Hfu2]; exact (h2sh.2.2.2.2 i (st.head i + 1) hk2l).2.2 ▸ (by unfold ChSt.fuAt; rw [hst3])
          have hfu2v : ∀ d, d < cs.length → d ≠ i → sint.Z (fu2.getD d 0) = FUe h cs i d (st.head i + 1) := by
            intro d hd hdi
            have := h2fu i (st.head i + 1) hk2v d hd hdi
            rw [Hfu2]; unfold ChSt.fuAt at this ⊢; rw [hst3]; exact this
          icases BigSepL.bigSepL_lookup_acc Hco2 $$ Hfus3 with ⟨Hfu, Hfus3⟩
          rw [← Hfu2]
          ihave %Hful := ownSlice_len $$ Hfu
          ihave HK : (∃ (kv : w64), "k" ∷ k_ptr ↦ kv ∗
              "He" ∷ sliceIndexRef client (i : Int) chV2.clients' ↦
                (⟨cvi.id', cvi.cltOps', cvi.head', W64 (cnt h cs st2.heads i (sint.nat kv) : Int)⟩ : client) ∗
              "%Hk" ∷ ⌜0 ≤ sint.Z kv ∧ sint.Z kv ≤ cs.length⌝ : IProp GF) $$ [k He]
          · iexists W64 0
            rw [show sint.nat (W64 0) = 0 from rfl, cnt_zero]
            iframe
            ipureintro; exact ⟨by decide, by word⟩
          wp_for HK
          obtain ⟨Hk1, Hk2⟩ := Hk
          have hw1 : ∀ n : Nat, (W64 ((n + 1 : Nat) : Int) : w64) = W64 (n : Int) + W64 1 := by
            intro n; push_cast; word
          wp_if_destruct
          · -- the recount's body
            have hkl : sint.nat kv < cs.length := by
              have := Hif
              rw [Hlen2] at this; rw [snat_eq]; omega
            have hk1 : sint.nat (kv + W64 1) = sint.nat kv + 1 := by
              rw [snat_eq, snat_eq]; have := hkl; rw [snat_eq] at this; word
            have hkv1 : 0 ≤ sint.Z (kv + W64 1) ∧ sint.Z (kv + W64 1) ≤ cs.length := by
              have := hkl; rw [snat_eq] at this
              have h1 : sint.Z (kv + W64 1) = sint.Z kv + 1 := by word
              omega
            wp_if_destruct
            · -- `k == i`
              wp_for_post
              iframe
              iexists W64 (i : Int) + W64 1
              rw [hk1, hinw, cnt_succ, if_neg (fun h0 => h0.1 rfl), Nat.add_zero]
              iframe
              ipureintro; exact hkv1
            · -- `k != i`: `opI.firstUnk[k] > ch.clients[k].head`
              obtain ⟨kn, hkn⟩ : ∃ kn, sint.nat kv = kn := ⟨_, rfl⟩
              rw [hkn] at hkl hk1
              rw [hkn]
              have hkz : sint.Z kv = (kn : Int) := by rw [← hkn, snat_eq]; omega
              have hki : kn ≠ i := by
                intro he; apply Hif; apply BitVec.eq_of_toInt_eq
                have := hiz; simp only [sint.Z] at this hkz; omega
              have hbf : 0 ≤ (kn : Int) ∧ (kn : Int) < sint.Z co2.firstUnk'.len := by
                have := Hful; rw [snat_eq, hfu2l] at this; omega
              repeat ((try simp only [hkz, hbf, _root_.and_self, ↓reduceIte]); wp_auto)
              simp only [hkz, hbf, _root_.and_self, ↓reduceIte]
              obtain ⟨fv, Hfv⟩ : ∃ fv, fu2[kn]? = some fv := ⟨_, List.getElem?_eq_getElem (by omega)⟩
              wp_apply wp_load_slice_index co2.firstUnk' (kn : Int) fu2 _ fv (by omega) $$ [Hfu] as Hfu
              · iframe; ipureintro; simpa using Hfv
              have hfv : sint.Z fv = FUe h cs i kn (st.head i + 1) := by
                have := hfu2v kn hkl hki
                rw [List.getD_eq_getElem?_getD, Hfv] at this; exact this
              -- client `k`'s head
              obtain ⟨cvk, Hcvk⟩ : ∃ cvk, cvs[kn]? = some cvk := ⟨_, List.getElem?_eq_getElem (by omega)⟩
              icases chainsRest_read chV2 h cs st3 i kn cvs cvk Hcvk hki $$ Hrest with ⟨Hek, Hck, Hrest⟩
              icases clientOwn_facts h cs st3 kn cvk $$ Hck with ⟨%Hck', Hck⟩
              have hbk' : 0 ≤ (kn : Int) ∧ (kn : Int) < sint.Z chV2.clients'.len := by omega
              repeat ((try simp only [hkz, hbk', _root_.and_self, ↓reduceIte]); wp_auto)
              ihave Hrest := Hrest $$ Hek Hck
              have hhk : sint.Z cvk.head' = (st2.head kn : Int) := by rw [Hck'.2.1, h3head]
              have htest : (sint.Z cvk.head' < sint.Z fv) ↔
                  st2.heads.getD kn 0 < FUe h cs i kn (st2.heads.getD i 0) := by
                rw [hhk, hfv]
                have : st2.heads.getD i 0 = st.head i + 1 := hk2s
                rw [this]
                exact ⟨fun h0 => by exact_mod_cast h0, fun h0 => by exact_mod_cast h0⟩
              have hil2 : st2.heads.getD i 0 < (chain cs i).length := by
                have : st2.heads.getD i 0 = st.head i + 1 := hk2s
                rw [this]; exact hk2l
              wp_if_destruct
              · -- `nDeps[i]++`
                repeat ((try simp only [hiz, hbi2, _root_.and_self, ↓reduceIte]); wp_auto)
                ihave He : (sliceIndexRef client (i : Int) chV2.clients' ↦
                  (⟨cvi.id', cvi.cltOps', cvi.head', W64 (cnt h cs st2.heads i kn : Int) + W64 1⟩ : client)
                  : IProp GF) $$ [He]
                · iexact He
                wp_for_post
                iframe
                iexists kv + W64 1
                rw [hk1, cnt_succ, if_pos ⟨hki, hil2, htest.mp Hif⟩, hw1]
                iframe
                ipureintro; exact hkv1
              · wp_for_post
                iframe
                iexists kv + W64 1
                rw [hk1, cnt_succ, if_neg (fun h0 => Hif (htest.mpr h0.2.2)), Nat.add_zero]
                iframe
                ipureintro; exact hkv1
          · -- the recount is done: `nDeps[i]` is `deps`
            have hkend : sint.nat kv = cs.length := by
              have hn : ¬ sint.Z kv < sint.Z chV2.clients'.len := by
                intro hlt; apply Hif; simp [hlt]
              rw [Hlen2] at hn; rw [snat_eq]; omega
            rw [hkend, cnt_deps]
            have hdl : deps h cs st2.heads i ≤ cs.length := deps_le
            have hdz : sint.Z (W64 (deps h cs st2.heads i : Int)) = (deps h cs st2.heads i : Int) := by
              have := hcs; word
            repeat ((try simp only [hiz, hbi2, _root_.and_self, ↓reduceIte]); wp_auto)
            -- client `i` back
            ihave Hfus3 := Hfus3 $$ %co2 Hfu
            have hset2 : cos3.set (st.head i + 1) co2 = cos3 := by
              obtain ⟨hl, he⟩ := List.getElem?_eq_some_iff.mp Hco2
              rw [← he]; exact List.set_getElem_self hl
            rw [hset2]
            ihave Hc : clientOwn h cs st3 i cvi $$ [Hcos3 Hfus3]
            · iunfold clientOwn
              isplitr
              · ipureintro; exact ⟨Hcvi1, Hcvi2, Hcvi3⟩
              iexists cos3; iframe; ipureintro; exact Hcok3
            obtain ⟨st4, hst4⟩ : ∃ st4 : ChSt, st4 = ChSt.mk st3.heads
                (st3.nDeps.set i (W64 (deps h cs st2.heads i : Int))) st3.frontier st3.vis st3.fu :=
              ⟨_, rfl⟩
            have hin3 : i < st3.nDeps.length := by rw [h3n, Hci.1.2.1]; exact hil
            have hhd4 : sint.Z cvi.head' = (st4.head i : Int) := by
              rw [Hcvi2]; unfold ChSt.head; rw [hst4]
            have hnd4 : (W64 (deps h cs st2.heads i : Int) : w64) = st4.nDeps.getD i 0 := by
              rw [hst4]; simp [List.getD_eq_getElem?_getD, List.getElem?_set_self hin3]
            ihave Hc := clientOwn_upd (st := st3) (st' := st4) h cs cvi
              ⟨cvi.id', cvi.cltOps', cvi.head', W64 (deps h cs st2.heads i : Int)⟩ rfl rfl hhd4 hnd4
              (by rw [hst4]) (by rw [hst4]) $$ Hc
            have hag4 : ∀ c, c ≠ i → ChAgree st3 st4 c := by
              intro c' hc'
              refine ⟨by unfold ChSt.head; rw [hst4], ?_, by rw [hst4], by rw [hst4]⟩
              rw [hst4]; simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hc')]
            ihave He : (sliceIndexRef client (i : Int) chV2.clients' ↦
                (⟨cvi.id', cvi.cltOps', cvi.head', W64 (deps h cs st2.heads i : Int)⟩ : client)
                : IProp GF) $$ [He]
            · iexact He
            ihave Hr := chainsRest_close chV2 h cs st3 st4 i cvs cvi _ Hcvi hag4 (by rw [hst4]) $$ [He Hc Hrest]
            · iframe
            ihave Hch := chainsOwnCl_fold ch chV2 cl h cs st4 Hcl2 $$ [Hchp Hr]
            · iframe
            have h4h : st4.heads = st2.heads := by rw [hst4, hst3]
            have h4v : st4.vis = st2.vis := by rw [hst4, hst3]
            have h4f : st4.fu = st2.fu := by rw [hst4, hst3]
            have h4n : st4.nDeps.length = st.nDeps.length := by rw [hst4]; simp only; rw [List.length_set, h3n]
            have h4i : sint.Z (st4.nDeps.getD i 0) = deps h cs st2.heads i := by
              rw [← hnd4]; exact hdz
            have h4o : ∀ d, d ≠ i → st4.nDeps.getD d 0 = st.nDeps.getD d 0 := by
              intro d hd; rw [← h3n]; exact (hag4 d hd).2.1
            have h4fr : st4.frontier = st.frontier.erase i := by rw [hst4]; exact h3fr
            obtain ⟨hsort4, hnot4, hmem4⟩ := hlc2.erase_facts h4h h4fr
            wp_if_destruct
            · -- no dependency: `addToFrontier(i)`
              have hd0 : deps h cs st2.heads i = 0 := by
                have := hdz; rw [Hif] at this; simp at this; omega
              obtain ⟨hah, hamem⟩ := hlc2.add_pre h4h hil (by rw [hhi2]; exact hk2l) hd0 hmem4
              wp_apply wp_addToFrontier ch cl h cs st4 (W64 (i : Int)) cons hok
                (hlc2.shape_of h4h h4v h4f h4n) (by omega) (by omega) (by rw [hinw]; exact hil)
                (by rw [hinw]; exact hah) (by rw [hinw]; exact hnot4) (by rw [hinw]; exact hamem) hsort4
                $$ [Hch] as ⟨%fr5, Hch, %Hfr5⟩
              · iframe; iframe Hcons
              rw [hinw] at Hfr5
              isplitl []
              · ipureintro; rfl
              iexists _
              iframe
              ipureintro
              refine hlc2.inv_init_add (stc := ChSt.mk st4.heads st4.nDeps fr5 st4.vis st4.fu)
                h4h h4v h4f h4n h4i h4o Hfr5.1 (fun x => by rw [Hfr5.2 x, h4fr]) ⟨by rw [hhi2]; exact hk2l, hd0⟩
            · -- `i` has a dependency
              isplitl []
              · ipureintro; first | rfl | trivial
              iexists st4
              iframe
              ipureintro
              refine hlc2.inv_init_erase h4h h4v h4f h4n (fun _ => h4i) h4o h4fr ?_
              rintro ⟨-, hd0⟩
              apply Hif; rw [hd0]; rfl
        · -- client `i` finished
          have hfin : ¬ st2.head i < (chain cs i).length := by
            rw [hhi2]; intro hlt; apply Hif
            have := Hcos3l; rw [snat_eq] at this; rw [hk2]; omega
          ihave Hc : clientOwn h cs st3 i cvi $$ [Hcos3 Hfus3]
          · iunfold clientOwn
            isplitr
            · ipureintro; exact ⟨Hcvi1, Hcvi2, Hcvi3⟩
            iexists cos3; iframe; ipureintro; exact Hcok3
          ihave Hr := chainsRest_close chV2 h cs st3 st3 i cvs cvi cvi Hcvi
            (fun _ _ => ⟨rfl, rfl, rfl, rfl⟩) rfl $$ [He Hc Hrest]
          · iframe
          isplitl []
          · itrivial
          iexists st3
          iframe
          isplitl [Hchp Hr]
          · iapply chainsOwnCl_fold ch chV2 cl h cs st3 Hcl2; iframe
          ipureintro
          refine hlc2.inv_init_erase (by rw [hst3]) (by rw [hst3]) (by rw [hst3])
            (by rw [h3n]) (fun h0 => absurd h0 hfin) (fun d _ => by rw [h3n]) h3fr
            (fun ⟨h0, _⟩ => hfin h0)
      -- the loop over `j`
      ihave HJ : (∃ (jv : w64) (stj : ChSt),
          "j" ∷ j_ptr ↦ jv ∗ "Hch" ∷ chainsOwnCl ch cl h cs stj ∗
          "%Hj" ∷ ⌜0 ≤ sint.Z jv ∧ sint.Z jv ≤ cs.length ∧
            LiftInv h cs st st2 i (sint.nat jv) stj⌝ : IProp GF) $$ [j Hch]
      · iexists W64 0, stc
        iframe
        ipureintro; exact ⟨by decide, by word, by rw [show sint.nat (W64 0) = 0 from rfl]; exact Hinv0⟩
      wp_for HJ
      obtain ⟨Hj1, Hj2, Hinv⟩ := Hj
      have hstj : ∀ d, stj.head d = st2.head d := fun d => by unfold ChSt.head; rw [Hinv.1]
      iunfold chainsOwnCl at Hch
      icases Hch with ⟨%chV4, Hchp, %Hcl4, Hr⟩
      icases chainsRepr_acc chV4 h cs stj i hil $$ Hr with ⟨%Hlen4, %cvx, Hex, Hcx, Hbackx⟩
      ihave Hr := Hbackx $$ %stj %cvx [] Hex Hcx
      · ipureintro; exact ⟨fun _ _ => ⟨rfl, rfl, rfl, rfl⟩, rfl⟩
      wp_auto
      wp_if_destruct
      · -- the body
        have hjl : sint.nat jv < cs.length := by
          have : sint.Z jv < sint.Z chV4.clients'.len := by have := go.intoVal_inj Hif; simpa using this
          rw [Hlen4] at this; rw [snat_eq]; omega
        have hjv1 : 0 ≤ sint.Z (jv + W64 1) ∧ sint.Z (jv + W64 1) ≤ cs.length := by
          have := hjl; rw [snat_eq] at this
          have h1 : sint.Z (jv + W64 1) = sint.Z jv + 1 := by word
          omega
        have hj1 : sint.nat (jv + W64 1) = sint.nat jv + 1 := by
          rw [snat_eq, snat_eq]; have := hjl; rw [snat_eq] at this; word
        wp_if_destruct
        · -- `j == i`
          wp_for_post
          iframe
          iexists W64 (i : Int) + W64 1, stj
          iframe
          isplitl [Hchp Hr]
          · iapply chainsOwnCl_fold ch chV4 _ h cs stj Hcl4; iframe
          ipureintro
          refine ⟨hjv1.1, hjv1.2, ?_⟩
          rw [hj1]
          exact hlc2.inv_skip Hinv (Or.inl hinw)
        · -- `j != i`: client `j`'s head
          obtain ⟨jn, hjn⟩ : ∃ jn, sint.nat jv = jn := ⟨_, rfl⟩
          rw [hjn] at hjl hj1 Hinv
          have hjz : sint.Z jv = (jn : Int) := by rw [← hjn, snat_eq]; omega
          have hji : jn ≠ i := by
            intro he; apply Hif; apply BitVec.eq_of_toInt_eq
            have := hiz; simp only [sint.Z] at this hjz; omega
          icases chainsRepr_acc chV4 h cs stj jn hjl $$ Hr with ⟨-, %cvj, Hej, Hcj, Hbackj⟩
          iunfold clientOwn at Hcj
          icases Hcj with ⟨%Hcj, %cosj, Hcosj, %Hcokj, Hfusj⟩
          obtain ⟨Hcj1, Hcj2, Hcj3⟩ := Hcj
          ihave %Hcosjl := ownSlice_len $$ Hcosj
          have hbj : 0 ≤ (jn : Int) ∧ (jn : Int) < sint.Z chV4.clients'.len := by omega
          have hbj4 : (jn : Int) < sint.Z chV4.clients'.len := by omega
          repeat ((try simp only [hjz, hbj, hbj4, _root_.and_self, ↓reduceIte, Int.natCast_nonneg]); wp_auto)
          have hcosjl : cosj.length = (chain cs jn).length := Hcokj.1
          have hk0 : sint.Z cvj.head' = ((st2.head jn : Nat) : Int) := by rw [Hcj2, hstj]
          wp_if_destruct
          · -- client `j` unfinished: its head's `firstUnk[i]`
            obtain ⟨k0, hk0n⟩ : ∃ k0, st2.head jn = k0 := ⟨_, rfl⟩
            rw [hk0n] at hk0
            have hk0l : k0 < cosj.length := by
              have := Hcosjl; rw [snat_eq] at this; omega
            obtain ⟨co, Hco⟩ : ∃ co, cosj[k0]? = some co := ⟨_, List.getElem?_eq_getElem hk0l⟩
            icases ownSlice_elem_acc (sint.Z cvj.head') co _ _ cosj (by omega)
              (by rw [hk0]; simpa using Hco) $$ Hcosj with ⟨Hco, Hcosj⟩
            icases BigSepL.bigSepL_lookup_acc Hco $$ Hfusj with ⟨Hfu, Hfusj⟩
            ihave %Hful := ownSlice_len $$ Hfu
            have hshj : ShapeOk cs stj := hlc2.shape_of Hinv.1 Hinv.2.1 Hinv.2.2.1 Hinv.2.2.2.1
            have hful : (stj.fuAt jn k0).length = cs.length := (hshj.2.2.2.2 jn k0 (by omega)).2.2
            have hbk : 0 ≤ sint.Z cvj.head' ∧ sint.Z cvj.head' < sint.Z cvj.cltOps'.len := by omega
            have hbc : 0 ≤ (i : Int) ∧ (i : Int) < sint.Z co.firstUnk'.len := by
              have := Hful; rw [snat_eq] at this; omega
            repeat ((try simp only [hjz, hbj, hbj4, hbk, hiz, hbc, _root_.and_self, ↓reduceIte,
              Int.natCast_nonneg]); wp_auto)
            simp only [hiz, hbc, _root_.and_self, ↓reduceIte]
            obtain ⟨fv, Hfv⟩ : ∃ fv, (stj.fuAt jn k0)[i]? = some fv :=
              ⟨_, List.getElem?_eq_getElem (by omega)⟩
            wp_apply wp_load_slice_index co.firstUnk' (i : Int) (stj.fuAt jn k0) _ fv (by omega) $$ [Hfu] as Hfu
            · iframe; ipureintro; simpa using Hfv
            ihave Hcosj := Hcosj $$ %co Hco
            ihave Hfusj := Hfusj $$ %co Hfu
            have hsetj : cosj.set k0 co = cosj := by
              obtain ⟨hl, he⟩ := List.getElem?_eq_some_iff.mp Hco
              rw [← he]; exact List.set_getElem_self hl
            rw [show (sint.Z cvj.head').toNat = k0 by omega, hsetj]
            ihave Hr := Hbackj $$ %stj %cvj [] Hej [Hcosj Hfusj]
            · ipureintro; exact ⟨fun _ _ => ⟨rfl, rfl, rfl, rfl⟩, rfl⟩
            · iunfold clientOwn
              isplitr
              · ipureintro; exact ⟨Hcj1, Hcj2, Hcj3⟩
              iexists cosj; iframe; ipureintro; exact Hcokj
            -- client `i`'s head
            icases chainsRepr_acc chV4 h cs stj i hil $$ Hr with ⟨-, %cvc, Hec, Hcc, Hbackc⟩
            icases clientOwn_facts h cs stj i cvc $$ Hcc with ⟨%Hcc', Hcc⟩
            have hbi4 : 0 ≤ (i : Int) ∧ (i : Int) < sint.Z chV4.clients'.len := by omega
            have hbi4' : (i : Int) < sint.Z chV4.clients'.len := by omega
            simp only [hiz, hbi4, hbi4', _root_.and_self, ↓reduceIte, Int.natCast_nonneg]
            wp_auto
            ihave Hr := Hbackc $$ %stj %cvc [] Hec Hcc
            · ipureintro; exact ⟨fun _ _ => ⟨rfl, rfl, rfl, rfl⟩, rfl⟩
            have hvis : stj.visAt jn k0 = true := by
              have h1 := h2vis jn k0
              have h2 := Hci.2.2.2.2.2.2.2.1 jn k0 (by omega)
                (by rw [← hk0n, hlc2.head2_ne hji]; exact Nat.le_refl _)
              unfold ChSt.visAt at h1 h2 ⊢
              rw [Hinv.2.1, h1, hst1]; simp only; rw [h2]
            have hfv : sint.Z fv = FUe h cs jn i k0 := by
              have := h2fu jn k0 (by unfold ChSt.visAt at hvis ⊢; rw [Hinv.2.1] at hvis; exact hvis)
                i hil (Ne.symm hji)
              unfold ChSt.fuAt at this Hfv
              rw [Hinv.2.2.1] at Hfv
              rw [List.getD_eq_getElem?_getD, Hfv] at this
              exact this
            have hhc : sint.Z cvc.head' = ((st2.head i : Nat) : Int) := by rw [Hcc'.2.1, hstj]
            have hFle : FUe h cs jn i k0 ≤ (chain cs i).length := fue_le
            have hcll : (chain cs i).length < 2 ^ 60 := hhl
            have htest : fv = cvc.head' ↔ FUe h cs jn i k0 = st2.head i := by
              constructor
              · intro he; rw [he, hhc] at hfv; omega
              · intro he; apply BitVec.eq_of_toInt_eq
                simp only [sint.Z] at hfv hhc ⊢
                omega
            wp_if_destruct
            · -- the test holds: `nDeps[j]--`, and `addToFrontier(j)` at `0`
              have hfu' : FUe h cs jn i (st2.head jn) = st2.head i := by rw [hk0n]; exact htest.mp rfl
              have hjh : st2.head jn < (chain cs jn).length := by rw [hk0n, ← hcosjl]; exact hk0l
              obtain ⟨hdec, hjnot⟩ := hlc2.hit_val Hinv hji hjl hjh hfu' (by omega)
              icases chainsRepr_acc chV4 h cs stj jn hjl $$ Hr with ⟨-, %cvj2, Hej, Hcj, Hbackj⟩
              icases clientOwn_facts h cs stj jn cvj2 $$ Hcj with ⟨%Hcj', Hcj⟩
              repeat ((try simp only [hjz, hbj, hbj4, _root_.and_self, ↓reduceIte, Int.natCast_nonneg]); wp_auto)
              obtain ⟨nd, hnd⟩ : ∃ nd, stj.nDeps.getD jn 0 = nd := ⟨_, rfl⟩
              have hcvnd : cvj2.nDeps' = nd := by rw [Hcj'.2.2, hnd]
              rw [hnd] at hdec
              obtain ⟨stj', hstj'⟩ : ∃ stj' : ChSt, stj' = ChSt.mk stj.heads (stj.nDeps.set jn (nd - W64 1))
                  stj.frontier stj.vis stj.fu := ⟨_, rfl⟩
              have hjn' : jn < stj.nDeps.length := by rw [Hinv.2.2.2.1, Hci.1.2.1]; exact hjl
              have hndj : cvj2.nDeps' - W64 1 = stj'.nDeps.getD jn 0 := by
                rw [hstj', hcvnd]; simp [List.getD_eq_getElem?_getD, List.getElem?_set_self hjn']
              ihave Hc := clientOwn_upd (st := stj) (st' := stj') h cs cvj2
                ⟨cvj2.id', cvj2.cltOps', cvj2.head', cvj2.nDeps' - W64 1⟩ rfl rfl
                (by rw [Hcj'.2.1]; unfold ChSt.head; rw [hstj']) hndj (by rw [hstj']) (by rw [hstj']) $$ Hcj
              ihave Hej : (sliceIndexRef client (jn : Int) chV4.clients' ↦
                  (⟨cvj2.id', cvj2.cltOps', cvj2.head', cvj2.nDeps' - W64 1⟩ : client) : IProp GF) $$ [Hej]
              · iexact Hej
              ihave Hr := Hbackj $$ %stj' %_ [] Hej Hc
              · ipureintro
                refine ⟨fun c' hc' => ⟨by unfold ChSt.head; rw [hstj'], ?_, by rw [hstj'], by rw [hstj']⟩,
                  by rw [hstj']⟩
                rw [hstj']; simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hc')]
              ihave Hch := chainsOwnCl_fold ch chV4 cl h cs stj' Hcl4 $$ [Hchp Hr]
              · iframe
              rw [hcvnd]
              have hh' : stj'.heads = stj.heads := by rw [hstj']
              have hv' : stj'.vis = stj.vis := by rw [hstj']
              have hf' : stj'.fu = stj.fu := by rw [hstj']
              have hn' : stj'.nDeps = stj.nDeps.set jn (stj.nDeps.getD jn 0 - W64 1) := by rw [hstj', hnd]
              have hfrj : frOf cs stj' = frOf cs stj := by unfold frOf hdOp ChSt.head; rw [hstj']
              wp_if_destruct
              · -- `nDeps[j]` reached `0`: `addToFrontier(j)`
                have hd0 : deps h cs st2.heads jn = 0 := by rw [Hif] at hdec; simp at hdec; omega
                have hstjh : stj'.heads = st2.heads := by rw [hh', Hinv.1]
                obtain ⟨hah, hamem⟩ := hlc2.add_pre hstjh hjl hjh hd0
                  (by rw [show stj'.frontier = stj.frontier by rw [hstj']]; exact Hinv.members)
                wp_apply wp_addToFrontier ch cl h cs stj' jv cons hok
                  (hlc2.shape_of hstjh (by rw [hv', Hinv.2.1]) (by rw [hf', Hinv.2.2.1])
                    (by rw [hn', List.length_set, Hinv.2.2.2.1])) (by omega) Hj1
                  (by rw [hjn]; exact hjl) (by rw [hjn]; exact hah)
                  (by rw [hjn, show stj'.frontier = stj.frontier by rw [hstj']]; exact hjnot)
                  (by rw [hjn]; exact hamem) (by rw [hfrj]; exact Hinv.2.2.2.2.2.2.2.1)
                  $$ [Hch] as ⟨%fr6, Hch, %Hfr6⟩
                · iframe; iframe Hcons
                rw [hjn] at Hfr6
                wp_for_post
                iframe
                iexists jv + W64 1, _
                iframe
                ipureintro
                refine ⟨hjv1.1, hjv1.2, ?_⟩
                rw [hj1]
                refine hlc2.inv_hit (stc' := ChSt.mk stj'.heads stj'.nDeps fr6 stj'.vis stj'.fu) Hinv hji hjl
                  hjh hfu' (by omega) hh' hv' hf' hn' ?_ ?_
                · have : frOf cs (ChSt.mk stj'.heads stj'.nDeps fr6 stj'.vis stj'.fu) =
                      fr6.map (hdOp cs stj') := by unfold frOf hdOp ChSt.head; rfl
                  rw [this]; exact Hfr6.1
                · intro x
                  show x ∈ fr6 ↔ _
                  rw [Hfr6.2 x, show stj'.frontier = stj.frontier by rw [hstj'], hnd, Hif]
                  constructor
                  · rintro (rfl | hx); exact Or.inl ⟨rfl, rfl⟩; exact Or.inr hx
                  · rintro (⟨rfl, -⟩ | hx); exact Or.inl rfl; exact Or.inr hx
              · -- `nDeps[j]` still positive
                wp_for_post
                iframe
                iexists jv + W64 1, stj'
                iframe
                ipureintro
                refine ⟨hjv1.1, hjv1.2, ?_⟩
                rw [hj1]
                refine hlc2.inv_hit Hinv hji hjl hjh hfu' (by omega) hh' hv' hf' hn'
                  (by rw [hfrj]; exact Hinv.2.2.2.2.2.2.2.1) ?_
                intro x
                rw [show stj'.frontier = stj.frontier by rw [hstj'], hnd]
                constructor
                · exact Or.inr
                · rintro (⟨-, h0⟩ | hx)
                  · exact absurd h0 Hif
                  · exact hx
            · -- the test fails
              wp_for_post
              iframe
              iexists jv + W64 1, stj
              iframe
              isplitl [Hchp Hr]
              · iapply chainsOwnCl_fold ch chV4 _ h cs stj Hcl4; iframe
              ipureintro
              refine ⟨hjv1.1, hjv1.2, ?_⟩
              rw [hj1]
              refine hlc2.inv_skip Hinv (Or.inr (Or.inr fun he => Hif ?_))
              rw [hk0n] at he
              exact htest.mpr he
          · -- client `j` finished
            ihave Hr := Hbackj $$ %stj %cvj [] Hej [Hcosj Hfusj]
            · ipureintro; exact ⟨fun _ _ => ⟨rfl, rfl, rfl, rfl⟩, rfl⟩
            · iunfold clientOwn
              isplitr
              · ipureintro; exact ⟨Hcj1, Hcj2, Hcj3⟩
              iexists cosj; iframe; ipureintro; exact Hcokj
            wp_for_post
            iframe
            iexists jv + W64 1, stj
            iframe
            isplitl [Hchp Hr]
            · iapply chainsOwnCl_fold ch chV4 _ h cs stj Hcl4; iframe
            ipureintro
            refine ⟨hjv1.1, hjv1.2, ?_⟩
            rw [hj1]
            refine hlc2.inv_skip Hinv (Or.inr (Or.inl fun hlt => Hif ?_))
            have := Hcosjl; rw [snat_eq] at this; rw [hk0]; omega
      · -- the loop's end: return
        sorry
  · -- every candidate tried
    have hiv : sint.Z iv = -1 := by
      have : ¬ 0 ≤ sint.Z iv := by
        intro h0; apply Hif; rw [show sint.Z (W64 0) = 0 from rfl]; exact h0
      omega
    iapply HΦ
    iframe
    ileft
    iframe
    isplitr
    · ipureintro; rfl
    rw [← hiv]
    iexact Hbad

end proof

end porcupine
end EtcdGrove
end Perennial
