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
        icases chainsRepr_acc chV2 h cs st3 i hil $$ Hr with ⟨%Hlen2, %cvi, He, Hc, Hback⟩
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
          sorry
        · -- client `i` finished
          have hfin : ¬ st2.head i < (chain cs i).length := by
            rw [hhi2]; intro hlt; apply Hif
            have := Hcos3l; rw [snat_eq] at this; rw [hk2]; omega
          ihave Hr := Hback $$ %st3 %cvi [] He [Hcos3 Hfus3]
          · ipureintro; exact ⟨fun _ _ => ⟨rfl, rfl, rfl, rfl⟩, rfl⟩
          · iunfold clientOwn
            isplitr
            · ipureintro; exact ⟨Hcvi1, Hcvi2, Hcvi3⟩
            iexists cos3; iframe; ipureintro; exact Hcok3
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
