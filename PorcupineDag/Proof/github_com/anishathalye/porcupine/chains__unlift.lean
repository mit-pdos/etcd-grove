/- Lean-first (no Rocq counterpart).

`(*chains).unlift(stack, serialized, consistency)` (dag.go, PR #46): the newest frame `f` lifted
its client `c`'s head (`Chains.headsOf_cons`); `removeFromFrontier(c)`, the client's `unlift`
(head back by one, bitset without `f.id`), the stack popped, `nDeps[c] = 0` (`f.id` is a
candidate below), then the loop over `j` (`deps_lift` read backwards: client `j`'s `nDeps` grows
by one exactly when its head's `firstUnk[c]` is the new head of `c` plus one, and it leaves the
frontier if it was there), then `addToFrontier(c)`: the frontier is the candidate list of the
frames below (`UnliftInv`, `SearchLemmas.lean`), hence `f.fr` (`candList_unique`).
-/
module

public import PorcupineDag.Spec.github_com.anishathalye.porcupine.chains__unlift
public import PorcupineDag.Spec.github_com.anishathalye.porcupine.client__unlift
public import PorcupineDag.Spec.github_com.anishathalye.porcupine.chains__removeFromFrontier
public import PorcupineDag.Spec.github_com.anishathalye.porcupine.chains__addToFrontier
public import PorcupineDag.Proof.github_com.anishathalye.porcupine.SearchLemmas
public import PorcupineDag.Proof.github_com.anishathalye.porcupine.DagLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace porcupine

open Iris Iris.BI Iris.ProofMode github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

end spec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NaInvG GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

theorem chains.unlift.wp_proof
    (wp_client_unlift : client.unlift.spec (GF := GF) (hG := hG))
    (wp_removeFromFrontierCl : chains.removeFromFrontier.spec (GF := GF) (hG := hG))
    (wp_addToFrontier : chains.addToFrontier.spec (GF := GF) (hG := hG)) :
    chains.unlift.spec (GF := GF) (hG := hG) := by
  intro σ S np cons h cs ch stack_ptr lin_ptr cm f fs fr cache s p hok hwf halloc hst
  wp_start as ⟨#Hcons, Hs⟩
  unfold searchOwn
  iNamed Hs
  obtain ⟨Hci, Hfr⟩ := Hci
  obtain ⟨Hws1, Hws2⟩ := Hws
  -- the newest frame lifted the head of client `c`
  have hfs : FramesStruct h cs (Before h cs) (f :: fs) := hst.2.1
  have hcall : CallLeRet h := hwf.2
  obtain ⟨c, hc, hcl, hcop, hHH⟩ := headsOf_cons hok hcall hfs
  have hx : UnliftCtx h cs st (headsOf cs (ids fs)) c f fs :=
    ⟨hok, hcall, Hci, hfs, hc, hcl, hcop, by rw [Hci.2.1]; exact hHH, rfl⟩
  have hfid : f.id ∈ chain cs c := by rw [← hcop]; exact List.mem_of_getElem? (opAt_get hcl)
  have hcof : clientOf cs f.id = c := clientOf_eq hok hc hfid
  have hfidl : f.id < h.length := lt_length_of_mem hok hfid
  have hcs : (cs.length : Int) ≤ 2 ^ 45 := by
    have := halloc; unfold AllocOk maxAllocBytes at this
    have hm : (cs.length : Int) * 1 ≤ cs.length * ((max h.length 6 : Nat) : Int) :=
      Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
    omega
  icases stackRep_pop S np cs ses f fs $$ Hses with ⟨%ses', %se, %Hse, #Hsv, #Hses'⟩
  obtain ⟨rfl, Hop, Hcid, Hpos⟩ := Hse
  rw [hcof] at Hcid
  ihave %Hsl := ownSlice_len $$ Hstack
  obtain ⟨Hsl1, Hsl2⟩ := Hsl
  simp only [List.length_append, List.length_singleton] at Hsl1
  icases chainsOwn_cl ch h cs st $$ Hch with ⟨%cl, Hch⟩
  icases chainsOwnCl_acc ch cl h cs st c hc $$ Hch with ⟨%chV, %cv, Hchp, %Hcl, He, Hc, Hback⟩
  obtain ⟨rfl, Hcll⟩ := Hcl
  wp_auto
  have Hb : 0 ≤ sint.Z (ssl.len - W64 1) ∧ sint.Z (ssl.len - W64 1) < sint.Z ssl.len := by
    constructor <;> word
  simp only [Hb, _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index ssl _ (ses' ++ [se]) _ se Hb.1 $$ [Hstack] as Hstack
  · iframe; ipureintro
    have : (sint.Z (ssl.len - W64 1)).toNat = ses'.length := by word
    rw [this]; simp
  have Hb2 : 0 ≤ sint.Z se.clientId' ∧ sint.Z se.clientId' < sint.Z chV.clients'.len := by
    rw [Hcid, Hcll]; omega
  simp only [Hb2, _root_.and_self, ↓reduceIte]
  rw [Hcid]
  ihave Hch := Hback $$ %st %cv [] Hchp He Hc
  · ipureintro; exact ⟨fun _ _ => ⟨rfl, rfl, rfl, rfl⟩, rfl⟩
  wp_auto
  have hcn : sint.nat se.clientId' = c := by
    have := Hcid; simp only [sint.nat, sint.Z] at this ⊢; omega
  wp_apply wp_removeFromFrontierCl ch chV.clients' h cs st se.clientId' (by omega)
    (fun v hv => (Hci.2.2.2.2.2.2.2.2.2.1 v hv).1) (by omega) $$ [Hch] as Hch
  · iframe
  rw [hcn]
  -- `client.unlift(top, serialized)`
  icases chainsOwnCl_acc ch chV.clients' h cs _ c hc $$ Hch with ⟨%chV1, %cv1, Hchp, %Hcl1, He, Hc, Hback⟩
  icases clientOwn_facts h cs _ c cv1 $$ Hc with ⟨%Hcv, Hc⟩
  obtain ⟨Hcv1, Hcv2, Hcv3⟩ := Hcv
  have hid : se.clientId' = cv1.id' := BitVec.eq_of_toInt_eq (by
    have h1 := Hcid; have h2 := Hcv1; simp only [sint.Z] at h1 h2; omega)
  have hopn : uint.nat se.opId' = f.id := by
    have := Hop; simp only [sint.Z] at this; simp only [uint.nat]; word
  have hlen : uint.nat se.opId' / 64 < ws.length := by
    rw [hopn, Hws1]; exact bsChunks_gt _ _ hfidl
  wp_apply wp_client_unlift (sliceIndexRef client (c : Int) chV.clients') cv1 se lin_ptr lsl ws hid
    (by omega) hlen $$ [He lin Hlin] as ⟨He, lin, Hlin⟩
  · iframe
  -- `*stack = (*stack)[:len(*stack)-1]`
  ihave %Hwf := ownSlice_wf $$ Hstack
  obtain ⟨Hwf1, Hwf2⟩ := Hwf
  have Hb3 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (ssl.len - W64 1) ∧
      sint.Z (ssl.len - W64 1) ≤ sint.Z ssl.cap := by
    refine ⟨by decide, by word, by word⟩
  simp only [Hb3, _root_.and_self, ↓reduceIte]
  icases ownSlice_slice_with_cap (W64 0) (ssl.len - W64 1) ssl (ses' ++ [se])
    ⟨by decide, by word, by word⟩ $$ [Hstack Hscap] with ⟨-, Hstack, Hscap⟩
  · iframe
  have hsub : subslice (sint.nat (W64 0)) (sint.nat (ssl.len - W64 1)) (ses' ++ [se]) = ses' := by
    rw [show sint.nat (W64 0) = 0 from rfl, show sint.nat (ssl.len - W64 1) = ses'.length by word]
    simp [subslice]
  rw [hsub]
  wp_auto
  -- `ch.clients[clientId].nDeps = 0`
  obtain ⟨Hcl1, -⟩ := Hcl1
  rw [Hcl1, Hcid]
  simp only [show 0 ≤ (c : Int) ∧ (c : Int) < sint.Z chV.clients'.len by omega, _root_.and_self,
    ↓reduceIte]
  wp_auto
  have hHc := hx.head_c
  obtain ⟨st3, hst3⟩ : ∃ st3 : ChSt, st3 = ChSt.mk (headsOf cs (ids fs))
      (st.nDeps.set c (W64 0)) (st.frontier.erase c) st.vis st.fu := ⟨_, rfl⟩
  ihave Hch := Hback $$ %st3 %_ [] Hchp He [Hc]
  · subst hst3
    ipureintro
    refine ⟨fun c' hc' => ⟨(hx.head_ne hc').symm, ?_, rfl, rfl⟩, rfl⟩
    simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hc')]
  · subst hst3
    have hhd : sint.Z (cv1.head' - W64 1) = ((headsOf cs (ids fs)).getD c 0 : Nat) := by
      have h2 := Hcv2
      unfold ChSt.head at h2 hHc
      simp only at h2
      rw [hHc] at h2
      word
    have hnd : (W64 0 : w64) = (st.nDeps.set c (W64 0)).getD c 0 := by
      have hcn' : c < st.nDeps.length := by rw [Hci.1.2.1]; exact hc
      simp [List.getD_eq_getElem?_getD, List.getElem?_set_self hcn']
    iapply (clientOwn_upd (st := ChSt.mk st.heads st.nDeps (st.frontier.erase c) st.vis st.fu)
      (st' := ChSt.mk (headsOf cs (ids fs)) (st.nDeps.set c (W64 0))
      (st.frontier.erase c) st.vis st.fu) h cs cv1 ⟨cv1.id', cv1.cltOps', cv1.head' - W64 1, W64 0⟩
      rfl rfl hhd hnd rfl rfl)
    iexact Hc
  have hinit := hx.inv_init (stc := st3) (by rw [hst3]) (by rw [hst3]) (by rw [hst3]) (by rw [hst3])
    (by rw [hst3])
  -- the loop over `j`
  ihave HI : (∃ (jv : w64) (stc : ChSt),
      "j" ∷ j_ptr ↦ jv ∗ "Hch" ∷ chainsOwnCl ch chV.clients' h cs stc ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z jv ∧ sint.Z jv ≤ cs.length ∧
        UnliftInv h cs st (headsOf cs (ids fs)) c (sint.nat jv) stc⌝ : IProp GF) $$ [j Hch]
  · iexists W64 0, _
    iframe
    ipureintro; exact ⟨by decide, by word, by rw [show sint.nat (W64 0) = 0 from rfl]; exact hinit⟩
  wp_for HI
  obtain ⟨Hj1, Hj2, Hinv⟩ := Hj
  iunfold chainsOwnCl at Hch
  icases Hch with ⟨%chV2, Hchp, %Hcl2, Hr⟩
  wp_auto
  rw [Hcl2]
  wp_if_destruct
  · -- the body
    have hjl : sint.nat jv < cs.length := by
      have : sint.Z jv < sint.Z chV.clients'.len := by have := go.intoVal_inj Hif; simpa using this
      rw [Hcll] at this; rw [snat_eq]; omega
    have hjz : sint.Z jv = ((sint.nat jv : Nat) : Int) := by rw [snat_eq]; omega
    have hjv1 : 0 ≤ sint.Z (jv + W64 1) ∧ sint.Z (jv + W64 1) ≤ cs.length := by
      have := hjl; rw [snat_eq] at this
      have h1 : sint.Z (jv + W64 1) = sint.Z jv + 1 := by word
      omega
    have hshape : ShapeOk cs stc := hx.shape Hinv.1 Hinv.2.1 Hinv.2.2.1 Hinv.2.2.2.1
    wp_if_destruct
    · -- `j == clientId`
      wp_for_post
      iframe
      iexists se.clientId' + W64 1, stc
      iframe
      isplitl [Hchp Hr]
      · iapply chainsOwnCl_fold ch chV2 _ h cs stc Hcl2; iframe
      ipureintro
      refine ⟨hjv1.1, hjv1.2, ?_⟩
      rw [show sint.nat (se.clientId' + W64 1) = sint.nat se.clientId' + 1 by
        rw [snat_eq, snat_eq]; word]
      exact hx.inv_skip Hinv (Or.inl hcn)
    · -- `j != clientId`: client `j`'s head
      obtain ⟨jn, hjn⟩ : ∃ jn, sint.nat jv = jn := ⟨_, rfl⟩
      rw [hjn] at hjl hjz Hinv
      have hjc : jn ≠ c := by
        intro he; apply Hif; apply BitVec.eq_of_toInt_eq
        have := Hcid; simp only [sint.Z] at this hjz; omega
      icases chainsRepr_acc chV2 h cs stc jn hjl $$ Hr with ⟨%Hlen2, %cvj, Hej, Hcj, Hbackj⟩
      iunfold clientOwn at Hcj
      icases Hcj with ⟨%Hcj, %cos, Hcos, %Hcok, Hfus⟩
      obtain ⟨Hcj1, Hcj2, Hcj3⟩ := Hcj
      ihave %Hcosl := ownSlice_len $$ Hcos
      have hhj : stc.head jn = (headsOf cs (ids fs)).getD jn 0 := by
        unfold ChSt.head; rw [Hinv.1]
      have hbj : 0 ≤ (jn : Int) ∧ (jn : Int) < sint.Z chV2.clients'.len := by omega
      simp only [hjz, hbj, _root_.and_self, ↓reduceIte]
      wp_auto
      simp only [hjz, hbj, _root_.and_self, ↓reduceIte]
      wp_auto
      have hcosl : cos.length = (chain cs jn).length := Hcok.1
      have hk0 : sint.Z cvj.head' = (((headsOf cs (ids fs)).getD jn 0 : Nat) : Int) := by
        rw [Hcj2, hhj]
      have hj1 : sint.nat (jv + W64 1) = jn + 1 := by
        rw [← hjn, snat_eq, snat_eq]; word
      wp_if_destruct
      · -- client `j` unfinished: its head's `firstUnk[c]`
        obtain ⟨k0, hk0n⟩ : ∃ k0, (headsOf cs (ids fs)).getD jn 0 = k0 := ⟨_, rfl⟩
        rw [hk0n] at hk0
        have hk0l : k0 < cos.length := by
          have := Hcosl; rw [snat_eq] at this; omega
        list_elem cos k0 as co
        icases ownSlice_elem_acc (sint.Z cvj.head') co _ _ cos (by omega)
          (by rw [hk0]; simpa using Hco_lookup) $$ Hcos with ⟨Hco, Hcos⟩
        icases BigSepL.bigSepL_lookup_acc Hco_lookup $$ Hfus with ⟨Hfu, Hfus⟩
        ihave %Hful := ownSlice_len $$ Hfu
        have hful : (stc.fuAt jn k0).length = cs.length :=
          (hshape.2.2.2.2 jn k0 (by omega)).2.2
        have hbk : 0 ≤ sint.Z cvj.head' ∧ sint.Z cvj.head' < sint.Z cvj.cltOps'.len := by omega
        have hbc : 0 ≤ (c : Int) ∧ (c : Int) < sint.Z co.firstUnk'.len := by
          have := Hful; rw [snat_eq] at this; omega
        repeat ((try simp only [hjz, hbj, hbk, Hcid, hbc, _root_.and_self, ↓reduceIte]); wp_auto)
        simp only [Hcid, hbc, _root_.and_self, ↓reduceIte]
        list_elem (stc.fuAt jn k0) c as fv
        wp_apply wp_load_slice_index co.firstUnk' (c : Int) (stc.fuAt jn k0) _ fv (by omega) $$ [Hfu] as Hfu
        · iframe; ipureintro; simpa using Hfv_lookup
        -- client `j` back
        ihave Hcos := Hcos $$ %co Hco
        ihave Hfus := Hfus $$ %co Hfu
        have hset : cos.set k0 co = cos := by
          obtain ⟨hl, he⟩ := List.getElem?_eq_some_iff.mp Hco_lookup
          rw [← he]; exact List.set_getElem_self hl
        rw [show (sint.Z cvj.head').toNat = k0 by omega, hset]
        ihave Hr := Hbackj $$ %stc %cvj [] Hej [Hcos Hfus]
        · ipureintro; exact ⟨fun _ _ => ⟨rfl, rfl, rfl, rfl⟩, rfl⟩
        · iunfold clientOwn
          isplitr
          · ipureintro; exact ⟨Hcj1, Hcj2, Hcj3⟩
          iexists cos; iframe; ipureintro; exact Hcok
        -- client `c`'s head
        icases chainsRepr_acc chV2 h cs stc c hc $$ Hr with ⟨-, %cvc, Hec, Hcc, Hbackc⟩
        icases clientOwn_facts h cs stc c cvc $$ Hcc with ⟨%Hcc', Hcc⟩
        have hbc2 : 0 ≤ (c : Int) ∧ (c : Int) < sint.Z chV2.clients'.len := by omega
        simp only [Hcid, hbc2, _root_.and_self, ↓reduceIte]
        wp_auto
        ihave Hr := Hbackc $$ %stc %cvc [] Hec Hcc
        · ipureintro; exact ⟨fun _ _ => ⟨rfl, rfl, rfl, rfl⟩, rfl⟩
        -- what `firstUnk[c]` holds
        have hvis : stc.visAt jn k0 = true := by
          unfold ChSt.visAt; rw [Hinv.2.1]
          refine Hci.2.2.2.2.2.2.2.1 jn k0 (by omega) ?_
          rw [hx.head_ne hjc, hk0n]; exact Nat.le_refl _
        have hfv : sint.Z fv = FUe h cs jn c k0 := by
          have := hx.2.2.1.2.2.2.2.2.2.1 jn k0 (by unfold ChSt.visAt at hvis ⊢; rw [Hinv.2.1] at hvis; exact hvis)
            c hc (Ne.symm hjc)
          unfold ChSt.fuAt at this Hfv_lookup
          rw [Hinv.2.2.1] at Hfv_lookup
          rw [List.getD_eq_getElem?_getD, Hfv_lookup] at this
          exact this
        have hhc : sint.Z cvc.head' = (((headsOf cs (ids fs)).getD c 0 : Nat) : Int) := by
          rw [Hcc'.2.1]; unfold ChSt.head; rw [Hinv.1]
        have hFle : FUe h cs jn c k0 ≤ (chain cs c).length := fue_le
        have hcll : (chain cs c).length < 2 ^ 60 := by
          have := chain_length_le hok c
          have := hwf.1; omega
        have htest : fv = cvc.head' + W64 1 ↔ FUe h cs jn c k0 = (headsOf cs (ids fs)).getD c 0 + 1 := by
          constructor
          · intro he; rw [he] at hfv
            have : sint.Z (cvc.head' + W64 1) = sint.Z cvc.head' + 1 := by
              rw [hhc] at ⊢; have := hcl; word
            omega
          · intro he; apply BitVec.eq_of_toInt_eq
            have : sint.Z (cvc.head' + W64 1) = sint.Z cvc.head' + 1 := by
              rw [hhc] at ⊢; have := hcl; word
            simp only [sint.Z] at this hfv hhc ⊢
            omega
        wp_if_destruct
        · -- the test holds: `nDeps[j]` grows
          rw [← hk0n] at htest
          have hfu' := htest.mp rfl
          icases chainsRepr_acc chV2 h cs stc jn hjl $$ Hr with ⟨-, %cvj2, Hej, Hcj, Hbackj⟩
          icases clientOwn_facts h cs stc jn cvj2 $$ Hcj with ⟨%Hcj', Hcj⟩
          simp only [hjz, hbj, _root_.and_self, ↓reduceIte]
          wp_auto
          rw [Hcj'.2.2]
          wp_join iprop(∃ stx : ChSt, j_ptr ↦ jv ∗ ch_ptr ↦ ch ∗ chainsOwnCl ch chV.clients' h cs stx ∗
              ⌜stx = ChSt.mk stc.heads stc.nDeps (if stc.nDeps.getD jn 0 = W64 0 then
                stc.frontier.erase jn else stc.frontier) stc.vis stc.fu⌝)
            with [Hej Hcj Hbackj Hchp j ch] as ⟨%stx, j, ch, Hch, %Hstx⟩
          · -- `nDeps[j] == 0`: client `j` leaves the frontier
            ihave Hr := Hbackj $$ %stc %cvj2 [] Hej Hcj
            · ipureintro; exact ⟨fun _ _ => ⟨rfl, rfl, rfl, rfl⟩, rfl⟩
            ihave Hch := chainsOwnCl_fold ch chV2 _ h cs stc Hcl2 $$ [Hchp Hr]
            · iframe
            have hmemlt : ∀ v ∈ stc.frontier, v < cs.length := fun v hv =>
              (Hci.2.2.2.2.2.2.2.2.2.1 v (Hinv.2.2.2.2.2.2.2.1.subset hv)).1
            wp_apply wp_removeFromFrontierCl ch chV.clients' h cs stc jv Hj1 hmemlt (by omega)
              $$ [Hch] as Hch
            · iframe
            isplitl []
            · ipureintro; rfl
            iexists _
            iframe
            ipureintro
            rw [hjn, if_pos Hif]
          · -- `nDeps[j] != 0`
            ihave Hr := Hbackj $$ %stc %cvj2 [] Hej Hcj
            · ipureintro; exact ⟨fun _ _ => ⟨rfl, rfl, rfl, rfl⟩, rfl⟩
            ihave Hch := chainsOwnCl_fold ch chV2 _ h cs stc Hcl2 $$ [Hchp Hr]
            · iframe
            iexists stc
            iframe
            ipureintro
            rw [if_neg Hif]
          -- `nDeps[j]++`
          iunfold chainsOwnCl at Hch
          icases Hch with ⟨%chV3, Hchp, %Hcl3, Hr⟩
          icases chainsRepr_acc chV3 h cs stx jn hjl $$ Hr with ⟨%Hlen3, %cvj3, Hej, Hcj, Hbackj⟩
          icases clientOwn_facts h cs stx jn cvj3 $$ Hcj with ⟨%Hcj3, Hcj⟩
          have hbj3 : 0 ≤ (jn : Int) ∧ (jn : Int) < sint.Z chV3.clients'.len := by omega
          repeat ((try simp only [hjz, hbj3, _root_.and_self, ↓reduceIte]); wp_auto)
          have hjn3 : jn < stx.nDeps.length := by
            rw [Hstx]; simp only; rw [Hinv.2.2.2.1, Hci.1.2.1]; exact hjl
          have hnd3 : cvj3.nDeps' + W64 1 = (stx.nDeps.set jn (stx.nDeps.getD jn 0 + W64 1)).getD jn 0 := by
            rw [Hcj3.2.2]; simp [List.getD_eq_getElem?_getD, List.getElem?_set_self hjn3]
          ihave Hr := Hbackj $$ %(ChSt.mk stx.heads (stx.nDeps.set jn (stx.nDeps.getD jn 0 + W64 1))
              stx.frontier stx.vis stx.fu) %_ [] Hej [Hcj]
          · ipureintro
            refine ⟨fun c' hc' => ⟨rfl, ?_, rfl, rfl⟩, rfl⟩
            simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hc')]
          · iapply (clientOwn_upd (st := stx) (st' := ChSt.mk stx.heads
              (stx.nDeps.set jn (stx.nDeps.getD jn 0 + W64 1)) stx.frontier stx.vis stx.fu) h cs cvj3
              ⟨cvj3.id', cvj3.cltOps', cvj3.head', cvj3.nDeps' + W64 1⟩ rfl rfl Hcj3.2.1 hnd3 rfl rfl)
            iexact Hcj
          wp_for_post
          iframe
          iexists jv + W64 1, _
          iframe
          isplitl [Hchp Hr]
          · iapply chainsOwnCl_fold ch chV3 _ h cs _ Hcl3; iframe
          ipureintro
          refine ⟨hjv1.1, hjv1.2, ?_⟩
          rw [hj1]
          refine hx.inv_hit Hinv hjc hjl (by rw [hk0n, ← hcosl]; exact hk0l) hfu' (by omega)
            (by rw [Hstx]) (by rw [Hstx]) (by rw [Hstx]) (by rw [Hstx]) (by rw [Hstx])
        · -- the test fails
          wp_for_post
          iframe
          iexists jv + W64 1, stc
          iframe
          isplitl [Hchp Hr]
          · iapply chainsOwnCl_fold ch chV2 _ h cs stc Hcl2; iframe
          ipureintro
          refine ⟨hjv1.1, hjv1.2, ?_⟩
          rw [hj1]
          refine hx.inv_skip Hinv (Or.inr (Or.inr fun he => Hif ?_))
          rw [← hk0n] at htest
          exact htest.mpr he
      · -- client `j` finished
        ihave Hr := Hbackj $$ %stc %cvj [] Hej [Hcos Hfus]
        · ipureintro; exact ⟨fun _ _ => ⟨rfl, rfl, rfl, rfl⟩, rfl⟩
        · iunfold clientOwn
          isplitr
          · ipureintro; exact ⟨Hcj1, Hcj2, Hcj3⟩
          iexists cos; iframe; ipureintro; exact Hcok
        wp_for_post
        iframe
        iexists jv + W64 1, stc
        iframe
        isplitl [Hchp Hr]
        · iapply chainsOwnCl_fold ch chV2 _ h cs stc Hcl2; iframe
        ipureintro
        refine ⟨hjv1.1, hjv1.2, ?_⟩
        rw [hj1]
        refine hx.inv_skip Hinv (Or.inr (Or.inl fun hlt => Hif ?_))
        have := Hcosl; rw [snat_eq] at this; rw [hk0]
        omega
  · -- the loop's end: `addToFrontier(clientId)`
    have hnlt : ¬ sint.Z jv < sint.Z chV.clients'.len := by
      intro hlt; apply Hif; simp [hlt]
    have hjend : sint.nat jv = cs.length := by
      have := hnlt
      rw [Hcll] at this; rw [snat_eq]; omega
    simp only [hnlt, _root_.decide_false, Bool.false_eq_true, ↓reduceIte]
    rw [hjend] at Hinv
    obtain ⟨hshape, hcnot, hch, hcop', hmem, hsort⟩ := hx.add_pre Hinv
    ihave Hch := chainsOwnCl_fold ch chV2 _ h cs stc Hcl2 $$ [Hchp Hr]
    · iframe
    ihave Hch := chainsOwnCl_weaken ch _ h cs stc $$ Hch
    wp_auto
    wp_apply wp_addToFrontier ch h cs stc se.clientId' cons hok hshape (by omega) (by omega)
      (by rw [hcn]; exact hc) (by rw [hcn]; exact hch) (by rw [hcn]; exact hcnot)
      (by rw [hcn]; exact hmem) hsort $$ [Hch] as ⟨%fr', Hch, %Hfr'⟩
    · iframe; iframe Hcons
    rw [hcn] at Hfr'
    obtain ⟨hfin, hfrf⟩ := hx.inv_final Hinv Hfr'.1 Hfr'.2
    iapply HΦ
    have hfnot : f.id ∉ ids fs := (List.nodup_cons.mp (framesStruct_nodup hfs)).1
    isplitl
    · iexists (ChSt.mk stc.heads stc.nDeps fr' stc.vis stc.fu),
        slice.slice ssl stackEntry (W64 0) (ssl.len - W64 1), ses', lsl, bsClear ws se.opId'
      simp only [named]
      isplitl [Hch]
      · iexact Hch
      isplitr
      · ipureintro; exact ⟨hfin, hfrf⟩
      iframe
      iframe Hses'
      ipureintro
      refine ⟨by rw [bsClear_length]; exact Hws1, fun i => ?_⟩
      rw [bsBit_clear _ _ _ hlen, Hws2, hopn]
      by_cases hif : i = f.id
      · subst hif; simp [hfnot]
      · simp [ids, hif]
    · iframe Hsv; ipureintro; exact Hpos

end proof

end porcupine
end EtcdGrove
end Perennial
