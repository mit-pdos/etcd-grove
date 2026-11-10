/- Lean-first (no Rocq counterpart). The proof of `stream.pick`: the live ids collected, one chosen.

The callee: `choose`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.stream__pick
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.choose
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.StreamLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem stream.pick.wp_proof
    (wp_choose : choose.spec (GF := GF) (hG := hG)) :
    stream.pick.spec (GF := GF) (hG := hG) := by
  intro T rs W Hl P
  wp_start as ⟨Hctx, HB⟩
  iunfold streamCtx at Hctx
  icases Hctx with ⟨Hep, -, -, -, -, #Fwm, -⟩
  iunfold smuBody at HB
  icases HB with ⟨Hwm, ⟨%osl, %ids, Hord, Hids, Hcap, %Hids⟩, Hevl, Hreg, Hrcv0, #Hlb, %Hknown, Hwats⟩
  iunfold epCtx at Hep; icases Hep with ⟨Hrn, -⟩; iunfold rnCtx at Hrn
  icases Hrn with ⟨#Hpkg, -⟩
  wp_auto
  ihave %Hlen := ownSlice_len $$ Hids
  ihave HI : (∃ (j : w64) (v0 : w64) (lsl : GoSlice) (lv : List w64),
      "i" ∷ i_ptr ↦ j ∗ "id" ∷ id_ptr ↦ v0 ∗ "live" ∷ live_ptr ↦ lsl ∗ "Hlv" ∷ lsl ↦* lv ∗
      "Hlcap" ∷ ownSliceCap w64 lsl (DFrac.own 1) ∗ "Hids" ∷ osl ↦* ids ∗
      "Hwm" ∷ T.wm ↦$ GMap.fmap Reg.wp W ∗
      "Hwats" ∷ ([∗map] id ↦ x ∈ W, watcherOwn' Hl rs T.σs.ws id x) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z osl.len ∧
        ∀ id ∈ lv, ∃ x, W !! id = some x ∧ x.cm = false⌝ : IProp GF)
      $$ [i id live Hids Hwm Hwats]
  · iexists W64 0, _, slice.nil, []
    iframe
    isplitl []
    · iapply ownSlice_nil
    isplitl []
    · iapply ownSliceCap_nil
    ipureintro; refine ⟨by word, by word, ?_⟩; simp
  wp_for HI
  by_cases Hlt : sint.Z j < sint.Z osl.len
  · rw [decide_eq_true Hlt]; simp only [↓reduceIte]
    have hjl : sint.nat j < ids.length := by rw [Hlen.1]; word
    list_elem ids (sint.nat j) as wid
    have hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z osl.len := ⟨Hj.1, Hlt⟩
    (try wp_auto)
    (try simp only [hb, _root_.and_self, ↓reduceIte])
    wp_apply wp_load_slice_index osl (sint.Z j) ids (DFrac.own 1) wid Hj.1 $$ [Hids] as Hids
    · iframe; ipureintro; exact Hwid_lookup
    (try wp_auto)
    obtain ⟨x, hx⟩ : ∃ x, W !! wid = some x := by
      have := (Hids.2 wid).1 (List.mem_of_getElem? Hwid_lookup)
      exact Option.isSome_iff_exists.1 this
    wp_apply (wp_map_lookup1 go_etcd_io.etcd.server.v3.storage.mvcc.WatchID.ty
      watcher.ty.PointerType T.wm (GMap.fmap Reg.wp W) wid (DFrac.own 1)) $$ [$Hwm] as Hwm
    rw [hx]
    simp only [Option.map_some, Option.getD_some]
    icases (BigSepM.bigSepM_lookup_acc
      (Φ := fun (id : w64) (x : Reg) => watcherOwn' (GF := GF) Hl rs T.σs.ws id x) (m := W) hx)
      $$ Hwats with ⟨Hw, Hwats⟩
    iunfold watcherOwn' at Hw
    icases Hw with ⟨%wv, Hp, #Hk, #He, Hlbk, %Hok⟩
    have hcm : wv.cancelled' = x.cm := Hok.2.2.2.2.2.2.2.2.2.2.1
    (try wp_auto)
    ispecialize Hwats $$ [Hp Hlbk]
    · iunfold watcherOwn'
      iexists wv
      iframe Hp Hlbk
      iframe #
      ipureintro; exact Hok
    cases hc : wv.cancelled'
    · simp only [Bool.not_false]
      (try wp_auto)
      wp_apply wp_slice_literal [wid]
      (try wp_auto)
      isplitr
      · ipureintro; rfl
      iintro %sl1 ⟨Hs1, Hs1cap⟩
      (try wp_auto)
      wp_apply wp_slice_append lsl lv _ [wid] (DFrac.own 1) $$ [$Hlv $Hlcap $Hs1] as %lsl' ⟨Hlv, Hlcap, -⟩
      (try wp_auto)
      wp_for_post
      iframe
      iexists j + W64 1, wid, lsl', lv ++ [wid]
      iframe
      ipureintro; refine ⟨by word, by word, ?_⟩
      intro id' hid'
      rcases List.mem_append.1 hid' with h | h
      · exact Hj.2.2 id' h
      · rw [List.mem_singleton] at h; subst h; exact ⟨x, hx, by rw [← hcm, hc]⟩
    · simp only [Bool.not_true]
      (try wp_auto)
      wp_for_post
      iframe
      iexists j + W64 1, wid, lsl, lv
      iframe
      ipureintro; refine ⟨by word, by word, Hj.2.2⟩
  rw [decide_eq_false Hlt]; simp only [Bool.false_eq_true, ↓reduceIte]
  (try wp_auto)
  ihave %Hlvl := ownSlice_len $$ Hlv
  ihave HB : smuBody T rs W Hl P $$ [Hwm Hord Hids Hcap Hevl Hreg Hrcv0 Hwats]
  · iunfold smuBody
    iframe
    iframe #
    ipureintro; exact ⟨Hids, Hknown⟩
  by_cases hz : lsl.len = W64 0
  · rw [decide_eq_true hz]
    (try wp_auto)
    iapply HΦ
    iframe
    ipureintro; intro h; cases h
  rw [decide_eq_false hz]
  (try wp_auto)
  wp_apply wp_choose as %c %Hc
  have hpos : 0 < sint.Z lsl.len := by
    have := Hlvl.2
    have : sint.Z lsl.len ≠ 0 := fun h => hz (by word)
    omega
  have hcl : sint.nat c < lv.length := by rw [Hlvl.1]; have := Hc.2.1 hpos; word
  list_elem lv (sint.nat c) as cid
  (try wp_auto)
  (try simp only [show 0 ≤ sint.Z c ∧ sint.Z c < sint.Z lsl.len from ⟨Hc.1, Hc.2.1 hpos⟩,
    _root_.and_self, ↓reduceIte])
  wp_apply wp_load_slice_index lsl (sint.Z c) lv (DFrac.own 1) cid Hc.1 $$ [Hlv] as Hlv
  · iframe; ipureintro; exact Hcid_lookup
  (try wp_auto)
  iapply HΦ
  iframe
  ipureintro; intro _; exact Hj.2.2 cid (List.mem_of_getElem? Hcid_lookup)

end proof

end mvccfull
end EtcdGrove
end Perennial
