/- Lean-first (no Rocq counterpart). The proof of `stream.complete` (Probe, proved).

Under `s.mu` (released by the `defer`), the loop over `s.order` keeps the lock's watchers'
`[∗map]` as its invariant; each watcher not cancelled or compacted is read by `expect` at the
spec's history bound `Hlb` (its position's `0 ≤ rev`, `0 ≤ index` from `wPosOk'`).

The callee: `stream.expect`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.stream__complete
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.stream__expect

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

theorem stream.complete.wp_proof
    (wp_stream_expect : stream.expect.spec (GF := GF) (hG := hG)) :
    stream.complete.spec (GF := GF) (hG := hG) := by
  intro T Hlb upto Hu0 HuL HuM
  wp_start as ⟨Hctx, Hrd, #HlbU⟩
  iunfold streamCtx at Hctx
  icases Hctx with ⟨Hep, #Fx, -, -, -, #Fwm, -, -, #Hmu, -⟩
  iunfold epCtx at Hep
  icases Hep with ⟨Hrn, -, -⟩
  iunfold rnCtx at Hrn
  iunfold runnerH at Hrn
  icases Hrn with ⟨#Hpkg, #Hmpkg, -, -, #HrH, -⟩
  ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_auto
  wp_bind (App (Val wrapDefer) _)
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hmu] as ⟨Hlocked, HL⟩
  iunfold smuInv at HL
  icases HL with ⟨%rs0, %W, %Hl, %P, HB⟩
  iunfold smuBody at HB
  icases HB with ⟨Hwm, ⟨%osl, %ids, Hord, Hids, Hcap, %Hids⟩, Hevl, Hreg, Hrcv0, #Hlb, %Hknown, Hwats⟩
  (try wp_auto)
  ihave %Hlen := ownSlice_len $$ Hids
  ihave HI : (∃ (j : w64) (v0 : w64),
      "i" ∷ i_ptr ↦ j ∗ "id" ∷ id_ptr ↦ v0 ∗ "Hids" ∷ osl ↦* ids ∗
      "Hwm" ∷ T.wm ↦$ GMap.fmap Reg.wp W ∗ "Hrd" ∷ histRd T.ep.h T.ep.γh ∗
      "Hwats" ∷ ([∗map] id ↦ x ∈ W, watcherOwn' Hl rs0 T.σs.ws id x) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z osl.len⌝ : IProp GF) $$ [i id Hids Hwm Hwats Hrd]
  · iexists W64 0, _
    iframe
    ipureintro; constructor <;> word
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
      (Φ := fun (id : w64) (x : Reg) => watcherOwn' (GF := GF) Hl rs0 T.σs.ws id x) (m := W) hx)
      $$ Hwats with ⟨Hw, Hwats⟩
    iunfold watcherOwn' at Hw
    icases Hw with ⟨%wv, Hp, #Hk, #He, Hlbk, %Hok⟩
    (try wp_auto)
    have Hpos := Hok.2.2.2.2.2.2.2.2.2.2.2.2.2
    have hr0 : 0 ≤ sint.Z wv.rev' := Hpos.1
    have hi0 : 0 ≤ sint.Z wv.index' := Hpos.2.1
    cases hc : wv.cancelled'
    · (try rw [hc])
      (try wp_auto)
      cases hm : wv.compacted'
      · (try rw [hm])
        (try wp_auto)
        wp_apply (wp_stream_expect T.s T.ep.x T.ep.h T.ep.γh Hlb x.wp wv x.key x.e upto
            (DFrac.own 1) DFrac.discard DFrac.discard hr0 hi0 HuL HuM)
          $$ [Hp Hrd] as %ch %rr %more ⟨Hp, -, -, Hrd, -⟩
        · iframe Hp Hrd
          iframe #
        (try wp_auto)
        cases more
        · (try wp_auto)
          ihave Hwats := Hwats $$ [Hp Hlbk]
          · iunfold watcherOwn'
            iexists wv
            iframe
            iframe #
            ipureintro; exact Hok
          wp_for_post
          iframe
          iexists j + W64 1, wid
          iframe
          ipureintro; constructor <;> word
        · (try wp_auto)
          ihave Hwats := Hwats $$ [Hp Hlbk]
          · iunfold watcherOwn'
            iexists wv
            iframe
            iframe #
            ipureintro; exact Hok
          wp_for_post
          wp_apply sync.Mutex.wp_Unlock (sF go!"mu" T.s) (smuInv T)
            $$ [$Hmu $Hlocked Hwm Hord Hids Hcap Hevl Hreg Hrcv0 Hwats]
          · iunfold smuInv
            iexists rs0, W, Hl, P
            iunfold smuBody
            iframe
            iframe #
            inext; ipureintro; exact ⟨Hids, Hknown⟩
          (try wp_auto)
          iapply HΦ
          iframe
      · (try rw [hm])
        (try wp_auto)
        ihave Hwats := Hwats $$ [Hp Hlbk]
        · iunfold watcherOwn'
          iexists wv
          iframe
          iframe #
          ipureintro; exact Hok
        wp_for_post
        iframe
        iexists j + W64 1, wid
        iframe
        ipureintro; constructor <;> word
    · (try rw [hc])
      (try wp_auto)
      ihave Hwats := Hwats $$ [Hp Hlbk]
      · iunfold watcherOwn'
        iexists wv
        iframe
        iframe #
        ipureintro; exact Hok
      wp_for_post
      iframe
      iexists j + W64 1, wid
      iframe
      ipureintro; constructor <;> word
  · rw [decide_eq_false Hlt]; simp only [Bool.false_eq_true, ↓reduceIte]
    (try wp_auto)
    wp_apply sync.Mutex.wp_Unlock (sF go!"mu" T.s) (smuInv T)
      $$ [$Hmu $Hlocked Hwm Hord Hids Hcap Hevl Hreg Hrcv0 Hwats]
    · iunfold smuInv
      iexists rs0, W, Hl, P
      iunfold smuBody
      iframe
      iframe #
      inext; ipureintro; exact ⟨Hids, Hknown⟩
    (try wp_auto)
    iapply HΦ
    iframe

end proof

end mvccfull
end EtcdGrove
end Perennial
