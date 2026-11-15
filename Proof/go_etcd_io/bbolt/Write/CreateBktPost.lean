/-
U7j (`notes/bbolt-proof-plan.md`): **`CreateBucket`'s records' post before the open**, pure (as
U7i's `putPost` for `Put`): from the writer's records `X` (its `boltTx` facts), the
materializations `matGrow X X3 X.rl` of the search's path, and the put of the empty inline bucket
`createEnt kb ib` into the root leaf `l` where the absent name `kb` lands, the records
`X4 = X3.setNode X.rl l …` are `wOK`, hold the data with the empty bucket `kb`, keep `gensOK`,
`wrFacts` and what the exclusive part keeps (`XclKeep`: the view, the meta copy, `flViewU`).
`b.Bucket(newKey)` then opens it (`bktOpened`: U6x's `gensOK_bktOpened`, `wrFacts_bktOpened`,
`flViewU_bktOpened_root`).
-/
module

public import Proof.go_etcd_io.bbolt.Write.WOkLeafPut
public import Proof.go_etcd_io.bbolt.Write.CreateBktOK
public import Proof.go_etcd_io.bbolt.Write.CreateBktFl

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt


namespace Write

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section createbktpost
variable [GooseExts]

/-- `c.node().put(newKey, newKey, value, 0, BucketLeafFlag)`'s entry (`CreateBucket`): a bucket
entry, no child page, the empty bucket's value, its key and value persistent heap bytes. -/
def createEnt (kb : List w8) (ib : InBucket) : WEntry :=
  ⟨W32 1, W64 0, kb, emptyBktVal ib, Src.own DFrac.discard, Src.own DFrac.discard⟩

theorem createEnt_flag (kb : List w8) (ib : InBucket) : isBktFlag (createEnt kb ib).flags := by
  show W32 1 &&& W32 1 ≠ W32 0; decide

/-- A name absent from the data has no root entry. -/
theorem rootEnts_none (X : WX) (n : GoString) (h : (wtxData X) !! n = none) :
    ∀ v, (n, v) ∉ rootEnts X := by
  intro v hv
  rw [wtxData_lookup] at h
  unfold bktData at h
  cases hf : (rootEnts X).find? (fun e => decide (e.1 = n)) with
  | none => have := List.find?_eq_none.1 hf _ hv; simp at this
  | some e => rw [hf] at h; cases h

/-- **`CreateBucket`'s post before the open** (see the module doc). -/
theorem createPost (T : TxView) (X X3 : WX) (kb : List w8) (ib : InBucket) (l : Loc) (B3 : BRec)
    (rl : NRec) (s : GoSlice) (ins : List Inode)
    (hok : wOK X) (hcur : T.cur = wtxData X) (hgens : gensOK T X) (hwr : wrFacts X)
    (hmg : matGrow X X3 X.rl) (hok3 : wOK X3) (hd3 : objsDisj X3.t)
    (hB3 : X3.t.bs !! X.rl = some B3) (hrl : B3.ns !! l = some rl) (hlf : leafFor X3 X.rl kb l)
    (hnew : T.cur !! kb = none) (hk : 0 < kb.length) (hkm : kb.length ≤ maxKeySize)
    (h0 : ib.root' = W64 0)
    (hins : ins.length = (wsPutAt rl.ws kb (createEnt kb ib)).length) :
    wOK (X3.setNode X.rl l (rl.withEnts s ins (wsPutAt rl.ws kb (createEnt kb ib)))) ∧
      wtxData (X3.setNode X.rl l (rl.withEnts s ins (wsPutAt rl.ws kb (createEnt kb ib)))) =
        T.cur.insert kb ∅ ∧
      gensOK T (X3.setNode X.rl l (rl.withEnts s ins (wsPutAt rl.ws kb (createEnt kb ib)))) ∧
      wrFacts (X3.setNode X.rl l (rl.withEnts s ins (wsPutAt rl.ws kb (createEnt kb ib)))) ∧
      XclKeep X (X3.setNode X.rl l (rl.withEnts s ins (wsPutAt rl.ws kb (createEnt kb ib)))) := by
  let e := createEnt kb ib
  let r' := rl.withEnts s ins (wsPutAt rl.ws kb e)
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8⟩ := matGrow_keepW hmg
  obtain ⟨B0, r0, bnd, hB0, hr0, hlf0, hbk, hkin⟩ := id hlf
  rw [hB3] at hB0; cases hB0; rw [hrl] at hr0; cases hr0
  have hpw : wsPw rl.ws :=
    wsSorted_pw _ ((wOK_bktClean X3 hok3 X.rl B3 hB3).2.2.2.2.2.2.2.1 l rl hrl).2.2.2.1
  have hput : wsPutAt rl.ws kb e = wsPut rl.ws e := wsPutAt_wsPut rl.ws e hpw
  have hdata3 : wtxData X3 = wtxData X := wtxData_matGrow X X3 X.rl hok hmg
  have hnew3 : (wtxData X3) !! kb = none := by rw [hdata3, ← hcur]; exact hnew
  have hnone3 := rootEnts_none X3 kb hnew3
  have hloc3 : bktLoc X3 kb = none := by
    cases h : bktLoc X3 kb with
    | none => rfl
    | some c =>
      obtain ⟨v, hv⟩ := bktLoc_rootEnt X3 hok3 kb c h
      exact absurd hv (hnone3 v)
  have hrl3 : X3.rl = X.rl := k2
  have hB3' : X3.t.bs !! X3.rl = some B3 := by rw [hrl3]; exact hB3
  have hnr3 : ∀ k c, B3.bm !! k = some c → c ≠ X3.rl := by
    intro k c hkc
    obtain ⟨B, hB, hbm⟩ := k8 X.rl B3 hB3
    rw [hrl3]; exact hwr.2.2 B hB k c (by rw [← hbm]; exact hkc)
  have hlf3 : leafFor X3 X3.rl e.key l := by rw [hrl3]; exact hlf
  -- the root's opened buckets are not the root
  have hnrL : ∀ m c, bktLoc X3 m = some c → c ≠ X3.rl := by
    intro m c h
    unfold bktLoc at h; rw [hB3'] at h; simp only [Option.bind_some] at h
    exact hnr3 m c h
  -- wOK
  have hok4 : wOK (X3.setNode X3.rl l r') :=
    wOK_createPut X3 l B3 rl e ib s ins hok3 hd3 hlf3 hB3' hrl hloc3 hnr3 hk hkm
      (createEnt_flag kb ib) rfl h0 rfl (by simp [e, createEnt]) rfl hins
  rw [hrl3] at hok4
  refine ⟨hok4, ?_, ?_⟩
  · -- the data
    rw [wtxData_setNode X3 X.rl l B3 rl r' hB3 hrl rfl]
    show wtxData (X3.withWs X.rl l (wsPutAt rl.ws kb e)) = _
    rw [hput, ← hrl3]
    rw [wtxData_createPut X3 l B3 rl bnd e hok3 hB3' hrl hlf0 hbk hkin (createEnt_flag kb ib) hloc3
      (emptyBktVal_data _ ib h0) hnrL, hdata3, ← hcur]
    rfl
  · -- gensOK, wrFacts, XclKeep: as U7i's `post_common`, `flViewU` by `flViewU_createPut`
    have hX4 := setNode_eqT X3 X.rl l B3 r' hB3
    have hh4 : (X3.setNode X.rl l r').handles = X.handles := by rw [hX4]; exact k1
    have hrl4 : (X3.setNode X.rl l r').rl = X.rl := by rw [hX4]; exact k2
    have hbm4 : ∀ c C, X.t.bs !! c = some C → ∃ C', (X3.setNode X.rl l r').t.bs !! c = some C' ∧
        C'.bm = C.bm := by
      intro c C hC
      obtain ⟨C3, hC3, e'⟩ := k7 c C hC
      rw [hX4]
      by_cases ec : c = X.rl
      · subst ec; rw [hB3] at hC3; cases hC3
        exact ⟨_, GMap.lookup_insert _ _ _, e'⟩
      · exact ⟨C3, by show (X3.t.bs.insert X.rl _) !! c = _; rw [GMap.lookup_insert_ne _ _ (Ne.symm ec)]; exact hC3, e'⟩
    have hbm4' : ∀ c C', (X3.setNode X.rl l r').t.bs !! c = some C' → ∃ C, X.t.bs !! c = some C ∧
        C'.bm = C.bm := by
      intro c C' hC'
      rw [hX4] at hC'
      have hC'' : (X3.t.bs.insert X.rl { B3 with ns := B3.ns.insert l r' }) !! c = some C' := hC'
      by_cases ec : c = X.rl
      · subst ec; rw [GMap.lookup_insert] at hC''; cases hC''
        exact k8 _ B3 hB3
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm ec)] at hC''
        exact k8 c C' hC''
    have hloc4 : ∀ n, bktLoc (X3.setNode X.rl l r') n = bktLoc X n := by
      intro n
      unfold bktLoc
      rw [hrl4]
      cases hR : X.t.bs !! X.rl with
      | none =>
        cases hR' : (X3.setNode X.rl l r').t.bs !! X.rl with
        | none => rfl
        | some R' =>
          obtain ⟨R, hR0, -⟩ := hbm4' _ R' hR'
          rw [hR] at hR0; cases hR0
      | some R =>
        obtain ⟨R', hR', e'⟩ := hbm4 _ R hR
        rw [hR']; simp only [Option.bind_some]; rw [e']
    have hX4t : (X3.setNode X.rl l r').t.t = X.t.t := by rw [hX4]; exact k4
    obtain ⟨e1, e2, e3, e4, e5, e6, e8, e9, e10, e11⟩ := sameShapeU_withEnts rl s ins (wsPutAt rl.ws kb e)
    refine ⟨gensOK_congr T X _ hh4 hloc4 hgens, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, fun fl hfl => ?_⟩⟩
    · exact liveReach_setNode X3 X.rl l B3 rl r' hB3 hrl e6 e8 (liveReach_matGrow hmg hok hwr.1)
    · rw [hX4t]; exact hwr.2.1
    · intro C hC k c hk'
      rw [hrl4] at hC ⊢
      obtain ⟨C0, hC0, e'⟩ := hbm4' _ C hC
      exact hwr.2.2 C0 hC0 k c (by rw [← e']; exact hk')
    · rw [hX4]; exact k3
    · rw [hX4]; exact k5
    · have h3 := flViewU_matGrow X X3 fl X.rl hok hmg hfl
      have hY := flViewU_createPut X3 l B3 rl bnd e ib hok3 hB3' hrl hlf0 hbk hkin
        (createEnt_flag kb ib) rfl h0 hnone3 fl h3
      rw [hrl3] at hY
      apply flViewU_setNode_of_withWs X3 fl X.rl l B3 rl r' hB3 hrl e5 e3
      show flViewU (X3.withWs X.rl l (wsPutAt rl.ws kb e)) fl
      rw [hput]; exact hY

end createbktpost

end Write

end bbolt
end EtcdGrove
end Perennial
