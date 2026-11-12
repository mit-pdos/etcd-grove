/-
U6x (`notes/bbolt-proof-plan.md`, "Writer reads at a fraction"): what a writer's `Bucket.Get` at a
fraction needs. Pure: a handle's bucket's data is the `GMap.ofList` of its logical entries
(`wdata_bkt`), and the entry `seek` returns decides the lookup of the key (`wget_lookup`, from
`lRoutes_found'` and `route_found_at`); a writer's bucket is searchable (`bktLocalOK_of_wOK`,
`pmFresh_of_wOK`). Separation: `wtxWQ`'s statistics token, a handle's registry entry, and a key
read together with a live slice.
-/
module

public import Proof.go_etcd_io.bbolt.Read.WQ
public import Proof.go_etcd_io.bbolt.Read.WKey
public import Proof.go_etcd_io.bbolt.Read.WOpenOK
public import Proof.go_etcd_io.bbolt.Write.DataBkt
public import Proof.go_etcd_io.bbolt.Write.Data
public import Proof.go_etcd_io.bbolt.Read.TreeEnts

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace PubW

section pure
variable [GooseExts]

theorem ofList_isSome_of_mem {K V : Type} [DecidableEq K] :
    ∀ (L : List (K × V)) (k : K) (v : V), (k, v) ∈ L → ((GMap.ofList L) !! k).isSome
  | [], _, _, h => by cases h
  | (a1, a2) :: L, k, v, h => by
    simp only [GMap.ofList, GMap.lookup_insert_eq_iff]
    split
    · rfl
    · rename_i hk
      rcases List.mem_cons.1 h with e | h'
      · cases e; exact absurd rfl hk
      · exact ofList_isSome_of_mem L k v h'

theorem mem_lbktEnts (X : WX) (bl : Loc) (k v : List w8) :
    (k, v) ∈ lbktEnts X bl ↔
      ∃ w ∈ X.allEnts bl, ¬ isBktFlag w.flags ∧ w.key = k ∧ w.value = v := by
  unfold lbktEnts WX.allEnts
  simp only [List.mem_flatMap, List.mem_filterMap, List.mem_flatten]
  constructor
  · rintro ⟨ws, hws, w, hw, he⟩
    by_cases hf : isBktFlag w.flags
    · simp [hf] at he
    · simp only [hf, decide_false, Bool.false_eq_true, ↓reduceIte, Option.some.injEq,
        Prod.mk.injEq] at he
      exact ⟨w, ⟨ws, hws, hw⟩, hf, he.1, he.2⟩
  · rintro ⟨w, ⟨ws, hws, hw⟩, hf, rfl, rfl⟩
    exact ⟨ws, hws, w, hw, by simp [hf]⟩

/-- **The lookup `Get` computes**: on a searchable bucket, after a search for `kb`, the bucket's
plain entries hold `kb` exactly when the entry at the leaf's search index has key `kb` and is no
bucket, with that entry's value. -/
theorem wget_lookup (X : WX) (bl : Loc) (els : List elemRef) (pids : List w64) (kb : List w8)
    (hb : bktLocalOK X bl) (hp : lPath X bl els pids) (hr : lRoutes X bl els pids kb) :
    (GMap.ofList (lbktEnts X bl)) !! kb =
      match (lLeaf X bl pids)[wsIdx (lLeaf X bl pids) kb]? with
      | some w => if w.key = kb ∧ ¬ isBktFlag w.flags then some w.value else none
      | none => none := by
  cases hl : (GMap.ofList (lbktEnts X bl)) !! kb with
  | some v =>
    obtain ⟨w, hw, hnb, hk, hv⟩ :=
      (mem_lbktEnts X bl kb v).1 (TreeEnts.ofList_mem _ _ _ hl)
    rw [WOpen.route_found_at X bl els pids kb hb hp hr w hw hk]
    simp only [hk, hnb, not_false_eq_true, and_self, ↓reduceIte, hv]
  | none =>
    cases hw : (lLeaf X bl pids)[wsIdx (lLeaf X bl pids) kb]? with
    | none => rfl
    | some w =>
      simp only
      by_cases h : w.key = kb ∧ ¬ isBktFlag w.flags
      · exfalso
        have hf : wsFound (lLeaf X bl pids) kb := by
          unfold wsFound; rw [hw]; simp [h.1]
        obtain ⟨w', hw', hk'⟩ := (lRoutes_found' X bl els pids kb hb hp hr).2 hf
        have := WOpen.route_found_at X bl els pids kb hb hp hr w' hw' hk'
        rw [hw] at this
        cases this
        have hm := (mem_lbktEnts X bl kb w.value).2 ⟨w, hw', h.2, h.1, rfl⟩
        have := ofList_isSome_of_mem _ _ _ hm
        rw [hl] at this; cases this
      · rw [if_neg h]

/-- **A handle's bucket's data** is its logical entries'. -/
theorem wdata_bkt (X : WX) (n : GoString) (bl : Loc) (m : BktData) (hb : bktLoc X n = some bl)
    (hm : (wtxData X) !! n = some m) : m = GMap.ofList (lbktEnts X bl) := by
  rw [Write.wtxData_lookup] at hm
  unfold bktData at hm
  cases hf : (rootEnts X).find? (fun e => decide (e.1 = n)) with
  | none => rw [hf] at hm; cases hm
  | some e =>
    rw [hf] at hm
    simp only [Option.map_some, Option.some.injEq] at hm
    rw [← hm, Write.bktDataOf_eq, hb]

/-- An opened top-level bucket has a record. -/
theorem bktLoc_rec (X : WX) (hok : wOK X) (n : GoString) (bl : Loc) (hb : bktLoc X n = some bl) :
    ∃ B, X.t.bs !! bl = some B := by
  unfold bktLoc at hb
  cases hR : X.t.bs !! X.rl with
  | none => rw [hR] at hb; cases hb
  | some R =>
    rw [hR] at hb
    simp only [Option.bind_some] at hb
    exact Option.isSome_iff_exists.1 ((hok.1.2.2.2.2.2 X.rl R hR).2 n bl hb)

/-- **Every bucket of a `wOK` writer can be searched.** -/
theorem bktLocalOK_of_wOK (X : WX) (hok' : wOK X) (c : Loc) (C : BRec)
    (hC : X.t.bs !! c = some C) : bktLocalOK X c := by
  have hok := wOK_wOKR X hok'
  refine ⟨hok.2.2.2.2.2.1.2.2.1 c C hC, C, hC, (hok.1.2.2.2.2.2 c C hC).1, (hok.2.1 c C hC).1,
    ?_, fun l r hr => wOKR_nsLive X hok c C l r hC hr, hok.2.2.2.2.2.2.2⟩
  intro bl B hB
  simp at hB
  obtain ⟨rfl, rfl⟩ := hB
  exact hok.2.2.1 _ _ hC

/-- A `wOK` writer's page cache is empty. -/
theorem pmFresh_of_wOK (X : WX) (hok : wOK X) : pmFresh X := by
  intro id h
  rw [hok.1.2.1.1] at h
  simp at h

end pure

end PubW

section wq
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **The statistics token** (with the core and the registration) out of `wtxWQ`, and back. -/
theorem wtxWQ_stats_acc (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (q : Qp) (X : WX) :
    wtxWQ (GF := GF) K tx r m q X ⊢ K.core ∗ reg tx K.B r ∗ statsTok r m q ∗
      (statsTok r m q -∗ wtxWQ K tx r m q X) := by
  unfold wtxWQ wtxCoreQ
  iintro ⟨⟨#Hpkg, #Hcore, %Hr, #Hreg, Hh, Hfills, Hbk, Hnl, Hdb, Hview, Hst⟩, Hcells, Hmap⟩
  iframe Hst; iframe Hcore; iframe Hreg
  iintro Hst
  iframe; iframe #
  ipureintro; exact Hr

/-- **A handle's registry entry**: a writer's registration and handle fragment agree with `wtxWQ`
(the same registration; the handle is in `X.handles`). -/
theorem wtxWQ_handle (K : BC) (tx : Loc) (r r' : TxReg) (m : Bool) (q : Qp) (X : WX) (b : Loc)
    (n : GoString) (g : Nat) :
    wtxWQ (GF := GF) K tx r m q X ∗ reg tx K.B r' ∗ handleFrag r' b n g ⊢
      wtxWQ K tx r m q X ∗ ⌜r' = r ∧ X.handles !! b = some (n, g)⌝ := by
  unfold handleFrag
  unfold wtxWQ wtxCoreQ hdlAuth
  iintro ⟨⟨⟨#Hpkg, #Hcore, %Hr, #Hreg, Hh, Hfills, ⟨Hbk, #Hf⟩, Hnl, Hdb, Hview, Hst⟩, Hcells,
    Hmap⟩, #Hreg', Hh'⟩
  iunfold reg at Hreg Hreg'
  icombine Hreg Hreg' gives %hr
  obtain ⟨-, rfl⟩ := hr
  rw [if_pos Hr.2.1]
  ihave %Hl := ghost_map_lookup $$ Hbk Hh'
  isplitl
  · iframe; iframe #
    isplitr
    · ipureintro; exact Hr
    unfold reg; iexact Hreg
  ipureintro; exact ⟨rfl, Hl⟩

/-- **A key and a live slice's bytes, read together** out of `wtxWQ`, and back. -/
theorem wtxWQ_keyR_src_acc (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (q : Qp) (X : WX)
    (key : GoSlice) (kr : KeyR) (kb : List w8) (s : GoSlice) (sr : Src) (bs : List w8)
    (hs : sr ≠ Src.stale) :
    wtxWQ (GF := GF) K tx r m q X ∗ keyR X.v key kr kb ∗ srcOwn X.v s sr bs ⊢
      ∃ d1 d2 : DFrac, key ↦*{d1} kb ∗ s ↦*{d2} bs ∗
        (key ↦*{d1} kb -∗ s ↦*{d2} bs -∗ wtxWQ K tx r m q X ∗ keyR X.v key kr kb) := by
  iintro ⟨Hw, Hk, #Hs⟩
  icases wtxWQ_cells_acc K tx r m q X $$ Hw with ⟨%Hbase, Hc, Hwb⟩
  icases (viewCells_halves (QpMul q wq) X.v).1 $$ Hc with ⟨Hc1, Hc2⟩
  icases keyR_cells_acc (QpMul q wq).half X.v Hbase key kr kb $$ [Hk Hc1] with ⟨%d1, H1, Hb1⟩
  · iframe
  icases viewCells_src_acc (QpMul q wq).half X.v Hbase s sr bs hs $$ [Hc2] with ⟨%d2, H2, Hb2⟩
  · iframe; iframe #
  iexists d1, d2
  iframe H1 H2
  iintro H1 H2
  icases Hb1 $$ H1 with ⟨Hk, Hc1⟩
  ihave Hc2 := Hb2 $$ H2
  iframe Hk
  iapply Hwb
  iapply (viewCells_halves (QpMul q wq) X.v).2
  iframe

end wq

end bbolt
end EtcdGrove
end Perennial
