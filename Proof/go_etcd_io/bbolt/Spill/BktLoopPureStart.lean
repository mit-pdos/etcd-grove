/-
`Bucket.spill`'s root loop (U9t, `notes/bbolt-proof-plan.md`): **the invariant at the start**
(`rinv_start`). Every cached child of the root not visited (`todo`): its unspilled tree
(`bk_init`) owning its slots `Dc k`, the root owning the other covered base slots (`rootOwn`,
`slotInv_start`).

`rinv_start'` is proved from the facts `StartFacts` beside the spill's pre, the
consequences of `Bucket.spill.spec`'s pure premises and `spillStartOK` (`spill_startFacts`; the
root's keys `rootKeys_start`, a `sorry`).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.BktLoopInv
public import Proof.go_etcd_io.bbolt.Spill.BktStart
public import Proof.go_etcd_io.bbolt.Spill.BktSlots

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section start
variable [GooseExts]

/-- **What the start needs beside the spill's pure premises**: the committed state's tree
well-formed, its high-water mark at most the transaction's (`beginRWTx` copies it, nothing
allocates before the spill), the transaction's mark below `2 ^ 62` (the mapping's bound,
`maxMapSize`), and the root's cached children distinct and not the root itself. -/
structure StartFacts (X : WX) (w : WDb) (B0 : BRec) : Prop where
  cok : treeOK w.C
  hwm : w.C.hwm ≤ X.t.mv.pgid'.toNat
  mark62 : X.t.mv.pgid'.toNat < 2 ^ 62
  notRoot : ∀ k c, B0.bm !! k = some c → c ≠ X.rl
  inj : ∀ k k' c, B0.bm !! k = some c → B0.bm !! k' = some c → k = k'
  rootKeys : ∀ we ∈ X.allEnts X.rl, 0 < we.key.length

/-- **The root bucket's entries' keys are not empty** (a `sorry`): `entriesBounded`'s `.1` for an
entry of a node, `posShape`'s `.2.1.1` (batch 43.4) for an entry of a view page at one of the root
bucket's positions; what is missing is the link from a block of the root's walk read from a page
(`ltree`'s `none` case) to `posShape`'s `posRoot B c ∧ ownHas X.v.pages c p` (the converse of
`BktSlotCov.pos_ownHas`). -/
theorem rootKeys_start {X : WX} {fl : FLPg} (hpre : spillPre X fl) :
    ∀ we ∈ X.allEnts X.rl, 0 < we.key.length := by
  sorry

/-- **The start's facts** (batch 43): `spillStartOK` (`Bucket.spill.spec`'s premise) gives the
committed tree, its mark, the root's children's; the mapping's bound (`wdbW_mapLen_le`) the
mark's `2 ^ 62`; `rootKeys_start` the root's keys. -/
theorem spill_startFacts {X : WX} {w : WDb} {B0 : BRec} (hpre : spillPre X w.fl)
    (hml : X.t.mv.pgid'.toNat * 4096 ≤ mapLen w.ms) (hl : mapLen w.ms ≤ 0xFFFFFFFFFFFF)
    (hS : spillStartOK X w) (hB0 : X.t.bs !! X.rl = some B0) : StartFacts X w B0 :=
  { cok := hS.1
    hwm := hS.2.1
    mark62 := by omega
    notRoot := (hS.2.2 B0 hB0).1
    inj := (hS.2.2 B0 hB0).2
    rootKeys := rootKeys_start hpre }

/-- The writer's txid at the start of the spill is its records'. -/
theorem txid_start {X : WX} {w : WDb} (hc : txClean X)
    (hw : wdbOK w ∧ w.ms = some (X.v.base, mapLen w.ms) ∧ X.v = View.ofC X.v.base w.C) :
    X.t.mv.txid' = w.wtxid := by
  have htx : X.v.txid + 1 = X.t.mv.txid'.toNat := hc.2.2.2.1
  have hv : X.v.txid = w.C.txid := by rw [hw.2.2]; rfl
  have hlt : w.C.txid + 1 < 2 ^ 64 := hw.1.2.2.2.2.2.2.1
  apply BitVec.eq_of_toNat_eq
  unfold WDb.wtxid
  rw [w64_cast_toNat hlt]
  omega

/-- **The view's pages lie below the mark at the start** (`spG`'s view clause, U9w): each page's
extent ends at most at the committed high-water mark (`treeOK`), which is at most the mark. -/
theorem view_lt_mark {X : WX} {w : WDb} {B0 : BRec} (hS : StartFacts X w B0)
    (hw : wdbOK w ∧ w.ms = some (X.v.base, mapLen w.ms) ∧ X.v = View.ofC X.v.base w.C) :
    ∀ id pg, X.v.pages !! id = some pg → id < X.t.mv.pgid'.toNat := by
  intro id pg hpg
  have hcp : X.v.pages = w.C.pages := by rw [hw.2.2]; rfl
  rw [hcp] at hpg
  have := hS.cok.2.2.2.1 id pg hpg
  have := hS.hwm
  omega

/-- A cached child of the root bucket has no bucket entry, so caches no bucket. -/
theorem child_bm_empty {X : WX} (hok : wOKR X) {c : Loc} {C : BRec}
    (hC : X.t.bs !! c = some C) (hne : c ≠ X.rl) : C.bm = ∅ := by
  apply GMap.ext
  intro k
  show C.bm !! k = (∅ : GMap GoString Loc) !! k
  rw [GMap.lookup_empty]
  cases hk : C.bm !! k with
  | none => rfl
  | some c' =>
    exfalso
    obtain ⟨-, v, -, hent, -⟩ := (hok.2.1 c C hC).2 k c' hk
    rcases hent with ⟨l, r, we, hr, hl, hw, -, hb, -⟩ | ⟨c0, p, pg, i, hpr, hown, hpg, hfl, hi, -, hf, -⟩
    · exact hne ((hok.1.2.1.2.2.1 c C hC l r hr hl we hw).1 hb)
    · exact hne ((hok.1.2.1.2.2.2.1 c C hC c0 p pg hpr hown hpg hfl i hi).1.1 hf)

/-- **A bucket of `wOKR` records can be searched.** -/
theorem bktLocalOK_of_wOKR {X : WX} (hok : wOKR X) {c : Loc} {C : BRec}
    (hC : X.t.bs !! c = some C) : bktLocalOK X c := by
  refine ⟨hok.2.2.2.2.2.1.2.2.1 c C hC, C, hC, (hok.1.2.2.2.2.2 c C hC).1, (hok.2.1 c C hC).1,
    ?_, fun l r hr => wOKR_nsLive X hok c C l r hC hr, hok.2.2.2.2.2.2.2⟩
  intro bl B hB
  simp at hB
  obtain ⟨rfl, rfl⟩ := hB
  exact hok.2.2.1 _ _ hC

/-- **The root bucket's facts at the start.** -/
theorem rootLoc_start {X : WX} {fl : FLPg} (hpre : spillPre X fl) {B0 : BRec}
    (hB0 : X.t.bs !! X.rl = some B0) : rootLoc X X.rl := by
  have hok := hpre.1
  refine ⟨bktLocalOK_of_wOKR hok hB0, hpre.2.2.2.1 X.rl (by rw [hB0]; simp), B0, hB0, ?_⟩
  intro l r hr
  exact ⟨hpre.2.1 X.rl B0 hB0 l r hr (wOKR_nsLive X hok X.rl B0 l r hB0 hr),
    fun w hw => ⟨(hok.2.2.2.1 X.rl B0 hB0 l r hr w hw).1,
      (hok.2.2.2.1 X.rl B0 hB0 l r hr w hw).2.1⟩⟩

/-- A filter dropping only keys whose slots are empty keeps the slots. -/
theorem flatMap_filter_nil {α β : Type} (p : α → Bool) (f : α → List β) (l : List α)
    (h : ∀ a ∈ l, p a = false → f a = []) : (l.filter p).flatMap f = l.flatMap f := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    have ih' := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    by_cases hp : p a = true
    · rw [List.filter_cons_of_pos hp, List.flatMap_cons, List.flatMap_cons, ih']
    · rw [List.filter_cons_of_neg hp, List.flatMap_cons, ih',
        h a List.mem_cons_self (by simpa using hp), List.nil_append]

/-- A key's child with a root node. -/
def hasRN (X : WX) (B0 : BRec) (k : GoString) : Prop :=
  ∃ c C, B0.bm !! k = some c ∧ X.t.bs !! c = some C ∧ C.bv.rootNode' ≠ null

/-- The child's unspilled tree at the start owns `D`. -/
def treeAt (X : WX) (B0 : BRec) (k : GoString) (D : List Nat) : Prop :=
  ∀ c C, B0.bm !! k = some c → X.t.bs !! c = some C → C.bv.rootNode' ≠ null →
    ∃ rn h F N E, X.node c C.bv.rootNode' = some rn ∧ rn.nv.parent' = null ∧
      uTree X c (spP X) X.t.mv.pgid'.toNat C.bv.rootNode' none none h F D N E ∧
      E.map (fun e => (e.2.1, e.2.2)) = lbktEnts X c ∧ plainEls E

/-- **The invariant at the start, from `StartFacts`.** -/
theorem rinv_start' {X : WX} {w : WDb} {B0 : BRec} (hpre : spillPre X w.fl)
    (hreach : liveReach X)
    (hml : X.t.mv.pgid'.toNat * 4096 ≤ mapLen w.ms) (hfv : flViewU X w.fl)
    (hw : wdbOK w ∧ w.ms = some (X.v.base, mapLen w.ms) ∧ X.v = View.ofC X.v.base w.C)
    (hB0 : X.t.bs !! X.rl = some B0) (keys : List GoString)
    (hk : ∀ k, k ∈ keys ↔ (B0.bm !! k).isSome) (hnd : keys.Nodup)
    (hS : StartFacts X w B0) :
    ∃ Lroot Dc, RInv X w B0 keys Lroot X w [] Dc (fun _ => .todo) := by
  classical
  have hok := hpre.1
  have htc := hok.1
  have hcp : X.v.pages = w.C.pages := by rw [hw.2.2]; rfl
  have htxid : X.t.mv.txid' = w.wtxid := txid_start htc hw
  -- each key's slots
  have hD : ∀ k, ∃ D, treeAt X B0 k D ∧ (¬ hasRN X B0 k → D = []) := by
    intro k
    by_cases hr : hasRN X B0 k
    · obtain ⟨c, C, hc, hC, hrn⟩ := hr
      have hne := hS.notRoot k c hc
      have hpage : ∀ c0 p pg, posRoot C c0 → ownHas X.v.pages c0 p → X.v.pages !! p = some pg →
          pageFlags pg = leafPageFlag → ∀ i < pageCount pg,
            leafFlags pg i % 2 = 0 ∧ 0 < leafKsize pg i ∧
              leafKsize pg i + leafVsize pg i ≤ bboltEntryMax := by
        intro c0 p pg hpr hown hpg hfl i hi
        have hs := htc.2.1.2.2.2.1 c C hC c0 p pg hpr hown hpg hfl i hi
        have h1 : leafFlags pg i % 2 ≠ bucketLeafFlag := fun e => hne (hs.1.1 e)
        unfold bucketLeafFlag at h1
        exact ⟨by omega, hs.2.1⟩
      obtain ⟨rn, h, F, D, N, E, h1, h2, h3, h4, h5⟩ :=
        bk_init hpre hreach w.C hS.cok hcp hS.hwm hfv.2.2.1 hC hne hrn hpage
      refine ⟨D, ?_, fun hn => absurd ⟨c, C, hc, hC, hrn⟩ hn⟩
      intro c' C' hc' hC' _
      rw [hc] at hc'; cases hc'; rw [hC] at hC'; cases hC'
      exact ⟨rn, h, F, N, E, h1, h2, h3, h4, h5⟩
    · refine ⟨[], fun c C hc hC hrn => absurd ⟨c, C, hc, hC, hrn⟩ hr, fun _ => rfl⟩
  let Dc : GoString → List Nat := fun k => Classical.choose (hD k)
  have hDc : ∀ k, treeAt X B0 k (Dc k) ∧ (¬ hasRN X B0 k → Dc k = []) :=
    fun k => Classical.choose_spec (hD k)
  -- the children with a root node
  let cOf : GoString → Loc := fun k => (B0.bm !! k).getD null
  let ks' := keys.filter fun k => decide (hasRN X B0 k)
  let cs : List (Loc × List Nat) := ks'.map fun k => (cOf k, Dc k)
  have hcsD : cs.flatMap Prod.snd = keys.flatMap Dc := by
    simp only [cs, ks', List.flatMap_map]
    exact flatMap_filter_nil _ Dc keys (fun a _ hp => (hDc a).2 (by simpa using hp))
  have hcsnd : (cs.map Prod.fst).Nodup := by
    simp only [cs, List.map_map]
    rw [List.Nodup, List.pairwise_map]
    refine (hnd.filter _).imp_of_mem ?_
    intro a b ha hb hab e
    apply hab
    obtain ⟨ca, Ca, hca, -⟩ := of_decide_eq_true (List.mem_filter.1 ha).2
    obtain ⟨cb, Cb, hcb, -⟩ := of_decide_eq_true (List.mem_filter.1 hb).2
    simp only [Function.comp, cOf, hca, hcb, Option.getD_some] at e
    subst e
    exact hS.inj a b ca hca hcb
  have hcs : ∀ c D, (c, D) ∈ cs → c ≠ X.rl ∧ ∃ Cc h F N E, X.t.bs !! c = some Cc ∧
      uTree X c (spP X) X.t.mv.pgid'.toNat Cc.bv.rootNode' none none h F D N E := by
    intro c D hm
    obtain ⟨k, hkm, e⟩ := List.mem_map.1 hm
    cases e
    obtain ⟨c, C, hc, hC, hrn⟩ := of_decide_eq_true (List.mem_filter.1 hkm).2
    have hco : cOf k = c := by simp only [cOf, hc, Option.getD_some]
    rw [hco]
    obtain ⟨rn, h, F, N, E, -, -, hu, -⟩ := (hDc k).1 c C hc hC hrn
    exact ⟨hS.notRoot k c hc, C, h, F, N, E, hC, hu⟩
  have hids : ∀ id ∈ w.fl.allIds, id.toNat < X.t.mv.pgid'.toNat := by
    intro id hid
    have hfree : ∀ x ∈ w.fl.free, x.toNat < w.C.hwm := hw.1.2.2.2.2.2.2.2.2.2.2.2.1
    have hsl : ∀ s, s ∈ treeSlots w.C ∨ s ∈ pendSlots w.fl → s < w.C.hwm :=
      hw.1.2.2.2.2.2.2.2.2.2.2.1
    have := hS.hwm
    unfold FLPg.allIds at hid
    rcases List.mem_append.1 hid with h | h
    · have := hfree id h; omega
    · have := hsl id.toNat (Or.inr (List.mem_map.2 ⟨id, h, rfl⟩)); omega
  have hslots := slotInv_start hpre hreach hfv hS.cok hcp hS.hwm hids cs hcsnd hcs
  rw [hcsD] at hslots
  -- the slots owned at the start are base slots, and the base slots owned or pending
  have hcov : ∀ s ∈ keys.flatMap Dc, coversSlot X.v.pages s := by
    intro s hs
    rw [← hcsD] at hs
    obtain ⟨⟨c, D⟩, hcD, hsD⟩ := List.mem_flatMap.1 hs
    obtain ⟨hne, Cc, h, F, N, E, hc, hu⟩ := hcs c D hcD
    exact ((uTree_start_cov hpre hreach hfv hc hne hu).2 s hsD).1
  refine ⟨rootOwn X (keys.flatMap Dc), Dc, ?_⟩
  exact {
    C := rfl
    fl := rfl
    pages := rfl
    rl := rfl
    mark := Nat.le_refl _
    G := ⟨htxid, hml, wOKR_derefPre X hok, wOKR_liveFresh X hok, hreach,
      fun id => by rw [htc.2.1.1, htc.2.1.2.1]; rfl, hS.mark62,
      (fun id h => by rw [htc.2.1.2.1] at h; cases h), view_lt_mark hS hw⟩
    root := ⟨B0, hB0, rfl, rfl⟩
    rootOK := rootLoc_start hpre hB0
    rootIb := fun B hB => by rw [hB0] at hB; cases hB; rfl
    slots := hslots
    base := by
      intro s hs
      have hc : coversSlot X.v.pages s := by
        rw [hcp]; exact mem_pagesSlots_cov.1 hs
      rcases hpre.2.2.2.2 s hc with hl | hp
      · left
        by_cases hD : s ∈ keys.flatMap Dc
        · exact List.mem_append_right _ hD
        · exact List.mem_append_left _ (mem_rootOwn.2 ⟨hc, hl, hD⟩)
      · exact Or.inr hp
    new := by
      intro s hs
      left
      show s ∈ pagesSlots w.C.pages
      rw [← hcp]
      apply mem_pagesSlots_cov.2
      rcases List.mem_append.1 hs with h | h
      · exact (mem_rootOwn.1 h).1
      · exact hcov s h
    agree := fun _ _ => rfl
    kids := by
      intro k c hc
      show childTodo X X w w.wtxid c (Dc k)
      have hne := hS.notRoot k c hc
      obtain ⟨C, hC⟩ := Option.isSome_iff_exists.1 ((htc.2.2.2.2.2 X.rl B0 hB0).2 k c hc)
      refine ⟨C, hC, hok.2.2.2.2.2.1.2.2.1 c C hC, child_bm_empty hok hC hne, hne,
        fun _ => bktLocalOK_of_wOKR hok hC, hpre.2.2.2.1 c (by rw [hC]; simp), rfl, ?_, ?_⟩
      · intro hn
        exact ⟨(hDc k).2 (fun ⟨c', C', hc', hC', hrn⟩ => by
          rw [hc] at hc'; cases hc'; rw [hC] at hC'; cases hC'; exact hrn hn), C, hC, hn⟩
      · intro hn
        obtain ⟨rn, h, F, N, E, h1, h2, h3, h4, h5⟩ := (hDc k).1 c C hc hC hn
        refine ⟨rn, h, F, N, E, h1, h2, h3, ?_, h4, h5⟩
        rw [← htxid]
        exact spFree_start htc hfv.1.2.1 (uTree_F_view h3)
    ents := by
      show rootEnts X = (rootEnts X).map fun e => (e.1, e.2)
      rw [List.map_id']
    keysAll := fun k h => (hk k).2 h
    rootPg := htc.2.1.2.2.2.2 B0 hB0
    entKeys := hS.rootKeys
    inj := hS.inj
    cok := hS.cok
    bufs := fun id pg h => by rw [htc.2.1.2.1, GMap.lookup_empty] at h; cases h }

/-- **The invariant at the start**: every child not visited, the root's own slots `rootOwn`
(U9p's `slotInv_start`), each child's its `bk_init` tree's. -/
theorem rinv_start {X : WX} {w : WDb} {B0 : BRec} (hpre : spillPre X w.fl) (hreach : liveReach X)
    (hml : X.t.mv.pgid'.toNat * 4096 ≤ mapLen w.ms) (hfv : flViewU X w.fl)
    (hw : wdbOK w ∧ w.ms = some (X.v.base, mapLen w.ms) ∧ X.v = View.ofC X.v.base w.C)
    (hB0 : X.t.bs !! X.rl = some B0) (keys : List GoString)
    (hk : ∀ k, k ∈ keys ↔ (B0.bm !! k).isSome) (hnd : keys.Nodup)
    (hl : mapLen w.ms ≤ 0xFFFFFFFFFFFF) (hS : spillStartOK X w) :
    ∃ Lroot Dc, RInv X w B0 keys Lroot X w [] Dc (fun _ => .todo) :=
  rinv_start' hpre hreach hml hfv hw hB0 keys hk hnd (spill_startFacts hpre hml hl hS hB0)

end start

end Spill

end bbolt
end EtcdGrove
end Perennial
