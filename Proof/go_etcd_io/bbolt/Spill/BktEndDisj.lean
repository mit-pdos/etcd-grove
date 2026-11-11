/-
`Bucket.spill`'s root loop's end (U9x9, `notes/bbolt-proof-plan.md`): **where the root's
entries' nested slots are** at the loop's end (`ent_class`) and **the global disjointness of the
root tree's pieces** (`end_gdisj`, `BktEndPieces.GDisj`). A root entry `(k, v)` at the end is the
start's `(k, v0)` with the loop's value (`RInv.ents`): a put child's new value, whose slots are
`Dc k`; or the old value (a child skipped, `nilc`, or a bucket not opened), whose slots are the
root's own (`Lroot`), covered at the start by the child's positions (`nilBkt_coverW`) or by the
unopened bucket (`coverW .bkt`). A position's slot at the end is a root position's at the start
(`RInv.rootExt`), the root's own. Owned slots are distinct (`RInv.slots`), and a slot is covered
once at the start (`covU`).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.BktEndPieces
public import Proof.go_etcd_io.bbolt.Spill.BktEndKeys
public import Proof.go_etcd_io.bbolt.Spill.BktEndRootLeaf
public import Proof.go_etcd_io.bbolt.Spill.BktRootKeys
public import Proof.go_etcd_io.bbolt.Spill.BktVal
public import Proof.go_etcd_io.bbolt.Spill.BktEndInit
public import Proof.go_etcd_io.bbolt.Spill.BktEndNil
public import Proof.go_etcd_io.bbolt.Spill.BktEndOwn

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section disj
variable [GooseExts]

/-- A leaf page's entry `i`, as the walk reads it. -/
theorem pageW_leaf_eq {pg : List w8} (hlf : pageFlags pg = leafPageFlag) (i : Nat) :
    pageW pg i = ⟨W32 (leafFlags pg i : Int), W64 0, leafKey pg i, leafValue pg i,
      Src.view, Src.view⟩ := by
  simp [pageW, hlf]

/-- A leaf page's entry read as a bucket is a bucket entry of the page. -/
theorem pageW_bkt {pg : List w8} (hlf : pageFlags pg = leafPageFlag) {i : Nat}
    (hbk : isBktFlag (pageW pg i).flags) : leafFlags pg i % 2 = bucketLeafFlag := by
  rw [pageW_leaf_eq hlf] at hbk
  have := (isBkt_iff _).1 hbk
  have hl := leafFlags_lt pg i
  have e : (W32 (leafFlags pg i : Int)).toNat = leafFlags pg i := by
    simp only [BitVec.toNat_ofInt]; omega
  rw [e] at this
  unfold bucketLeafFlag
  omega

/-- **Where a walk's leaf entry is**: in a leaf node, or a leaf page under a page position. -/
theorem walk_entryR {X : WX} {bl : Loc} {B : BRec} {hwm : Nat} (hB : X.t.bs !! bl = some B)
    (hcl : bktClean X.v hwm bl B) (h0 : B.ib.root' ≠ W64 0) :
    ∀ n pid, walkInv X B pid → ∀ ws ∈ lleaves (ltree X) bl n pid, ∀ we ∈ ws,
      (∃ l r, B.ns !! l = some r ∧ r.nv.isLeaf' = true ∧ we ∈ r.ws) ∨
      (∃ c p pg i, posRoot B c ∧ ownHas X.v.pages c p ∧ X.v.pages !! p = some pg ∧
        pageFlags pg = leafPageFlag ∧ i < pageCount pg ∧ we = pageW pg i) := by
  intro n
  induction n with
  | zero => intro pid _ ws hws; simp [lleaves] at hws
  | succ n ih =>
    intro pid hinv ws hws we hwe
    unfold lleaves at hws
    cases hres : resolve B pid with
    | some l =>
      have hL : ltree X bl pid = (B.ns !! l).map (fun r => (r.nv.isLeaf', r.ws)) := by
        unfold ltree; rw [hB]; simp only [hres]
      rw [hL] at hws
      cases hr : B.ns !! l with
      | none => rw [hr] at hws; simp at hws
      | some r =>
        rw [hr] at hws
        simp only [Option.map_some] at hws
        cases hlf : r.nv.isLeaf' with
        | true =>
          rw [hlf] at hws
          simp only [List.mem_singleton] at hws
          subst hws
          exact Or.inl ⟨l, r, hr, hlf, hwe⟩
        | false =>
          rw [hlf] at hws
          obtain ⟨w, hw, hws'⟩ := List.mem_flatMap.1 hws
          exact ih w.pgid (walkInv_node h0 hr hlf hw) ws hws' we hwe
    | none =>
      obtain ⟨c, hc, hto⟩ : ∃ c, posRoot B c ∧ ownTo X.v.pages c pid.toNat := by
        rcases hinv with h | h
        · rw [hres] at h; cases h
        · exact h
      cases hp : X.v.pages !! pid.toNat with
      | none =>
        have hL : ltree X bl pid = none := by
          unfold ltree wpageAt; rw [hB]; simp only [hres]; rw [if_neg h0, hp]; rfl
        rw [hL] at hws; simp at hws
      | some pg =>
        have hL : ltree X bl pid = some (decide (pageFlags pg = leafPageFlag), pageWs pg) := by
          unfold ltree wpageAt; rw [hB]; simp only [hres]; rw [if_neg h0, hp]; rfl
        rw [hL] at hws
        have hown := ownTo_ownHas hto hp
        have hpt : pageTreeWF X.v.pages hwm pg pg.length := by
          rcases treeWF_ownHas hown (posRoot_treeWF hcl hc) with ⟨_, pg', _, _, hpg', _, _, hpt⟩
          rw [hp] at hpg'; cases hpg'; exact hpt
        by_cases hfl : pageFlags pg = leafPageFlag
        · rw [decide_eq_true hfl] at hws
          simp only [List.mem_singleton] at hws
          subst hws
          obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hwe
          rw [List.mem_range] at hi
          exact Or.inr ⟨c, pid.toNat, pg, i, hc, hown, hp, hfl, hi, rfl⟩
        · rw [decide_eq_false hfl] at hws
          obtain ⟨w, hw, hws'⟩ := List.mem_flatMap.1 hws
          obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hw
          rw [List.mem_range] at hi
          have hbr : pageFlags pg = branchPageFlag := by
            rcases mat_kind hpt with ⟨h, -⟩ | ⟨h, -⟩
            · exact absurd h hfl
            · exact h
          refine ih _ ?_ ws hws' we hwe
          by_cases hs : (resolve B (pageW pg i).pgid).isSome
          · exact Or.inl hs
          · refine Or.inr ⟨c, hc, Or.inr ⟨pid.toNat, pg, i, hown, hp, hbr, hi, ?_⟩⟩
            rw [pageW_pgid_branch pg i hbr, rp_cast_toNat (Write.branchPgid_lt pg i)]

/-- The root position satisfies `walkInv`. -/
theorem walkInv_root {X : WX} {bl : Loc} {B : BRec} {hwm : Nat} (hcl : bktClean X.v hwm bl B)
    (h0 : B.ib.root' ≠ W64 0) : walkInv X B B.ib.root' := by
  by_cases hs : (resolve B B.ib.root').isSome
  · exact Or.inl hs
  · right
    have hrn : B.bv.rootNode' = null := by
      apply Classical.byContradiction
      intro hne
      apply hs
      unfold resolve; rw [if_neg h0, hcl.2.2.2.1 hne]; rfl
    exact ⟨_, Or.inl ⟨hrn, h0, rfl⟩, Or.inl rfl⟩

/-- **Where a root entry is** (`walk_entryR` from the root position). -/
theorem rootEnt_src {X : WX} {B : BRec} {hwm : Nat} (hB : X.t.bs !! X.rl = some B)
    (hcl : bktClean X.v hwm X.rl B) (h0 : B.ib.root' ≠ W64 0) {k v : List w8}
    (he : (k, v) ∈ rootEnts X) :
    ∃ we ∈ X.allEnts X.rl, isBktFlag we.flags ∧ we.key = k ∧ we.value = v ∧
      ((∃ l r, B.ns !! l = some r ∧ r.nv.isLeaf' = true ∧ we ∈ r.ws) ∨
      (∃ c p pg i, posRoot B c ∧ ownHas X.v.pages c p ∧ X.v.pages !! p = some pg ∧
        pageFlags pg = leafPageFlag ∧ i < pageCount pg ∧ we = pageW pg i)) := by
  obtain ⟨ws, hws, we, hwe, hbk, hk, hv⟩ := mem_rootEnts_leaf he
  have hrp : X.rootPid X.rl = B.ib.root' := by unfold WX.rootPid; rw [hB]; rfl
  refine ⟨we, List.mem_flatten.2 ⟨ws, hws, hwe⟩, hbk, hk, hv, ?_⟩
  unfold WX.leaves at hws; rw [hrp] at hws
  exact walk_entryR hB hcl h0 _ _ (walkInv_root hcl h0) ws hws we hwe

/-- **A slot not covered by a cached child's position with a root node is not in the
children's starting slots** (`BktEndOwn.not_mem_Dc0`, a child without one allowed). -/
theorem not_mem_Dc0' {X0 : WX} {w0 : WDb} {B0 : BRec} {keys : List GoString}
    {Dc0 : GoString → List Nat} (hpre : spillPre X0 w0.fl) (hreach : liveReach X0)
    (hfv : flViewU X0 w0.fl) (hk : ∀ k, k ∈ keys ↔ (B0.bm !! k).isSome)
    (hDc0 : ∀ k c, B0.bm !! k = some c → childTodo X0 X0 w0 w0.wtxid c (Dc0 k))
    {s : Nat} {cw : CovW} (hcw : coverW X0 s cw)
    (hno : ∀ k c pid C, B0.bm !! k = some c → X0.t.bs !! c = some C → C.bv.rootNode' ≠ null →
      cw ≠ .pos c pid) : s ∉ keys.flatMap Dc0 := by
  intro hm
  obtain ⟨k, hkm, hs⟩ := List.mem_flatMap.1 hm
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 ((hk k).1 hkm)
  obtain ⟨Cc, hCc, -, -, hne, -, -, -, hnil, hrnd⟩ := hDc0 k c hc
  by_cases hrn : Cc.bv.rootNode' = null
  · rw [(hnil hrn).1] at hs; cases hs
  · obtain ⟨rn, h, F, N, E, -, -, hu, -⟩ := hrnd hrn
    obtain ⟨pid, hpid⟩ := ((uTree_start_cov hpre hreach hfv hCc hne hu).2 s hs).2
    exact hno k c pid Cc hc hCc hrn (hfv.2.1 s _ _ hcw hpid)

section ctx
variable {X0 X : WX} {w0 w : WDb} {B0 : BRec} {keys : List GoString} {Lroot : List Nat}
  {st : List FLStep} {Dc : GoString → List Nat} {ks : GoString → KSt}

/-- The root's own slots and a child's are distinct. -/
theorem root_vs_kid (hI : RInv X0 w0 B0 keys Lroot X w st Dc ks) {s : Nat} (hs : s ∈ Lroot)
    {k : GoString} (hk : k ∈ keys) (hs' : s ∈ Dc k) : False :=
  (List.nodup_append.1 hI.slots.1).2.2 s hs s (List.mem_flatMap.2 ⟨k, hk, hs'⟩) rfl

/-- Two children's slots are distinct. -/
theorem kid_vs_kid (hI : RInv X0 w0 B0 keys Lroot X w st Dc ks) {k k' : GoString}
    (hk : k ∈ keys) (hk' : k' ∈ keys) (hne : k ≠ k') {s : Nat} (hs : s ∈ Dc k)
    (hs' : s ∈ Dc k') : False := by
  have hnd := (List.nodup_append.1 hI.slots.1).2.1
  obtain ⟨i, hi, hik⟩ := List.getElem_of_mem hk
  obtain ⟨j, hj, hjk⟩ := List.getElem_of_mem hk'
  have hij : i ≠ j := by intro e; subst e; exact hne (hik.symm.trans hjk)
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · exact flatMap_nodup_disj Dc keys i j k k' s hnd h (by rw [List.getElem?_eq_getElem hi, hik])
      (by rw [List.getElem?_eq_getElem hj, hjk]) hs hs'
  · exact flatMap_nodup_disj Dc keys j i k' k s hnd h (by rw [List.getElem?_eq_getElem hj, hjk])
      (by rw [List.getElem?_eq_getElem hi, hik]) hs' hs

/-- At the loop's end every iterated key is visited and put. -/
theorem ksEnd (hks : ksAt keys keys.length ks) {k : GoString} (hk : k ∈ keys) :
    ks k ≠ .todo ∧ ∀ v, ks k ≠ .val v false := by
  obtain ⟨j, hj, hjk⟩ := List.getElem_of_mem hk
  exact (hks j k (by rw [List.getElem?_eq_getElem hj, hjk])).1 hj

/-- **Where a root entry's nested slots are at the loop's end** (see the module doc). -/
theorem ent_class (hpre : spillPre X0 w0.fl) (hreach : liveReach X0) (hfv : flViewU X0 w0.fl)
    (hB0 : X0.t.bs !! X0.rl = some B0) (hk : ∀ k, k ∈ keys ↔ (B0.bm !! k).isSome)
    (hI : RInv X0 w0 B0 keys Lroot X w st Dc ks) (hks : ksAt keys keys.length ks)
    (hvC : X.v = View.ofC X.v.base w.C) {k v : List w8} (he : (k, v) ∈ rootEnts X) {s : Nat}
    (hs : bucketCovers (spP X) v s) :
    (k ∈ keys ∧ s ∈ Dc k) ∨
      ((∃ cw, coverW X0 s cw ∧ (cw = .bkt k ∨ ∃ c pid, B0.bm !! k = some c ∧ cw = .pos c pid))
        ∧ s ∈ Lroot) := by
  have hok := hpre.1
  have hcl0 : bktClean X0.v X0.t.mv.pgid'.toNat X0.rl B0 := (hok.1.2.2.2.2.2 X0.rl B0 hB0).1
  have h0 : B0.ib.root' ≠ W64 0 := hI.rootPg
  have hcp : X0.v.pages = w0.C.pages := by
    have := congrArg View.pages hvC
    simp only [View.ofC] at this
    rw [← hI.pages, this, hI.C]
  have hag : pagesLe X0.v.pages (spP X) := by
    have := spP_agree hI.G (by rw [hI.pages]; exact hfv.2.2.1); rwa [hI.pages] at this
  have hrt0 : rtOK X0 X0.rl := hpre.2.2.2.1 X0.rl (by rw [hB0]; simp)
  have h64 : ∀ p pg, X0.v.pages !! p = some pg → p < 2 ^ 64 := by
    intro p pg hp
    have := hI.cok.2.2.2.1 p pg (by rw [← hcp]; exact hp)
    have := hI.hwm0
    have := X0.t.mv.pgid'.isLt
    omega
  obtain ⟨Dc0, hL, hDc0⟩ := hI.lroot
  have he' : (k, v) ∈ (rootEnts X0).map (fun e => (e.1, (ks e.1).entVal e.2)) := hI.ents ▸ he
  obtain ⟨⟨k0, v0⟩, hm0, heq⟩ := List.mem_map.1 he'
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, hv⟩ := heq
  have hkeys : ∀ c, B0.bm !! k0 = some c → k0 ∈ keys := fun c hc => (hk k0).2 (by rw [hc]; rfl)
  obtain ⟨we, hwe, hwbk, hwk, hwv, hsrc⟩ := rootEnt_src (X := X0) hB0 hcl0 h0 hm0
  cases hst : ks k0 with
  | val v' p =>
    have hkk : k0 ∈ keys := by
      apply Classical.byContradiction; intro hn; rw [hI.notKeys k0 hn] at hst; cases hst
    cases p with
    | false => exact absurd hst ((ksEnd hks hkk).2 v')
    | true =>
      rw [hst] at hv; simp only [KSt.entVal] at hv; subst hv
      obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 ((hk k0).1 hkk)
      have hch := hI.kids k0 c hc
      rw [hst] at hch
      obtain ⟨S, hS, hD, -⟩ := hch
      obtain ⟨id, pg, hbh, hpg, h1, h2⟩ := hs
      refine Or.inl ⟨hkk, ?_⟩
      rw [hD]; exact mem_pgSlots_of ((bvalS_has hS id).1 hbh) hpg h1 h2
  | todo =>
    rw [hst] at hv; simp only [KSt.entVal] at hv; subst hv
    have hnk : B0.bm !! k0 = none := by
      cases hc : B0.bm !! k0 with
      | none => rfl
      | some c => exact absurd hst (ksEnd hks (hkeys c hc)).1
    have hwf : bucketWF X0.v.pages X0.t.mv.pgid'.toNat v0 := by
      rw [← hwv]
      rcases hsrc with ⟨l, r, hr, hl, hw⟩ | ⟨c, p, pg, i, hpr, hown, hpg, hfl, hi, rfl⟩
      · have hnc' := (hcl0.2.2.2.2.2.2.2.1 l r hr).2.2.2.2.2.2.2.2.2.2.2.1 hl we hw hwbk
        exact (hnc'.1 (by rw [hwk, hnk]; rfl)).1
      · rw [pageW_leaf_eq hfl i]
        exact bucketWF_of_leaf (treeWF_ownHas hown (posRoot_treeWF hcl0 hpr)) hpg hfl hi
          (pageW_bkt hfl hwbk)
    obtain ⟨id, pg, hbh, hpg, h1, h2⟩ := hs
    have hbv := bucketHas_of_le hag _ hbh hwf
    obtain ⟨pg', hpg'⟩ := bucketHas_page hbv
    have e := hag id pg' hpg'
    rw [hpg] at e; cases e
    have hcw : coverW X0 s (.bkt k0) :=
      ⟨v0, hm0, by unfold bktLoc; rw [hB0]; exact hnk, id, pg, hbv, hpg', h1, h2⟩
    refine Or.inr ⟨⟨_, hcw, Or.inl rfl⟩, ?_⟩
    rw [hL]; exact mem_rootOwn_bkt hpre hreach hfv hk hDc0 hcw
  | nilc =>
    rw [hst] at hv; simp only [KSt.entVal] at hv; subst hv
    have hkk : k0 ∈ keys := by
      apply Classical.byContradiction; intro hn; rw [hI.notKeys k0 hn] at hst; cases hst
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 ((hk k0).1 hkk)
    have hch := hI.kids k0 c hc
    rw [hst] at hch
    obtain ⟨-, C0, hC0, hrn0⟩ := hch
    obtain ⟨v', S, hent, hib, hS, hsl⟩ := bvalS_cachedNil hok hI.cok hcp
      (Nat.le_trans hI.hwm0 hI.mark) hag hB0 hc hC0 hrn0
    have hvv : v' = v0 := by
      rcases hent with ⟨l', r', w', hr', hl', hw', hkey, -, hval⟩ |
        ⟨c0, p, pg, i, hpr, hown, hpg, hfl, hi, hkey, -, hval⟩
      · have := allEnts_key_injR X0 hok X0.rl B0 hB0 we w' hwe
          (mem_allEnts_node hok hreach hrt0 hB0 h0 hr' hl' hw') (hwk.trans hkey.symm)
        rw [← hval, ← this, hwv]
      · have hpA := mem_allEnts_page hok hreach hrt0 hB0 h64 hpr hown hpg hfl hi
        have hk' : we.key = (pageW pg i).key := by
          rw [hwk]; simp [pageW, hfl, hkey]
        have := allEnts_key_injR X0 hok X0.rl B0 hB0 we _ hwe hpA hk'
        rw [← hval, ← hwv, this]; simp [pageW, hfl]
    subst hvv
    obtain ⟨id, pg, hbh, hpg, h1, h2⟩ := hs
    have hsS : s ∈ pgSlots (spP X) S := mem_pgSlots_of ((bvalS_has hS id).1 hbh) hpg h1 h2
    obtain ⟨id', pg', hbh', hpg', a1, a2⟩ := (hsl s).1 hsS
    have hcne : c ≠ X0.rl := by
      obtain ⟨_, _, _, _, hne, _⟩ := hDc0 k0 c hc; exact hne
    have hr0 : inBucketRoot v' ≠ 0 := by
      intro h; rcases hS.2 with ⟨-, hS0, -⟩ | ⟨h', -⟩
      · rw [hS0] at hsS; simp [pgSlots] at hsS
      · exact h' h
    have hroot : C0.ib.root'.toNat = inBucketRoot v' := by rw [hib]; rfl
    have hc0 : C0.ib.root' ≠ W64 0 := by
      intro e; rw [e] at hroot; exact hr0 (by rw [← hroot]; rfl)
    have hth : treeHas X0.v.pages C0.ib.root'.toNat id' := by
      cases hbh' with
      | file _ _ _ ht => rw [hroot]; exact ht
      | inline _ _ h _ => exact absurd h hr0
    have hclc : bktClean X0.v X0.t.mv.pgid'.toNat c C0 := (hok.1.2.2.2.2.2 c C0 hC0).1
    have hpr : posRoot C0 C0.ib.root'.toNat := Or.inl ⟨hrn0, hc0, rfl⟩
    have hown : ownHas X0.v.pages C0.ib.root'.toNat id' := by
      refine ownHas_of_treeHas (fun p pgp ho hp hfl i hi hb => ?_) hth
      exact hcne ((hok.1.2.1.2.2.2.1 c C0 hC0 _ p pgp hpr ho hp hfl i hi).1.1 hb)
    have hwfx := Read.treeHas_treeWF X0.v.pages _ hth ((hclc.2.1 hc0).2 hrn0)
    have h2x : 2 ≤ id' := by cases hwfx with | page _ _ h _ _ _ _ _ => exact h
    have hcw := nilBkt_coverW hC0 (hclc.2.2.1 hrn0).2 hc0 (hpre.2.2.2.1 c (by rw [hC0]; simp))
      hown h2x (h64 id' pg' hpg') hpg' a1 a2
    refine Or.inr ⟨⟨_, hcw, Or.inr ⟨c, _, hc, rfl⟩⟩, ?_⟩
    rw [hL]
    refine mem_rootOwn.2 ⟨⟨id', pg', hpg', a1, a2⟩, lCovers_of_coverW hcw,
      not_mem_Dc0' hpre hreach hfv hk hDc0 hcw fun k' c' pid C hc' hC hrn e => ?_⟩
    simp only [CovW.pos.injEq] at e
    obtain ⟨rfl, -⟩ := e
    rw [hC0] at hC; cases hC; exact hrn hrn0

/-- An element of a bucket's leaves that is a bucket is a root entry. -/
theorem ent_of_E0 {X : WX} {e : El}
    (he : e ∈ (X.leaves X.rl).flatMap (List.map wEl)) (hb : e.1 % 2 = 1) :
    (e.2.1, e.2.2) ∈ rootEnts X := by
  obtain ⟨ws, hws, he⟩ := List.mem_flatMap.1 he
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 he
  have hbk : isBktFlag w.flags := (isBkt_iff _).2 hb
  unfold rootEnts
  exact List.mem_flatMap.2 ⟨ws, hws, List.mem_filterMap.2 ⟨w, hw, by simp [hbk, wEl]⟩⟩

/-- **The global disjointness of the root tree's pieces at the loop's end** (see the module
doc). -/
theorem end_gdisj (hpre : spillPre X0 w0.fl) (hreach : liveReach X0) (hfv : flViewU X0 w0.fl)
    (hB0 : X0.t.bs !! X0.rl = some B0) (hk : ∀ k, k ∈ keys ↔ (B0.bm !! k).isSome)
    (hI : RInv X0 w0 B0 keys Lroot X w st Dc ks) (hks : ksAt keys keys.length ks)
    (hvC : X.v = View.ofC X.v.base w.C) :
    GDisj X X0.rl (spP X) ((X.leaves X0.rl).flatMap (List.map wEl)) := by
  obtain ⟨Dc0, hL, hDc0⟩ := hI.lroot
  have hE : ∀ e ∈ (X.leaves X0.rl).flatMap (List.map wEl), e.1 % 2 = 1 →
      (e.2.1, e.2.2) ∈ rootEnts X := fun e he hb =>
    ent_of_E0 (X := X) (by rw [hI.rl]; exact he) hb
  have hpos : ∀ s q, coverW X s (.pos X0.rl q) →
      ∃ pid, coverW X0 s (.pos X0.rl pid) ∧ s ∈ Lroot := by
    intro s q hq
    obtain ⟨-, hqp, e1, he1, h1, h2⟩ := hq
    have hmem : e1 ∈ X0.extents X0.rl := by
      rw [← hI.rootExt]; exact List.mem_filterMap.2 ⟨q, hqp, he1⟩
    obtain ⟨pid, hpid⟩ := coverW_of_extent (by rw [hB0]; simp) hmem h1 h2
    exact ⟨pid, hpid, by rw [hL]; exact mem_rootOwn_pos hpre hreach hfv hk hDc0 hpid⟩
  refine ⟨fun s q e hq he hb hc => ?_, fun s e e' he he' hne hb hb' hc hc' => ?_⟩
  · obtain ⟨pid, hpid, hsL⟩ := hpos s q hq
    rcases ent_class hpre hreach hfv hB0 hk hI hks hvC (hE e he hb) hc with
      ⟨hkk, hsD⟩ | ⟨⟨cw, hcw, hcase⟩, -⟩
    · exact root_vs_kid hI hsL hkk hsD
    · have := hfv.2.1 s _ _ hpid hcw
      rcases hcase with rfl | ⟨c, pid', hc, rfl⟩
      · cases this
      · simp only [CovW.pos.injEq] at this
        obtain ⟨_, _, _, _, hne, _⟩ := hDc0 _ c hc
        exact hne this.1.symm
  · rcases ent_class hpre hreach hfv hB0 hk hI hks hvC (hE e he hb) hc with
      ⟨hkk, hsD⟩ | ⟨⟨cw, hcw, hcase⟩, hsL⟩ <;>
      rcases ent_class hpre hreach hfv hB0 hk hI hks hvC (hE e' he' hb') hc' with
        ⟨hkk', hsD'⟩ | ⟨⟨cw', hcw', hcase'⟩, hsL'⟩
    · exact kid_vs_kid hI hkk hkk' hne hsD hsD'
    · exact root_vs_kid hI hsL' hkk hsD
    · exact root_vs_kid hI hsL hkk' hsD'
    · have := hfv.2.1 s _ _ hcw hcw'
      subst this
      rcases hcase with rfl | ⟨c, pid, hc, rfl⟩ <;> rcases hcase' with he2 | ⟨c', pid', hc', he2⟩
      · simp only [CovW.bkt.injEq] at he2; exact hne he2
      · cases he2
      · cases he2
      · simp only [CovW.pos.injEq] at he2
        obtain ⟨rfl, -⟩ := he2
        exact hne (hI.inj _ _ c hc hc')

end ctx

end disj

end Spill

end bbolt
end EtcdGrove
end Perennial
