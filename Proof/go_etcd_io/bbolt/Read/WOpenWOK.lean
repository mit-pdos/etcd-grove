/-
The writer's opened buckets, well-formedness (U6e, `notes/bbolt-proof-plan.md`): opening a nested
bucket (`bktOpened`'s state, `WX.addBkt` over the parent's cache update) keeps `wOK` and the
writer's data.
-/
module

public import Proof.go_etcd_io.bbolt.Read.WOpenH
public import Proof.go_etcd_io.bbolt.Read.WOpenOK
public import Proof.go_etcd_io.bbolt.Read.LeafOfT
public import Proof.go_etcd_io.bbolt.Inv.MatReady
public import Proof.go_etcd_io.bbolt.Write.Fuel

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

namespace WOpen

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section wok
variable [GooseExts]

/-! ### A bucket record whose cache grows -/

/-- `B` with the cache `bm`, which has every entry of `B`'s. -/
def bmGrow (B : BRec) (bm : GMap GoString Loc) : Prop :=
  ∀ k c, B.bm !! k = some c → bm !! k = some c

theorem bmGrow_isSome (B : BRec) (bm : GMap GoString Loc) (h : bmGrow B bm) (k : List w8)
    (hn : (bm !! k).isSome = false) : (B.bm !! k).isSome = false := by
  cases e : B.bm !! k with
  | none => rfl
  | some c => rw [h k c e] at hn; cases hn

theorem nodeClean_bm (v : View) (hwm : Nat) (bl : Loc) (B : BRec) (bm : GMap GoString Loc)
    (h : bmGrow B bm) (l : Loc) (r : NRec) (hn : nodeClean v hwm bl B l r) :
    nodeClean v hwm bl { B with bm := bm } l r := by
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17⟩ := hn
  exact ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11,
    fun hl w hw hf => ⟨fun hs => (n12 hl w hw hf).1 (bmGrow_isSome B bm h _ hs), (n12 hl w hw hf).2⟩,
    n13, n14, n15, n16, n17⟩

theorem bktClean_bm (v : View) (hwm : Nat) (bl : Loc) (B : BRec) (bm : GMap GoString Loc)
    (h : bmGrow B bm) (hc : bktClean v hwm bl B) : bktClean v hwm bl { B with bm := bm } := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ := hc
  exact ⟨c1, c2, c3, c4, c5, c6, c7, fun l r hr => nodeClean_bm v hwm bl B bm h l r (c8 l r hr), c9, c10⟩

theorem bktKeys_bm (v : View) (B : BRec) (bm : GMap GoString Loc) (h : bmGrow B bm)
    (hk : bktKeys v B) : bktKeys v { B with bm := bm } := by
  obtain ⟨bnd, k1, k2, k3⟩ := hk
  refine ⟨bnd, k1, k2, fun l r hr => ?_⟩
  obtain ⟨m1, m2, m3, m4, m5, m6⟩ := k3 l r hr
  refine ⟨m1, m2, m3, m4, m5, fun hl w hw hf hroot hno => m6 hl w hw hf hroot fun ho => hno ?_⟩
  unfold opened at ho ⊢
  cases e : B.bm !! w.key with
  | none => rw [e] at ho; cases ho
  | some c => simp only at ho ⊢; rw [h _ c e]; rfl

theorem entryIn_bm (vw : View) (B : BRec) (bm : GMap GoString Loc) (k v : List w8) :
    entryIn vw { B with bm := bm } k v ↔ entryIn vw B k v := Iff.rfl

/-! ### A bucket's record replaced, its nodes kept (local copies of `Txn/Heap`'s, pure) -/

theorem setBkt_t_bs' (X : WX) (bl : Loc) (B B' : BRec) (k : Loc) :
    (X.setBkt bl { B' with ns := B.ns }).t.bs !! k =
      if k = bl then some { B' with ns := B.ns } else X.t.bs !! k := by
  unfold WX.setBkt
  by_cases h : k = bl
  · subst h; simp
  · simp only [h, ↓reduceIte]; exact GMap.lookup_insert_ne _ _ (Ne.symm h)

theorem setBkt_ns' (X : WX) (bl : Loc) (B B' : BRec) (hb : X.t.bs !! bl = some B) (k : Loc)
    (C : BRec) (hC : (X.setBkt bl { B' with ns := B.ns }).t.bs !! k = some C) :
    ∃ C0, X.t.bs !! k = some C0 ∧ C.ns = C0.ns := by
  rw [setBkt_t_bs'] at hC
  by_cases h : k = bl
  · subst h; simp only [↓reduceIte, Option.some.injEq] at hC; subst hC
    exact ⟨B, hb, rfl⟩
  · simp only [h, ↓reduceIte] at hC
    exact ⟨C, hC, rfl⟩

theorem objsDisj_setBkt' (X : WX) (bl : Loc) (B B' : BRec) (hd : objsDisj X.t)
    (hb : X.t.bs !! bl = some B) : objsDisj (X.setBkt bl { B' with ns := B.ns }).t := by
  intro c C hC n hn c' C' hC' hne
  obtain ⟨C0, hC0, hns⟩ := setBkt_ns' X bl B B' hb c C hC
  rw [hns] at hn
  obtain ⟨C0', hC0', hns'⟩ := setBkt_ns' X bl B B' hb c' C' hC'
  rw [hns']; exact hd c C0 hC0 n hn c' C0' hC0' hne

theorem objs_setBkt' (X : WX) (bl : Loc) (B B' : BRec) (hd : objsDisj X.t)
    (hb : X.t.bs !! bl = some B) :
    (X.setBkt bl { B' with ns := B.ns }).t.objs = X.t.objs := by
  have hd' := objsDisj_setBkt' X bl B B' hd hb
  apply GMap.map_eq
  intro k
  by_cases hkn : ∃ c C rk, X.t.bs !! c = some C ∧ C.ns !! k = some rk
  · obtain ⟨c, C, rk, hC, hrk⟩ := hkn
    rw [objs_node X.t c C k rk hd hC hrk]
    by_cases hcb : c = bl
    · subst hcb
      rw [hb] at hC; cases hC
      exact objs_node _ c { B' with ns := B.ns } k rk hd' (by rw [setBkt_t_bs']; simp) hrk
    · exact objs_node _ c C k rk hd' (by rw [setBkt_t_bs']; simp [hcb, hC]) hrk
  · have hno : ∀ c C, X.t.bs !! c = some C → C.ns !! k = none := by
      intro c C hC
      cases h : C.ns !! k with
      | none => rfl
      | some rk => exact absurd ⟨c, C, rk, hC, h⟩ hkn
    rw [objs_other X.t k hno, objs_other]
    · rfl
    intro c C hC
    obtain ⟨C0, hC0, hns⟩ := setBkt_ns' X bl B B' hb c C hC
    rw [hns]; exact hno c C0 hC0

/-! ### The opened bucket's data: a tree of the view's pages -/

/-- The logical tree of a bucket with no node: its view pages. -/
def viewL (v : View) (c : Loc) : LTree := fun k p =>
  if k = c then (v.pages !! p.toNat).map fun pg => (decide (pageFlags pg = leafPageFlag), pageWs pg)
  else none

theorem lleaves_congr' (L L' : LTree) (bl : Loc) (h : ∀ q, L bl q = L' bl q) :
    ∀ n p, lleaves L bl n p = lleaves L' bl n p := by
  intro n
  induction n with
  | zero => intro p; rfl
  | succ n ih => intro p; simp only [lleaves, h p, ih]

theorem lleaves_viewL (v : View) (c : Loc) :
    ∀ n (pid : w64), lleaves (viewL v c) c n pid = (leavesF n v.pages pid.toNat).map pageWs
  | 0, _ => rfl
  | n + 1, pid => by
    simp only [lleaves, leavesF]
    simp only [viewL, ↓reduceIte]
    cases hp : v.pages !! pid.toNat with
    | none => rfl
    | some pg =>
      simp only [Option.map_some]
      by_cases hl : pageFlags pg = leafPageFlag
      · simp [hl]
      · simp only [hl, decide_false, ite_false]
        rw [List.map_flatMap]
        unfold pageWs
        rw [List.flatMap_map]
        apply Write.flatMap_congr'
        intro i _
        have hpw : (pageW pg i).pgid = W64 (branchPgid pg i : Int) := by
          unfold pageW; rw [if_neg hl]
        rw [hpw, lleaves_viewL v c n, LR.branchPgid_toNat]; rfl

/-- **A bucket of view pages walks its tree's leaves** with any fuel past the pages'. -/
theorem lleaves_viewL_fuel (v : View) (hv : viewWF v) (c : Loc) (pid : w64) (k : Nat) :
    lleaves (viewL v c) c (v.pages.size + 1 + k) pid =
      (treeLeaves v.pages pid.toNat).map pageWs := by
  unfold treeLeaves
  rw [← lleaves_viewL]
  apply Write.lleaves_fuel_stable (viewL v c) c (Write.treeMeasure v.pages) ?_ (v.pages.size + 1) k pid
  · have := Write.treeMeasure_le v.pages pid; omega
  · intro p ws hL w hw
    simp only [viewL, ↓reduceIte] at hL
    cases hp : v.pages !! p.toNat with
    | none => rw [hp] at hL; cases hL
    | some pg =>
      rw [hp] at hL
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, decide_eq_false_iff_not] at hL
      obtain ⟨hnl, rfl⟩ := hL
      unfold pageWs at hw
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hw
      rw [List.mem_range] at hi
      have hpw : (pageW pg i).pgid = W64 (branchPgid pg i : Int) := by
        unfold pageW; rw [if_neg hnl]
      rw [hpw]
      have hb : pageFlags pg = branchPageFlag := by
        rcases (viewWF_page_ready v hv _ pg hp).2.2.1 with e | e
        · exact absurd e hnl
        · exact e
      exact Write.treeMeasure_child v hv p pg hp hb i hi

/-- The leaves `leavesF` reaches are leaf pages of the tree below `id`. -/
theorem leavesF_own (P : Pages)
    (hk : ∀ id pg, P !! id = some pg → pageFlags pg = leafPageFlag ∨ pageFlags pg = branchPageFlag) :
    ∀ n id pg, pg ∈ leavesF n P id →
    ∃ p, ownHas P id p ∧ P !! p = some pg ∧ pageFlags pg = leafPageFlag
  | 0, _, _, h => by simp [leavesF] at h
  | n + 1, id, pg, h => by
    simp only [leavesF] at h
    cases hp : P !! id with
    | none => rw [hp] at h; simp at h
    | some pg0 =>
      rw [hp] at h
      simp only at h
      by_cases hl : pageFlags pg0 = leafPageFlag
      · rw [if_pos hl, List.mem_singleton] at h
        subst h
        exact ⟨id, ownHas.root _ _ hp, hp, hl⟩
      · rw [if_neg hl] at h
        obtain ⟨i, hi, hm⟩ := List.mem_flatMap.1 h
        rw [List.mem_range] at hi
        obtain ⟨p, ho, hpp, hlf⟩ := leavesF_own P hk n _ pg hm
        have hb : pageFlags pg0 = branchPageFlag := by
          rcases hk id pg0 hp with e | e
          · exact absurd e hl
          · exact e
        exact ⟨p, ownHas.child id pg0 i p hp hb hi ho, hpp, hlf⟩

/-- **Two entries of one key in a well-formed bucket are one.** -/
theorem allEnts_key_inj (X : WX) (hok : wOK X) (k : Loc) (R : BRec) (hR : X.t.bs !! k = some R)
    (w1 w2 : WEntry) (h1 : w1 ∈ X.allEnts k) (h2 : w2 ∈ X.allEnts k) (hk : w1.key = w2.key) :
    w1 = w2 := by
  have hc := Write.wOK_bktClean X hok k R hR
  obtain ⟨bnd, hbk⟩ := (hok.2.1 k R hR).1
  have hv : viewWF X.v := hok.2.2.2.2.2.2.2
  have hwalk := LR.bInvL_walk X k R bnd _ hR hc hbk hv X.fuel _ _
    (LR.bInvL_root X k R bnd _ hR hc hbk hv)
  have hall : X.allEnts k =
      ((Write.lleavesB (ltree X) k X.fuel (X.rootPid k) (none, none)).map fun x => x.2.2).flatten := by
    unfold WX.allEnts WX.leaves; rw [Write.lleavesB_snd]
  rw [hall, List.mem_flatten] at h1 h2
  obtain ⟨l1, hl1, hw1⟩ := h1
  obtain ⟨x1, hx1, rfl⟩ := List.mem_map.1 hl1
  obtain ⟨l2, hl2, hw2⟩ := h2
  obtain ⟨x2, hx2, rfl⟩ := List.mem_map.1 hl2
  have hk1 := hwalk.1 x1 hx1 w1 hw1
  have hk2 := hwalk.1 x2 hx2 w2 hw2
  have hxy : x1 = x2 := by
    apply Classical.byContradiction
    intro hne
    have := LR.pw_mem_ne _ (fun x y h k hy hx => h k hx hy) _ hwalk.2.1 x1 hx1 x2 hx2 hne
    exact this w1.key hk1 (hk ▸ hk2)
  subst hxy
  have hL := Write.lleavesB_leaf (ltree X) k X.fuel _ _ x1 hx1
  have hs := LeafT.leaf_pw X hok k R hR x1.1 x1.2.2 hL
  have e1 := wsAt_of_mem x1.2.2 hs w1 hw1
  have e2 := wsAt_of_mem x1.2.2 hs w2 hw2
  rw [hk, e2] at e1
  exact (Option.some.inj e1).symm

/-- A plain leaf page's entries are its elements'. -/
theorem plain_pageWs (pg : List w8) (hl : pageFlags pg = leafPageFlag)
    (hp : ∀ j < pageCount pg, leafFlags pg j % 2 = 0) :
    (pageWs pg).filterMap Write.plainOf = leafEnts pg := by
  unfold pageWs leafEnts
  rw [List.filterMap_map]
  have key : ∀ (l : List Nat), (∀ i ∈ l, i < pageCount pg) →
      l.filterMap (Write.plainOf ∘ pageW pg) = l.map fun i => (leafKey pg i, leafValue pg i) := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons i t ih =>
      intro hl'
      have hi := hl' i List.mem_cons_self
      have e : (Write.plainOf ∘ pageW pg) i = some (leafKey pg i, leafValue pg i) := by
        simp only [Function.comp_def]
        rw [pageW_leaf' pg i hl]
        unfold Write.plainOf
        have : ¬ isBktFlag (W32 (leafFlags pg i : Int)) := by
          intro h; have := isBktFlag_mod _ h; have := hp i hi; omega
        rw [if_neg (by simpa using this)]
      rw [List.filterMap_cons, e, List.map_cons]
      simp only
      rw [ih (fun j hj => hl' j (List.mem_cons_of_mem _ hj))]
  exact key _ (fun i hi => List.mem_range.1 hi)

/-! ### The opened state -/

theorem inBucketRoot_zero (v : List w8) : inBucketRoot v = 0 ↔ (ibOf v).root' = W64 0 := by
  unfold inBucketRoot ibOf
  constructor
  · intro h0; apply BitVec.eq_of_toNat_eq; simpa using h0
  · intro h0; rw [h0]; rfl


section opened
variable (X : WX) (bl c : Loc) (B C : BRec) (nb : List w8) (h : GoString × Nat)

/-- The state after the open. -/
abbrev XO : WX := (X.setBkt bl { B with bm := B.bm.insert nb c }).addBkt c C h

theorem XO_bs (k : Loc) : (XO X bl c B C nb h).t.bs !! k =
    if k = c then some C else if k = bl then some { B with bm := B.bm.insert nb c }
    else X.t.bs !! k := by
  unfold XO
  rw [addBkt_bs]
  split
  · rfl
  · unfold WX.setBkt
    split
    · rename_i hk; subst hk; simp
    · rename_i hk; exact GMap.lookup_insert_ne _ _ (Ne.symm hk)

variable (hB : X.t.bs !! bl = some B) (hc : X.t.bs !! c = none) (hbm : B.bm !! nb = none)
include hB hc hbm

omit hbm in
theorem c_ne_bl : c ≠ bl := by intro e; subst e; rw [hB] at hc; cases hc

/-- A bucket of the opened state: the new one, or an old one with (maybe) a grown cache. -/
theorem XO_back (k : Loc) (D : BRec) (hD : (XO X bl c B C nb h).t.bs !! k = some D) :
    (k = c ∧ D = C) ∨ (k ≠ c ∧ ∃ D0, X.t.bs !! k = some D0 ∧ D = { D0 with bm := D.bm } ∧
      bmGrow D0 D.bm ∧ (k ≠ bl → D = D0) ∧
      ∀ n c', D.bm !! n = some c' → (k = bl ∧ n = nb ∧ c' = c) ∨ D0.bm !! n = some c') := by
  rw [XO_bs] at hD
  by_cases hkc : k = c
  · simp only [hkc, ↓reduceIte, Option.some.injEq] at hD; exact Or.inl ⟨hkc, hD.symm⟩
  · right
    simp only [hkc, ↓reduceIte] at hD
    refine ⟨hkc, ?_⟩
    by_cases hkb : k = bl
    · simp only [hkb, ↓reduceIte, Option.some.injEq] at hD
      subst hkb hD
      refine ⟨B, hB, rfl, ?_, fun h' => absurd rfl h', ?_⟩
      · intro k' c' e
        by_cases hk' : nb = k'
        · subst hk'
          rw [hbm] at e; cases e
        · show (B.bm.insert nb c) !! k' = some c'
          rw [GMap.lookup_insert_ne _ _ hk']; exact e
      · intro n c' e
        by_cases hn : nb = n
        · subst hn; exact Or.inl ⟨rfl, rfl, by simpa [GMap.lookup_insert] using e.symm⟩
        · right
          have e' : (B.bm.insert nb c) !! n = some c' := e
          rw [GMap.lookup_insert_ne _ _ hn] at e'; exact e'
    · simp only [hkb, ↓reduceIte] at hD
      exact ⟨D, hD, rfl, fun _ _ e => e, fun _ => rfl, fun _ _ e => Or.inr e⟩

theorem XO_bs_old (k : Loc) (D0 : BRec) (hk : X.t.bs !! k = some D0) :
    ∃ D, (XO X bl c B C nb h).t.bs !! k = some D ∧ D.ns = D0.ns ∧ D.ib = D0.ib ∧ D.bv = D0.bv := by
  rw [XO_bs]
  have hkc : k ≠ c := by intro e; subst e; rw [hc] at hk; cases hk
  simp only [hkc, ↓reduceIte]
  by_cases hkb : k = bl
  · subst hkb; rw [hB] at hk; cases hk; simp
  · simp only [hkb, ↓reduceIte]; exact ⟨D0, hk, rfl, rfl, rfl⟩

/-- **The opened state is well-formed.** -/
theorem wOK_XO (w : WEntry) (hok : wOK X) (hd : objsDisj X.t) (hk : w.key = nb)
    (hrec : openedRec B.bv.tx' w.value w.vs C)
    (hbv : bvalOK X.v.pages X.t.mv.pgid'.toNat w.value) (hent : entryIn X.v B nb w.value)
    (htk : inBucketRoot w.value ≠ 0 → treeKeys X.v.pages (inBucketRoot w.value) none none)
    (hcd : X.t.deadB !! c = none) (hhd : h.1 = nb)
    (hplain : ∀ pg, bktLeafPg X.v.pages w.value pg → ∀ j < pageCount pg, leafFlags pg j % 2 = 0) :
    wOK (XO X bl c B C nb h) := by
  obtain ⟨hib, htx, hrn, hnm, hbmC, hns, hil, hni⟩ := hrec
  obtain ⟨⟨tw, ⟨tpm, tbuf, tls, tps⟩, t2, t3, trl, tall⟩, hkn, hpg, heb, hhs, hlv, hnl, hv⟩ := hok
  have hroot0 : C.ib.root' = W64 0 ↔ inBucketRoot w.value = 0 := by
    rw [hib, inBucketRoot_zero]
  have hrl : X.rl ≠ c := by
    intro e; obtain ⟨R, hR⟩ := Option.isSome_iff_exists.1 trl; rw [e, hc] at hR; cases hR
  have hnsN : ∀ l r, C.ns !! l = some r → False := by
    intro l r hr; rw [hns] at hr; cases hr
  -- the new bucket is clean
  have hCc : bktClean X.v X.t.mv.pgid'.toNat c C := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro h0 _
      have hi := hroot0.1 h0
      obtain ⟨hpp, hipg, hsrc⟩ := hil hi
      refine ⟨hpp, ?_, ?_⟩
      · rcases hsrc with ⟨-, a, b⟩ | ⟨a, b⟩
        · exact Or.inl ⟨a, b⟩
        · exact Or.inr ⟨a, b⟩
      · rw [hipg]; exact hbv.2 hi
    · intro h0
      have hi : inBucketRoot w.value ≠ 0 := fun e => h0 (hroot0.2 e)
      have hwf : treeWF X.v.pages X.t.mv.pgid'.toNat (inBucketRoot w.value) := by
        cases hbv.1 with
        | file _ _ _ ht => exact ht
        | inline _ _ h0' _ _ => exact absurd h0' hi
      have hr : C.ib.root'.toNat = inBucketRoot w.value := by rw [hib]; rfl
      rw [hr]
      refine ⟨?_, fun _ => hwf⟩
      cases hwf with
      | page _ _ _ hlt _ _ _ _ => exact hlt
    · intro _; exact ⟨hns, hnm⟩
    · intro h'; exact absurd hrn h'
    · intro c' l hl; rw [hnm] at hl; cases hl
    · intro h0; exact (hni (fun e => h0 (hroot0.2 e))).1
    · intro _ l r hr; exact (hnsN l r hr).elim
    · intro l r hr; exact (hnsN l r hr).elim
    · intro l1 _ _ _ _ _ hp; obtain ⟨r, -, hr, -⟩ := hp; exact (hnsN _ r hr).elim
    · intro l _ _ hp; obtain ⟨r, -, hr, -⟩ := hp; exact (hnsN _ r hr).elim
  refine ⟨⟨tw, ⟨tpm, tbuf, ?_, ?_⟩, t2, t3, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, hv⟩
  · -- leafShape
    unfold leafShape at tls ⊢
    intro k D hD l r hr hl w' hw'
    rcases XO_back X bl c B C nb h hB hc hbm k D hD with ⟨-, hDC⟩ | ⟨-, D0, hD0, hDe, -, -, -⟩
    · rw [hDC] at hr; exact (hnsN l r hr).elim
    · rw [hDe] at hr; exact tls k D0 hD0 l r hr hl w' hw'
  · -- posShape
    unfold posShape at tps ⊢
    intro k D hD c' p pg hpr hown hpg hlf i hi
    rcases XO_back X bl c B C nb h hB hc hbm k D hD with ⟨hkc, hDC⟩ | ⟨-, D0, hD0, hDe, -, -, -⟩
    · rw [hDC] at hpr
      rcases hpr with ⟨-, hr0, rfl⟩ | ⟨l, j, ⟨r, -, hr, -⟩, -⟩
      · have hr : C.ib.root'.toNat = inBucketRoot w.value := by rw [hib]; rfl
        rw [hr] at hown
        have hi0 : inBucketRoot w.value ≠ 0 := fun e => hr0 (hroot0.2 e)
        have := hplain pg (Or.inr ⟨hi0, p, hown, hpg, hlf⟩) i hi
        rw [hkc]
        constructor
        · intro e; unfold bucketLeafFlag at e; omega
        · intro e; exact absurd e.symm hrl
      · exact (hnsN l r hr).elim
    · rw [hDe] at hpr; exact tps k D0 hD0 c' p pg hpr hown hpg hlf i hi
  · -- the root bucket
    show ((XO X bl c B C nb h).t.bs !! X.rl).isSome
    obtain ⟨R, hR⟩ := Option.isSome_iff_exists.1 trl
    obtain ⟨D, hD, -⟩ := XO_bs_old X bl c B C nb h hB hc hbm X.rl R hR
    rw [hD]; rfl
  · -- every bucket clean, its cache's children buckets
    intro k D hD
    rcases XO_back X bl c B C nb h hB hc hbm k D hD with ⟨hkc, rfl⟩ | ⟨hkc, D0, hD0, hDe, hgr, -, hbmD⟩
    · rw [hkc]
      refine ⟨hCc, ?_⟩
      intro n c' e; rw [hbmC] at e; cases e
    · obtain ⟨hcl, hch⟩ := tall k D0 hD0
      refine ⟨by rw [hDe]; exact bktClean_bm _ _ _ D0 D.bm hgr hcl, fun n c' e => ?_⟩
      rcases hbmD n c' e with ⟨-, -, hcc⟩ | e0
      · rw [hcc]
        show ((XO X bl c B C nb h).t.bs !! c).isSome
        rw [XO_bs]; simp
      · obtain ⟨R, hR⟩ := Option.isSome_iff_exists.1 (hch n c' e0)
        obtain ⟨D', hD', -⟩ := XO_bs_old X bl c B C nb h hB hc hbm c' R hR
        rw [hD']; rfl
  · -- keys and nested buckets
    intro k D hD
    rcases XO_back X bl c B C nb h hB hc hbm k D hD with ⟨-, hDC⟩ | ⟨hkc, D0, hD0, hDe, hgr, -, hbmD⟩
    · rw [hDC]
      refine ⟨⟨fun _ => (none, none), fun _ h0 => ?_, fun r hr => (hnsN _ r hr).elim,
        fun l r hr => (hnsN l r hr).elim⟩, fun n c' e => ?_⟩
      · have hi : inBucketRoot w.value ≠ 0 := fun e => h0 (hroot0.2 e)
        have hr : C.ib.root'.toNat = inBucketRoot w.value := by rw [hib]; rfl
        rw [hr]; exact htk hi
      · rw [hbmC] at e; cases e
    · obtain ⟨hkk, hnest⟩ := hkn k D0 hD0
      refine ⟨by rw [hDe]; exact bktKeys_bm _ D0 D.bm hgr hkk, fun n c' e => ?_⟩
      rcases hbmD n c' e with ⟨hkb, hnn, hcc⟩ | e0
      · rw [hcc, hnn]
        rw [hkb, hB] at hD0; cases hD0
        refine ⟨C, w.value, by rw [XO_bs]; simp, ?_, ?_, fun h0 => (hbv.2 h0).1, ?_, fun _ => hib⟩
        · rw [hDe]; exact hent
        · cases hbv.1 <;> assumption
        · rw [hib]
      · obtain ⟨C0, v0, hC0, hin, h16, hinl, hr0, hrn0⟩ := hnest n c' e0
        obtain ⟨D', hD', hns', hib', hbv'⟩ := XO_bs_old X bl c B C nb h hB hc hbm c' C0 hC0
        refine ⟨D', v0, hD', by rw [hDe]; exact hin, h16, hinl, by rw [hib']; exact hr0,
          fun h' => by rw [hib']; exact hrn0 (by rw [← hbv']; exact h')⟩
  · -- nodes' pages
    intro k D hD l r hr
    rcases XO_back X bl c B C nb h hB hc hbm k D hD with ⟨-, hDC⟩ | ⟨hkc, D0, hD0, hDe, -, -, -⟩
    · rw [hDC] at hr; exact (hnsN l r hr).elim
    · rw [hDe] at hr ⊢; exact hpg k D0 hD0 l r hr
  · -- entries bounded
    intro k D hD l r hr
    rcases XO_back X bl c B C nb h hB hc hbm k D hD with ⟨-, hDC⟩ | ⟨hkc, D0, hD0, hDe, -, -, -⟩
    · rw [hDC] at hr; exact (hnsN l r hr).elim
    · rw [hDe] at hr; exact heb k D0 hD0 l r hr
  · -- handles
    intro b nm hb
    show ((XO X bl c B C nb h).t.bobjs !! b).isSome
    unfold WTx.bobjs
    by_cases hbc : b = c
    · rw [hbc, GMap.lookup_union_Some_l _ _ _ C (by rw [XO_bs]; simp)]; rfl
    · have hb' : X.handles !! b = some nm := by
        have : (X.handles.insert c h) !! b = some nm := hb
        rwa [GMap.lookup_insert_ne _ _ (Ne.symm hbc)] at this
      have := hhs b nm hb'
      unfold WTx.bobjs at this
      cases eb : X.t.bs !! b with
      | some R =>
        obtain ⟨D, hD, -⟩ := XO_bs_old X bl c B C nb h hB hc hbm b R eb
        rw [GMap.lookup_union_Some_l _ _ _ _ hD]; rfl
      | none =>
        have hXO : (XO X bl c B C nb h).t.bs !! b = none := by
          rw [XO_bs]; simp only [hbc, ↓reduceIte]
          by_cases hbb : b = bl
          · subst hbb; rw [hB] at eb; cases eb
          · simp only [hbb, ↓reduceIte]; exact eb
        rw [GMap.lookup_union_r _ _ _ hXO]
        rw [GMap.lookup_union_r _ _ _ eb] at this
        exact this
  · -- liveness
    obtain ⟨l1, l2, l3, l4, l5⟩ := hlv
    have hobjs : (XO X bl c B C nb h).t.objs = X.t.objs := by
      unfold XO
      have hd1 := objsDisj_setBkt' X bl B { B with bm := B.bm.insert nb c } hd hB
      have hc1 : (X.setBkt bl { B with bm := B.bm.insert nb c }).t.bs !! c = none := by
        unfold WX.setBkt; rw [GMap.lookup_insert_ne _ _ (Ne.symm (c_ne_bl X bl c B hB hc))]; exact hc
      rw [objs_addBkt _ c C h hd1 hns hc1]
      exact objs_setBkt' X bl B { B with bm := B.bm.insert nb c } hd hB
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show X.rl ∈ X.liveB.insert c ()
      simp only [GMap.mem_iff] at l1 ⊢
      rw [GMap.lookup_insert_ne _ _ (Ne.symm hrl)]; exact l1
    · intro l hl; rw [hobjs]; exact l2 l hl
    · intro k D hD
      show k ∈ X.liveB.insert c ()
      simp only [GMap.mem_iff]
      by_cases hkc : k = c
      · subst hkc; rw [GMap.lookup_insert]; rfl
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm hkc)]
        rcases XO_back X bl c B C nb h hB hc hbm k D hD with ⟨e, -⟩ | ⟨-, D0, hD0, -⟩
        · exact absurd e hkc
        · have := l3 k D0 hD0; simp only [GMap.mem_iff] at this; exact this
    · intro k D l r hD hr
      rcases XO_back X bl c B C nb h hB hc hbm k D hD with ⟨-, hDC⟩ | ⟨hkc, D0, hD0, hDe, -, -, -⟩
      · rw [hDC] at hr; exact (hnsN l r hr).elim
      · rw [hDe] at hr; exact l4 k D0 l r hD0 hr
    · exact l5
  · -- the node registry
    intro n b p hn hl
    obtain ⟨D0, r, hD0, hr, hp⟩ := hnl n b p hn hl
    obtain ⟨D, hD, hns', -⟩ := XO_bs_old X bl c B C nb h hB hc hbm b D0 hD0
    exact ⟨D, r, hD, by rw [hns']; exact hr, hp⟩

omit hbm in
theorem XO_size : (XO X bl c B C nb h).t.bs.size = X.t.bs.size + 1 := by
  unfold XO WX.addBkt WX.setBkt
  simp only
  rw [GMap.map_size_insert_None _ _ _ (by
    rw [GMap.lookup_insert_ne _ _ (Ne.symm (c_ne_bl X bl c B hB hc))]; exact hc)]
  congr 1
  rw [GMap.size_eq_length _ X.t.bs.domList (GMap.nodup_dom_list _)]
  · exact (GMap.size_eq_dom_list_length _).symm
  · intro k
    rw [GMap.mem_dom_list]
    by_cases hk : bl = k
    · subst hk; rw [GMap.lookup_insert, hB]; rfl
    · rw [GMap.lookup_insert_ne _ _ hk]

omit hbm in
theorem XO_ltree_old (k : Loc) (hk : k ≠ c) : ltree (XO X bl c B C nb h) k = ltree X k := by
  funext p
  unfold ltree
  rw [XO_bs]
  simp only [hk, ↓reduceIte]
  by_cases hkb : k = bl
  · subst hkb; rw [hB]; simp only [↓reduceIte]; rfl
  · simp only [hkb, ↓reduceIte]; rfl

omit hbm in
theorem XO_rootPid_old (k : Loc) (hk : k ≠ c) :
    (XO X bl c B C nb h).rootPid k = X.rootPid k := by
  unfold WX.rootPid
  rw [XO_bs]
  simp only [hk, ↓reduceIte]
  by_cases hkb : k = bl
  · subst hkb; rw [hB]; simp only [↓reduceIte]; rfl
  · simp only [hkb, ↓reduceIte]

theorem XO_leaves_old (hok : wOK X) (k : Loc) (hk : k ≠ c) :
    (XO X bl c B C nb h).leaves k = X.leaves k := by
  unfold WX.leaves
  rw [XO_rootPid_old X bl c B C nb h hB hc k hk,
    lleaves_congr' _ (ltree X) k (fun q => by rw [XO_ltree_old X bl c B C nb h hB hc k hk])]
  have hf : (XO X bl c B C nb h).fuel = X.fuel + 1 := by
    unfold WX.fuel; rw [XO_size X bl c B C nb h hB hc]; rfl
  rw [hf]
  exact Write.wOK_leaves_fuel' X k hok 1

/-- **The opened bucket's leaves** are its value's tree's (its inline page, or its view tree's). -/
theorem XO_leaves_new (w : WEntry) (hv : viewWF X.v) (hrec : openedRec B.bv.tx' w.value w.vs C)
    (hbv : bvalOK X.v.pages X.t.mv.pgid'.toNat w.value) :
    (XO X bl c B C nb h).leaves c = (bktLeaves X.v.pages w.value).map pageWs := by
  obtain ⟨hib, -, hrn, hnm, -, -, hil, hni⟩ := hrec
  have hCb : (XO X bl c B C nb h).t.bs !! c = some C := by rw [XO_bs]; simp
  have hrp : (XO X bl c B C nb h).rootPid c = C.ib.root' := by unfold WX.rootPid; rw [hCb]; rfl
  have hres : ∀ p, resolve C p = none := by
    intro p; unfold resolve; split
    · simp [hrn]
    · rw [hnm]; rfl
  have hr : C.ib.root'.toNat = inBucketRoot w.value := by rw [hib]; rfl
  unfold WX.leaves bktLeaves
  rw [hrp]
  by_cases h0 : inBucketRoot w.value = 0
  · rw [if_pos h0]
    have hC0 : C.ib.root' = W64 0 := by
      apply BitVec.eq_of_toNat_eq; rw [hr, h0]; rfl
    obtain ⟨-, hipg, -⟩ := hil h0
    have hg := (hbv.2 h0).1
    have hL : ltree (XO X bl c B C nb h) c (W64 0) = some (true, pageWs (inlinePage w.value)) := by
      unfold ltree; rw [hCb]; simp only; rw [hres]
      simp [wpageAt, hC0, hipg, hg.2.1]
    rw [hC0]
    obtain ⟨n, hn⟩ : ∃ n, (XO X bl c B C nb h).fuel = n + 1 := ⟨_, rfl⟩
    rw [hn]
    simp only [lleaves]
    rw [hL]
    rfl
  · rw [if_neg h0]
    have hC0 : C.ib.root' ≠ W64 0 := by
      intro e; apply h0; rw [← hr, e]; rfl
    have hL : ∀ q, ltree (XO X bl c B C nb h) c q = viewL X.v c c q := by
      intro q
      unfold ltree viewL; rw [hCb]; simp only [↓reduceIte]; rw [hres]
      simp only [wpageAt, hC0, ↓reduceIte, Option.map_map]
      rfl
    rw [lleaves_congr' _ (viewL X.v c) c hL]
    have hf : (XO X bl c B C nb h).fuel = X.v.pages.size + 1 + (XO X bl c B C nb h).t.bs.size := by
      unfold WX.fuel; rw [show (XO X bl c B C nb h).v = X.v from rfl]; omega
    rw [hf, lleaves_viewL_fuel X.v hv c _ _, hr]

/-- **Opening keeps the writer's data.** -/
theorem wtxData_XO (w : WEntry) (hok : wOK X) (hk : w.key = nb) (hf : isBktFlag w.flags)
    (hw : w ∈ X.allEnts bl)
    (hrec : openedRec B.bv.tx' w.value w.vs C)
    (hbv : bvalOK X.v.pages X.t.mv.pgid'.toNat w.value)
    (hplain : ∀ pg, bktLeafPg X.v.pages w.value pg → ∀ j < pageCount pg, leafFlags pg j % 2 = 0) :
    wtxData (XO X bl c B C nb h) = wtxData X := by
  have hv : viewWF X.v := hok.2.2.2.2.2.2.2
  have trl := hok.1.2.2.2.2.1
  have hrl : X.rl ≠ c := by
    intro e; obtain ⟨R, hR⟩ := Option.isSome_iff_exists.1 trl; rw [e, hc] at hR; cases hR
  have hroot : rootEnts (XO X bl c B C nb h) = rootEnts X := by
    unfold rootEnts
    rw [show (XO X bl c B C nb h).rl = X.rl from rfl, XO_leaves_old X bl c B C nb h hB hc hbm hok _ hrl]
  unfold wtxData
  rw [hroot]
  congr 1
  apply List.map_congr_left
  intro e he
  congr 1
  rw [Write.bktDataOf_eq, Write.bktDataOf_eq]
  have hloc : bktLoc (XO X bl c B C nb h) e.1 =
      if X.rl = bl ∧ e.1 = nb then some c else bktLoc X e.1 := by
    unfold bktLoc
    rw [show (XO X bl c B C nb h).rl = X.rl from rfl, XO_bs]
    simp only [hrl, ↓reduceIte]
    by_cases hb : X.rl = bl
    · rw [hb, hB]; simp only [↓reduceIte, Option.bind_some, true_and]
      by_cases hn : e.1 = nb
      · rw [if_pos hn, hn, GMap.lookup_insert]
      · rw [if_neg hn, GMap.lookup_insert_ne _ _ (Ne.symm hn)]
    · simp only [hb, ↓reduceIte, false_and]
  rw [hloc]
  by_cases hch : X.rl = bl ∧ e.1 = nb
  · rw [if_pos hch]
    obtain ⟨hb, hn⟩ := hch
    have hX : bktLoc X e.1 = none := by
      unfold bktLoc; rw [hb, hB, hn]; simp [hbm]
    rw [hX]
    simp only
    -- the root entry's value is `w`'s
    have he2 : e.2 = w.value := by
      unfold rootEnts at he
      obtain ⟨ws, hws, he'⟩ := List.mem_flatMap.1 he
      obtain ⟨w', hw', hb'⟩ := List.mem_filterMap.1 he'
      split at hb'
      · cases hb'
        have hw'a : w' ∈ X.allEnts X.rl := List.mem_flatten.2 ⟨ws, hws, hw'⟩
        rw [hb] at hw'a
        have := allEnts_key_inj X hok bl B hB w' w hw'a hw (by simp only at hn; rw [hn, hk])
        rw [this]
      · cases hb'
    rw [he2]
    unfold lbktEnts bktOfPage bktEntries
    rw [XO_leaves_new X bl c B C nb h hB hc hbm w hv hrec hbv, List.flatMap_map]
    congr 1
    apply Write.flatMap_congr'
    intro pg hpg
    have hpl : bktLeafPg X.v.pages w.value pg ∧ pageFlags pg = leafPageFlag := by
      unfold bktLeaves at hpg
      by_cases h0 : inBucketRoot w.value = 0
      · rw [if_pos h0, List.mem_singleton] at hpg
        subst hpg
        exact ⟨Or.inl ⟨h0, rfl⟩, (hbv.2 h0).1.2.1⟩
      · rw [if_neg h0] at hpg
        obtain ⟨p, ho, hp, hl⟩ := leavesF_own X.v.pages
          (fun id pg hp => (viewWF_page_ready X.v hv id pg hp).2.2.1) _ _ pg hpg
        exact ⟨Or.inr ⟨h0, p, ho, hp, hl⟩, hl⟩
    exact plain_pageWs pg hpl.2 (hplain pg hpl.1)
  · rw [if_neg hch]
    cases hl : bktLoc X e.1 with
    | none => rfl
    | some c' =>
      simp only
      have hc' : c' ≠ c := by
        intro e'; subst e'
        unfold bktLoc at hl
        obtain ⟨R, hR⟩ := Option.isSome_iff_exists.1 trl
        rw [hR] at hl
        simp only [Option.bind_some] at hl
        have := (hok.1.2.2.2.2.2 X.rl R hR).2 _ _ hl
        rw [hc] at this; cases this
      unfold lbktEnts
      rw [XO_leaves_old X bl c B C nb h hB hc hbm hok _ hc']

end opened


/-- **Opening a nested bucket keeps `wOK` and the data**: the parent `bl`'s cache gains
`nb ↦ c`, the fresh bucket `c` (record `C`, `openedRec` of the entry's value) is added, live, a
handle; the entry's nested tree's leaves are plain (`hplain`). -/
theorem wOK_bktOpened (X : WX) (bl c : Loc) (B C : BRec) (w : WEntry) (nb : List w8) (g : Nat)
    (hok : wOK X) (hd : objsDisj X.t) (hB : X.t.bs !! bl = some B) (hw : w ∈ X.allEnts bl)
    (hk : w.key = nb) (hf : isBktFlag w.flags) (hbm : B.bm !! nb = none)
    (hbo : X.t.bobjs !! c = none)
    (hrec : openedRec B.bv.tx' w.value w.vs C)
    (hbv : bvalOK X.v.pages X.t.mv.pgid'.toNat w.value) (hent : entryIn X.v B nb w.value)
    (htk : inBucketRoot w.value ≠ 0 → treeKeys X.v.pages (inBucketRoot w.value) none none)
    (hplain : ∀ pg, bktLeafPg X.v.pages w.value pg → ∀ j < pageCount pg, leafFlags pg j % 2 = 0) :
    wOK ((X.setBkt bl { B with bm := B.bm.insert nb c }).addBkt c C (nb, g)) ∧
      wtxData ((X.setBkt bl { B with bm := B.bm.insert nb c }).addBkt c C (nb, g)) = wtxData X := by
  have hc : X.t.bs !! c = none := ((GMap.lookup_union_None _ _ _).1 hbo).1
  have hcd : X.t.deadB !! c = none := ((GMap.lookup_union_None _ _ _).1 hbo).2
  exact ⟨wOK_XO X bl c B C nb (nb, g) hB hc hbm w hok hd hk hrec hbv hent htk hcd rfl hplain,
    wtxData_XO X bl c B C nb (nb, g) hB hc hbm w hok hk hf hw hrec hbv hplain⟩

end wok

end WOpen

end bbolt
end EtcdGrove
end Perennial
