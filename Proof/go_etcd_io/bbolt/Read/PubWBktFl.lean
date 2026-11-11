/-
U6y (`notes/bbolt-proof-plan.md`, "Writer reads at a fraction"): **opening a top-level bucket keeps
the freelist's agreement** (`flViewU_bktOpened_root`, U6x's OPEN statement, proved; it now also
takes `wOK` of the opened state, which `Bucket.Bucket_w` gives). The bucket's base pages, covered
in `X` as an unopened root entry (`lCovers`' second case, `bucketCovers` of its value), are covered
in `X'` by the opened bucket's positions (its first case): the opened bucket has no node, so its
logical tree is its view tree (`WOpen.viewL`), whose positions are its own pages (`ownHas`; with
the walks' fuel, `lposF_viewL_complete`), and a top-level bucket's leaves hold no nested bucket
(`posShape` of `X'`), so its tree's pages (`treeHas`) are its own (`ownHas_of_treeHas'`). Every
other bucket's positions and extents are kept (more fuel walks the same positions,
`wOK_positions_fuel`).
-/
module

public import Proof.go_etcd_io.bbolt.Read.PubWBkt
public import Proof.go_etcd_io.bbolt.Read.WOpenWOK
public import Proof.go_etcd_io.bbolt.Write.Fuel
public import Proof.go_etcd_io.bbolt.Write.FlView

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace PubW

section fl
variable [GooseExts]

/-- **More fuel walks the same positions** once a measure decreases along branches below the
fuel (`Write.lleaves_fuel_stable`'s positions analogue). -/
theorem lposF_fuel_stable (L : LTree) (bl : Loc) (μ : w64 → Nat)
    (hdec : ∀ pid ws, L bl pid = some (false, ws) → ∀ w ∈ ws, μ w.pgid < μ pid) :
    ∀ n k pid, μ pid < n → lposF L bl (n + k) pid = lposF L bl n pid
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, k, pid, h => by
    rw [show n + 1 + k = (n + k) + 1 by omega]
    simp only [lposF]
    congr 1
    cases hL : L bl pid with
    | none => rfl
    | some x =>
      obtain ⟨lf, ws⟩ := x
      cases lf with
      | true => rfl
      | false =>
        simp only
        apply Write.flatMap_congr'
        intro w hw
        exact lposF_fuel_stable L bl μ hdec n k w.pgid (by have := hdec pid ws hL w hw; omega)

theorem lposF_congr' (L L' : LTree) (bl : Loc) (h : ∀ q, L bl q = L' bl q) :
    ∀ n p, lposF L bl n p = lposF L' bl n p := by
  intro n
  induction n with
  | zero => intro p; rfl
  | succ n ih => intro p; simp only [lposF, h p, ih]

/-- A branch of a well-formed writer's logical tree has children of smaller measure
(`Write.wOK_leaves_fuel'`'s argument). -/
theorem wOK_hdec (X : WX) (bl : Loc) (hok : wOK X) :
    ∀ pid ws, ltree X bl pid = some (false, ws) → ∀ w ∈ ws,
      Write.treeMeasure X.v.pages w.pgid < Write.treeMeasure X.v.pages pid := by
  have hv : viewWF X.v := hok.2.2.2.2.2.2.2
  intro pid ws hL w hw
  unfold ltree at hL
  cases hB : X.t.bs !! bl with
  | none => rw [hB] at hL; cases hL
  | some B =>
    rw [hB] at hL
    simp only at hL
    have hc := Write.wOK_bktClean X hok bl B hB
    cases hr : resolve B pid with
    | some l =>
      rw [hr] at hL
      simp only at hL
      cases hrl : B.ns !! l with
      | none => rw [hrl] at hL; cases hL
      | some r =>
        rw [hrl] at hL
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hL
        obtain ⟨hleaf, rfl⟩ := hL
        by_cases hin : B.ib.root' = W64 0
        · have := hc.2.2.2.2.2.2.1 hin l r hrl; rw [hleaf] at this; cases this
        · have hnm : B.nm !! pid = some l := by unfold resolve at hr; rwa [if_neg hin] at hr
          obtain ⟨-, r', hr', hpid⟩ := hc.2.2.2.2.1 pid l hnm
          rw [hrl] at hr'; cases hr'
          obtain ⟨-, pg, hpg, hbr, hlen, hws⟩ := ((hok.2.2.1 bl B hB l r hrl).2 hleaf)
          rw [hpid] at hpg
          obtain ⟨i, hi, he⟩ := List.getElem_of_mem hw
          have hwi : r.ws[i]? = some w := by rw [List.getElem?_eq_getElem hi]; exact congrArg _ he
          rw [hws i w hwi]
          exact Write.treeMeasure_child X.v hv pid pg hpg hbr i (by rw [← hlen]; exact hi)
    | none =>
      rw [hr] at hL
      simp only at hL
      cases hp : wpageAt X.v B pid with
      | none => rw [hp] at hL; cases hL
      | some x =>
        obtain ⟨pa, pg⟩ := x
        rw [hp] at hL
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, decide_eq_false_iff_not] at hL
        obtain ⟨hnl, rfl⟩ := hL
        by_cases hin : B.ib.root' = W64 0
        · have hrn : B.bv.rootNode' = null := by
            unfold resolve at hr; rw [if_pos hin] at hr; split at hr
            · assumption
            · cases hr
          have := Write.wOK_inlineLeaf X bl pid hok B pa pg hB hin hrn hp
          exact absurd this hnl
        · have hpg : X.v.pages !! pid.toNat = some pg := by
            unfold wpageAt at hp; rw [if_neg hin] at hp
            cases h : X.v.pages !! pid.toNat with
            | none => rw [h] at hp; cases hp
            | some pg' => rw [h] at hp; simp only [Option.map_some, Option.some.injEq,
                            Prod.mk.injEq] at hp; rw [hp.2]
          have hbr : pageFlags pg = branchPageFlag := by
            rcases (Read.viewWF_page X.v hv _ pg hpg).2.2.2 with h | h
            · exact h
            · exact absurd h hnl
          unfold pageWs at hw
          obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hw
          rw [List.mem_range] at hi
          have : (pageW pg i).pgid = W64 (branchPgid pg i : Int) := by
            unfold pageW; simp [hnl]
          rw [this]
          exact Write.treeMeasure_child X.v hv pid pg hpg hbr i hi

/-- **The walk of a well-formed writer's tree ends within its fuel**: more fuel walks the same
positions. -/
theorem wOK_positions_fuel (X : WX) (bl : Loc) (hok : wOK X) (k : Nat) :
    lposF (ltree X) bl (X.fuel + k) (X.rootPid bl) = X.positions bl := by
  unfold WX.positions
  apply lposF_fuel_stable (ltree X) bl (Write.treeMeasure X.v.pages) (wOK_hdec X bl hok) X.fuel k
  have := Write.treeMeasure_le X.v.pages (X.rootPid bl)
  unfold WX.fuel; omega

/-- A position of a view tree with a page is one of the tree's own pages. -/
theorem lposF_viewL_own (v : View) (hv : viewWF v) (c : Loc) :
    ∀ n p pid pg, pid ∈ lposF (WOpen.viewL v c) c n p → v.pages !! pid.toNat = some pg →
      ownHas v.pages p.toNat pid.toNat
  | 0, _, _, _, h, _ => by simp [lposF] at h
  | n + 1, p, pid, pg, h, hpg => by
    simp only [lposF] at h
    rcases List.mem_cons.1 h with rfl | h
    · exact ownHas.root _ pg hpg
    · simp only [WOpen.viewL, ↓reduceIte] at h
      cases hp : v.pages !! p.toNat with
      | none => rw [hp] at h; simp at h
      | some pgp =>
        rw [hp] at h
        by_cases hl : pageFlags pgp = leafPageFlag
        · simp [hl] at h
        · simp only [Option.map_some, hl, decide_false] at h
          rw [List.mem_flatMap] at h
          obtain ⟨w, hw, hm⟩ := h
          unfold pageWs at hw
          rw [List.mem_map] at hw
          obtain ⟨i, hi, rfl⟩ := hw
          have hpgid : (pageW pgp i).pgid = W64 (branchPgid pgp i : Int) := by simp [pageW, hl]
          rw [hpgid] at hm
          have ih := lposF_viewL_own v hv c n _ pid pg hm hpg
          rw [LR.branchPgid_toNat] at ih
          have hb : pageFlags pgp = branchPageFlag := by
            rcases (Read.viewWF_page v hv p.toNat pgp hp).2.2.2 with h | h
            · exact h
            · exact absurd h hl
          exact ownHas.child _ pgp i _ hp hb (List.mem_range.1 hi) ih

/-- **Every own page of a view tree is a position** of its walk, with fuel past its measure. -/
theorem lposF_viewL_complete (v : View) (hv : viewWF v) (c : Loc) :
    ∀ n (p : w64) x, ownHas v.pages p.toNat x → Write.treeMeasure v.pages p < n →
      W64 (x : Int) ∈ lposF (WOpen.viewL v c) c n p
  | 0, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, p, x, ho, hm => by
    simp only [lposF]
    cases ho with
    | root _ pg hpg => rw [LR.w64_toNat_eq]; exact List.mem_cons_self
    | child _ pg i _ hpg hb hi ho' =>
      apply List.mem_cons_of_mem
      simp only [WOpen.viewL, ↓reduceIte]
      rw [hpg]
      have hl : ¬ pageFlags pg = leafPageFlag := by
        rw [hb]; simp [leafPageFlag, branchPageFlag]
      simp only [Option.map_some, hl, decide_false]
      rw [List.mem_flatMap]
      refine ⟨pageW pg i, List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩, ?_⟩
      have hpgid : (pageW pg i).pgid = W64 (branchPgid pg i : Int) := by simp [pageW, hl]
      rw [hpgid]
      have hpg' : v.pages !! (W64 (p.toNat : Int)).toNat = some pg := by
        rw [LR.w64_toNat_eq]; exact hpg
      have hlt := Write.treeMeasure_child v hv p pg hpg hb i hi
      apply lposF_viewL_complete v hv c n _ x _ (by omega)
      rw [LR.branchPgid_toNat]; exact ho'

theorem ownHas_treeHas' {P : Pages} {c p : Nat} (h : ownHas P c p) : treeHas P c p := by
  induction h with
  | root r pg hpg => exact treeHas.root r pg hpg
  | child r pg i id hpg hb hi _ ih => exact treeHas.sub r pg id hpg (pageHas.child pg i id hb hi ih)

/-- Below a root whose leaves hold no nested bucket, a page of the tree is one of its own
(`Spill.ownHas_of_treeHas`, copied: that module is the spill's). -/
theorem ownHas_of_treeHas' {P : Pages} {q : Nat}
    (hpl : ∀ p pg, ownHas P q p → P !! p = some pg → pageFlags pg = leafPageFlag →
      ∀ i < pageCount pg, leafFlags pg i % 2 ≠ bucketLeafFlag) {x : Nat} (h : treeHas P q x) :
    ownHas P q x :=
  treeHas.rec (pages := P)
    (motive_1 := fun a b _ => (∀ p, ownHas P a p → ownHas P q p) → ownHas P q b)
    (motive_2 := fun pg b _ => ∀ a, P !! a = some pg → (∀ p, ownHas P a p → ownHas P q p) →
      ownHas P q b)
    (motive_3 := fun _ _ _ => True)
    (fun a pg hpg hA => hA a (ownHas.root a pg hpg))
    (fun a _ _ hpg _ ih hA => ih a hpg hA)
    (fun pg i _ hfl hi _ ih a hpa hA =>
      ih (fun p hp => hA p (ownHas.child a pg i p hpa hfl hi hp)))
    (fun pg i _ hfl hi hbf _ _ a hpa hA =>
      absurd hbf (hpl a pg (hA a (ownHas.root a pg hpa)) hpa hfl i hi))
    (fun _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ => trivial)
    h (fun _ hp => hp)

/-- An extent of `X`'s positions of `bl`: a position and its extent. -/
theorem mem_extents (X : WX) (bl : Loc) (e : w64 × Nat) :
    e ∈ X.extents bl ↔ ∃ pid ∈ X.positions bl, X.posExtent bl pid = some e := by
  unfold WX.extents; rw [List.mem_filterMap]

end fl

section opened
variable [GooseExts]
variable (X : WX) (c : Loc) (B C : BRec) (name : List w8) (g : Nat)
variable (hok : wOK X) (hB : X.t.bs !! X.rl = some B) (hc : X.t.bs !! c = none)
  (hbm : B.bm !! name = none)

local notation "XO'" => WOpen.XO X X.rl c B C name (name, g)

include hB hc in
theorem XO_c_ne : c ≠ X.rl := WOpen.c_ne_bl X X.rl c B hB hc

include hok hB hc hbm in
theorem XO_positions_old (k : Loc) (hk : k ≠ c) : (XO').positions k = X.positions k := by
  unfold WX.positions
  rw [WOpen.XO_rootPid_old X X.rl c B C name (name, g) hB hc k hk,
    lposF_congr' _ (ltree X) k (fun q => by rw [WOpen.XO_ltree_old X X.rl c B C name (name, g) hB hc k hk])]
  have hf : (XO').fuel = X.fuel + 1 := by
    unfold WX.fuel; rw [WOpen.XO_size X X.rl c B C name (name, g) hB hc]; rfl
  rw [hf]
  exact wOK_positions_fuel X k hok 1

include hB hc hbm in
theorem XO_posExtent_old (k : Loc) (hk : k ≠ c) (pid : w64) :
    (XO').posExtent k pid = X.posExtent k pid := by
  refine Write.posExtent_eq X (XO') k pid rfl ?_
  rw [WOpen.XO_bs X X.rl c B C name (name, g)]
  simp only [hk, ↓reduceIte]
  by_cases hkr : k = X.rl
  · subst hkr; rw [hB]; simp only [↓reduceIte, Option.map_some]; rfl
  · simp only [hkr, ↓reduceIte]

include hB hc hbm in
theorem XO_bktLoc (n : GoString) :
    bktLoc (XO') n = if n = name then some c else bktLoc X n := by
  unfold bktLoc
  rw [show (XO').rl = X.rl from rfl, WOpen.XO_bs X X.rl c B C name (name, g)]
  simp only [Ne.symm (XO_c_ne X c B hB hc), ↓reduceIte, Option.bind_some, hB]
  by_cases hn : n = name
  · subst hn; simp
  · simp only [hn, ↓reduceIte]
    exact GMap.lookup_insert_ne _ _ (Ne.symm hn)

end opened

open WOpen in
/-- **Opening a top-level bucket keeps the freelist's agreement** (`flViewU`; U6x's OPEN
`flViewU_bktOpened_root`, proved with `wOK X'`, which `Bucket.Bucket_w`'s post gives). -/
theorem flViewU_bktOpened_root' [GooseExts] (X X' : WX) (c : Loc) (name : List w8) (g : Nat)
    (fl : FLPg) (hok : wOK X) (hok' : wOK X') (h : bktOpened X X' X.rl c name g)
    (hf : flViewU X fl) : flViewU X' fl := by
  obtain ⟨B, C, w, hB, hw, hk, hflag, hbm, hcn, hbo, hib, htx, hrn, hnm, hbm', hns, hil, hni,
    hX⟩ := h
  have hc : X.t.bs !! c = none := ((GMap.lookup_union_None _ _ _).1
    (Option.isNone_iff_eq_none.1 hbo)).1
  have hbmn : B.bm !! name = none := hk ▸ hbm
  have hXO : X' = XO X X.rl c B C name (name, g) := by rw [hX]; rfl
  subst hXO
  have hcr := XO_c_ne X c B hB hc
  have hv : viewWF X.v := hok.2.2.2.2.2.2.2
  have hCb : (XO X X.rl c B C name (name, g)).t.bs !! c = some C := by rw [XO_bs]; simp
  have hres : ∀ p, resolve C p = none := by
    intro p; unfold resolve; split
    · simp [hrn]
    · rw [hnm]; rfl
  have hpid : ∀ p, Write.posIdOf C p = p := by intro p; unfold Write.posIdOf; rw [hres]
  -- the opened bucket's extents
  have hpeC : ∀ p, (XO X X.rl c B C name (name, g)).posExtent c p =
      if p = W64 0 then none else (X.v.pages !! p.toNat).map fun pg => (p, 1 + pageOverflow pg) := by
    intro p; rw [Write.posExtent_def, hCb]; simp only [hpid]; rfl
  have hroot : rootEnts (XO X X.rl c B C name (name, g)) = rootEnts X := by
    unfold rootEnts
    rw [show (XO X X.rl c B C name (name, g)).rl = X.rl from rfl,
      XO_leaves_old X X.rl c B C name (name, g) hB hc hbmn hok X.rl (Ne.symm hcr)]
  have hbL := XO_bktLoc X c B C name g hB hc hbmn
  have hbLn : bktLoc X name = none := by unfold bktLoc; rw [hB]; exact hbmn
  have hpos := XO_positions_old X c B C name g hok hB hc hbmn
  have hpe := XO_posExtent_old X c B C name g hB hc hbmn
  have hrw : (w.key, w.value) ∈ rootEnts X := by
    unfold WX.allEnts at hw
    obtain ⟨ws, hws, hw⟩ := List.mem_flatten.1 hw
    unfold rootEnts
    exact List.mem_flatMap.2 ⟨ws, hws, List.mem_filterMap.2 ⟨w, hw, by simp [hflag]⟩⟩
  rw [hk] at hrw
  have hdisj : pagesDisjoint X.v.pages := by
    obtain ⟨C0, hC0, hvC⟩ := hv
    rw [show X.v.pages = C0.pages by rw [← hvC]; rfl]; exact hC0.2.2.1
  -- the opened bucket covers what its value's tree covers
  have hcovC : ∀ s, (∃ pid ∈ (XO X X.rl c B C name (name, g)).positions c, ∃ e,
      (XO X X.rl c B C name (name, g)).posExtent c pid = some e ∧ e.1.toNat ≤ s ∧
        s < e.1.toNat + e.2) ↔ bucketCovers X.v.pages w.value s := by
    intro s
    have hr : C.ib.root'.toNat = inBucketRoot w.value := by rw [hib]; rfl
    have hrp : (XO X X.rl c B C name (name, g)).rootPid c = C.ib.root' := by
      unfold WX.rootPid; rw [hCb]; rfl
    by_cases h0 : inBucketRoot w.value = 0
    · -- inline: no extent, and an inline page of plain entries has no page
      have hC0 : C.ib.root' = W64 0 := by apply BitVec.eq_of_toNat_eq; rw [hr, h0]; rfl
      have hg : inlineGood C.ipg :=
        ((hok'.1.2.2.2.2.2 c C hCb).1.1 hC0 hrn).2.2.1
      obtain ⟨-, hipg, -⟩ := hil h0
      rw [hipg] at hg
      constructor
      · rintro ⟨pid, hp, e, he, -⟩
        unfold WX.positions at hp
        rw [hrp, hC0] at hp
        have hL : ltree (XO X X.rl c B C name (name, g)) c (W64 0) =
            some (true, pageWs (inlinePage w.value)) := by
          unfold ltree; rw [hCb]; simp only; rw [hres]
          simp [wpageAt, hC0, hipg, hg.2.1]
        obtain ⟨n, hn⟩ : ∃ n, (XO X X.rl c B C name (name, g)).fuel = n + 1 := ⟨_, rfl⟩
        rw [hn] at hp
        simp only [lposF, hL, List.mem_cons, List.not_mem_nil, or_false] at hp
        subst hp
        rw [hpeC] at he; simp at he
      · rintro ⟨id, pg, hbh, -⟩
        cases hbh with
        | file _ _ h0' _ => exact absurd h0 h0'
        | inline _ _ _ hph =>
          cases hph with
          | child _ i _ hfl _ _ => rw [hg.2.1] at hfl; simp [leafPageFlag, branchPageFlag] at hfl
          | bucket _ i _ _ hi hbf _ =>
            have := (hg.2.2.2.2 i hi).2
            rw [hbf] at this; simp [bucketLeafFlag] at this
    · -- a file bucket: its positions are its own pages, and its pages are its own
      have hC0 : C.ib.root' ≠ W64 0 := by intro e; apply h0; rw [← hr, e]; rfl
      have hL : ∀ q, ltree (XO X X.rl c B C name (name, g)) c q = viewL X.v c c q := by
        intro q
        unfold ltree viewL; rw [hCb]; simp only [↓reduceIte]; rw [hres]
        simp only [wpageAt, hC0, ↓reduceIte, Option.map_map]
        rfl
      have hP : (XO X X.rl c B C name (name, g)).positions c =
          lposF (viewL X.v c) c (XO X X.rl c B C name (name, g)).fuel C.ib.root' := by
        unfold WX.positions; rw [hrp]; exact lposF_congr' _ _ c hL _ _
      have hpl : ∀ p pg, ownHas X.v.pages (inBucketRoot w.value) p → X.v.pages !! p = some pg →
          pageFlags pg = leafPageFlag → ∀ i < pageCount pg, leafFlags pg i % 2 ≠ bucketLeafFlag := by
        intro p pg ho hpg hl i hi hb
        have hps := hok'.1.2.1.2.2.2.1 c C hCb (inBucketRoot w.value) p pg
          (Or.inl ⟨hrn, hC0, hr.symm⟩) ho hpg hl i hi
        exact hcr (hps.1.1 hb)
      constructor
      · rintro ⟨pid, hp, e, he, h1, h2⟩
        rw [hpeC] at he
        by_cases hp0 : pid = W64 0
        · rw [if_pos hp0] at he; cases he
        rw [if_neg hp0] at he
        cases hpg : X.v.pages !! pid.toNat with
        | none => rw [hpg] at he; cases he
        | some pg =>
          rw [hpg] at he
          simp only [Option.map_some, Option.some.injEq] at he
          subst he
          rw [hP] at hp
          have ho := lposF_viewL_own X.v hv c _ _ pid pg hp hpg
          rw [hr] at ho
          exact ⟨pid.toNat, pg, bucketHas.file _ _ h0 (ownHas_treeHas' ho), hpg, h1, h2⟩
      · rintro ⟨id, pg, hbh, hpg, h1, h2⟩
        have ht : treeHas X.v.pages (inBucketRoot w.value) id := by
          cases hbh with
          | file _ _ _ ht => exact ht
          | inline _ _ h0' _ => exact absurd h0' h0
        have ho := ownHas_of_treeHas' hpl ht
        have hid2 := (Read.viewWF_page X.v hv id pg hpg).1
        have hid64 : id < 2 ^ 64 := by have := hf.2.2.1 id pg hpg; omega
        have hidt : (W64 (id : Int)).toNat = id := by
          simp only [BitVec.toNat_ofInt]; omega
        refine ⟨W64 (id : Int), ?_, (W64 (id : Int), 1 + pageOverflow pg), ?_, ?_, ?_⟩
        · rw [hP]
          apply lposF_viewL_complete X.v hv c _ C.ib.root' id (by rw [hr]; exact ho)
          have := Write.treeMeasure_le X.v.pages C.ib.root'
          have hfu : (XO X X.rl c B C name (name, g)).v = X.v := rfl
          unfold WX.fuel; rw [hfu]; omega
        · have hne0 : W64 (id : Int) ≠ W64 0 := by
            intro e; have := congrArg BitVec.toNat e; rw [hidt] at this; simp at this; omega
          rw [hpeC, if_neg hne0, hidt, hpg]; rfl
        · simp only [hidt]; exact h1
        · simp only [hidt]; exact h2
  -- `lCovers` is kept
  have hcov : ∀ s, lCovers (XO X X.rl c B C name (name, g)) s ↔ lCovers X s := by
    intro s
    unfold lCovers
    rw [hroot, show (XO X X.rl c B C name (name, g)).v = X.v from rfl]
    constructor
    · rintro (⟨bl, e, hbl, he, h1, h2⟩ | ⟨n, v0, hn, hbn, hbc⟩)
      · by_cases hbc : bl = c
        · subst hbc
          rw [mem_extents] at he
          obtain ⟨pid, hp, hpe'⟩ := he
          exact Or.inr ⟨name, w.value, hrw, hbLn, (hcovC s).1 ⟨pid, hp, e, hpe', h1, h2⟩⟩
        · refine Or.inl ⟨bl, e, ?_, ?_, h1, h2⟩
          · rw [XO_bs] at hbl; simp only [hbc, ↓reduceIte] at hbl
            by_cases hbr : bl = X.rl
            · subst hbr; rw [hB]; simp
            · simpa [hbr] using hbl
          · rw [mem_extents] at he ⊢
            obtain ⟨pid, hp, hpe'⟩ := he
            exact ⟨pid, by rw [← hpos bl hbc]; exact hp, by rw [← hpe bl hbc]; exact hpe'⟩
      · rw [hbL] at hbn
        by_cases hnn : n = name
        · rw [if_pos hnn] at hbn; cases hbn
        · rw [if_neg hnn] at hbn
          exact Or.inr ⟨n, v0, hn, hbn, hbc⟩
    · rintro (⟨bl, e, hbl, he, h1, h2⟩ | ⟨n, v0, hn, hbn, hbc⟩)
      · have hbc : bl ≠ c := by intro e; subst e; exact hbl hc
        refine Or.inl ⟨bl, e, ?_, ?_, h1, h2⟩
        · rw [XO_bs]; simp only [hbc, ↓reduceIte]
          by_cases hbr : bl = X.rl
          · simp [hbr]
          · simpa [hbr] using hbl
        · rw [mem_extents] at he ⊢
          obtain ⟨pid, hp, hpe'⟩ := he
          exact ⟨pid, by rw [hpos bl hbc]; exact hp, by rw [hpe bl hbc]; exact hpe'⟩
      · by_cases hnn : n = name
        · subst hnn
          obtain ⟨w', hw', -, hk', hv'⟩ := mem_rootEnts X n v0 hn
          have := WOpen.allEnts_key_inj X hok X.rl B hB w' w hw' hw (by rw [hk', hk])
          subst this
          rw [← hv'] at hbc
          obtain ⟨pid, hp, e, hpe', h1, h2⟩ := (hcovC s).2 hbc
          refine Or.inl ⟨c, e, by rw [hCb]; simp, ?_, h1, h2⟩
          rw [mem_extents]; exact ⟨pid, hp, hpe'⟩
        · refine Or.inr ⟨n, v0, hn, ?_, hbc⟩
          rw [hbL, if_neg hnn]; exact hbn
  -- `covU` is kept: an opened bucket's position stands for its old root entry
  have hcovU : covU (XO X X.rl c B C name (name, g)) := by
    let gw : CovW → CovW := fun
      | .pos bl pid => if bl = c then .bkt name else .pos bl pid
      | .bkt n => .bkt n
    have hmap : ∀ s d, coverW (XO X X.rl c B C name (name, g)) s d → coverW X s (gw d) := by
      intro s d hd
      cases d with
      | pos bl pid =>
        obtain ⟨hbl, hp, e, hpe', h1, h2⟩ := hd
        by_cases hbc : bl = c
        · subst hbc
          simp only [gw, ↓reduceIte]
          exact ⟨w.value, hrw, hbLn, (hcovC s).1 ⟨pid, hp, e, hpe', h1, h2⟩⟩
        · simp only [gw, hbc, ↓reduceIte]
          refine ⟨?_, by rw [← hpos bl hbc]; exact hp, e, by rw [← hpe bl hbc]; exact hpe', h1, h2⟩
          rw [XO_bs] at hbl; simp only [hbc, ↓reduceIte] at hbl
          by_cases hbr : bl = X.rl
          · subst hbr; rw [hB]; simp
          · simpa [hbr] using hbl
      | bkt n =>
        obtain ⟨v0, hn, hbn, hbc⟩ := hd
        rw [hroot] at hn
        rw [hbL] at hbn
        by_cases hnn : n = name
        · rw [if_pos hnn] at hbn; cases hbn
        · rw [if_neg hnn] at hbn
          exact ⟨v0, hn, hbn, hbc⟩
    intro s d1 d2 h1 h2
    have he := hf.2.1 s _ _ (hmap s d1 h1) (hmap s d2 h2)
    -- a position of the opened bucket
    have hposc : ∀ pid, coverW (XO X X.rl c B C name (name, g)) s (.pos c pid) →
        ∃ pg, X.v.pages !! pid.toNat = some pg ∧ pid.toNat ≤ s ∧ s < pid.toNat + (1 + pageOverflow pg) := by
      intro pid hd
      obtain ⟨-, -, e, hpe', h1, h2⟩ := hd
      rw [hpeC] at hpe'
      by_cases hp0 : pid = W64 0
      · rw [if_pos hp0] at hpe'; cases hpe'
      rw [if_neg hp0] at hpe'
      cases hpg : X.v.pages !! pid.toNat with
      | none => rw [hpg] at hpe'; cases hpe'
      | some pg =>
        rw [hpg] at hpe'
        simp only [Option.map_some, Option.some.injEq] at hpe'
        subst hpe'
        exact ⟨pg, rfl, h1, h2⟩
    have hbktn : ¬ coverW (XO X X.rl c B C name (name, g)) s (.bkt name) := by
      rintro ⟨v0, -, hbn, -⟩
      rw [hbL, if_pos rfl] at hbn; cases hbn
    cases d1 with
    | pos bl1 p1 =>
      cases d2 with
      | pos bl2 p2 =>
        by_cases hb1 : bl1 = c
        · by_cases hb2 : bl2 = c
          · subst hb1 hb2
            obtain ⟨pg1, hpg1, a1, b1⟩ := hposc p1 h1
            obtain ⟨pg2, hpg2, a2, b2⟩ := hposc p2 h2
            by_cases hpp : p1.toNat = p2.toNat
            · rw [BitVec.eq_of_toNat_eq hpp]
            · rcases hdisj _ _ _ _ hpg1 hpg2 hpp with h | h <;> omega
          · simp only [gw, hb1, hb2, ↓reduceIte] at he; cases he
        · by_cases hb2 : bl2 = c
          · simp only [gw, hb1, hb2, ↓reduceIte] at he; cases he
          · simpa [gw, hb1, hb2] using he
      | bkt n2 =>
        by_cases hb1 : bl1 = c
        · simp only [gw, hb1, ↓reduceIte, CovW.bkt.injEq] at he
          subst he; exact absurd h2 hbktn
        · simp [gw, hb1] at he
    | bkt n1 =>
      cases d2 with
      | pos bl2 p2 =>
        by_cases hb2 : bl2 = c
        · simp only [gw, hb2, ↓reduceIte, CovW.bkt.injEq] at he
          subst he; exact absurd h1 hbktn
        · simp [gw, hb2] at he
      | bkt n2 => simpa [gw] using he
  exact ⟨Write.flView_congr X _ fl rfl hcov hf.1, hcovU, hf.2.2.1, hf.2.2.2⟩

end PubW

end bbolt
end EtcdGrove
end Perennial
