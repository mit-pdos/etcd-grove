/-
`Bucket.spill`'s initial trees (U9i, `notes/bbolt-proof-plan.md`), part 4: **the unspilled tree
of a clean bucket** (`uTree_init_node`). A bucket whose record is clean (`bktClean`, its keys'
bounds `bnd`), its nodes live, non-empty below the root, branches of at least two entries, its
entries within `bboltEntryMax`, its nodes of heights `ht` (a leaf `0`, a branch one more than its
children, a page child's the base tree's `pht`), its nested buckets' values `bvalS` (slots `Sb`),
over a page map `P` holding the committed tree's pages: from each node, an unspilled tree whose
leaf elements are the logical tree's entries from it (`lleaves`), its nodes below it.

The premises are `InitB`; `Spill/BktInitTop` derives them from `spillPre` (but the heights and
the entry bound, see there).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.BktFin
public import Proof.go_etcd_io.bbolt.Spill.BktInitLem
public import Proof.go_etcd_io.bbolt.Spill.TreeElsFuel
public import Proof.go_etcd_io.bbolt.Read.BktOK

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section init
variable [GooseExts]

/-- **The premises of a bucket's initial unspilled tree** (see the module doc). -/
structure InitB (X : WX) (bl : Loc) (B : BRec) (P : Pages) (C : CommitSt) (pht : Nat → Nat)
    (ht : Loc → Nat) (bnd : Loc → Option (List w8) × Option (List w8))
    (Sb : Loc → Nat → List Nat) : Prop where
  hB : X.t.bs !! bl = some B
  clean : bktClean X.v X.t.mv.pgid'.toNat bl B
  keys : bktKeysB X.v B bnd
  live : ∀ l r, B.ns !! l = some r → l ∈ X.live
  ne : ∀ l r, B.ns !! l = some r →
    (r.nv.parent' ≠ null → 0 < r.ws.length) ∧ (r.nv.isLeaf' = false → 2 ≤ r.ws.length)
  bound : ∀ l r, B.ns !! l = some r → ∀ w ∈ r.ws, w.key.length + w.value.length ≤ bboltEntryMax
  cok : treeOK C
  cpages : X.v.pages = C.pages
  chwm : C.hwm ≤ X.t.mv.pgid'.toNat
  hpht : pageHts C.pages pht
  ext : pagesExt C.pages
  agree : ∀ x pg, C.pages !! x = some pg → P !! x = some pg
  hts : ∀ l r, B.ns !! l = some r → (r.nv.isLeaf' = true → ht l = 0) ∧
    (r.nv.isLeaf' = false → ∀ w ∈ r.ws, (∀ c, B.nm !! w.pgid = some c → ht c + 1 = ht l) ∧
      (B.nm !! w.pgid = none → pht w.pgid.toNat + 1 = ht l))
  sb : ∀ l r i w, B.ns !! l = some r → r.nv.isLeaf' = true → r.ws[i]? = some w →
    (isBktFlag w.flags → bvalS P X.t.mv.pgid'.toNat w.value (Sb l i)) ∧
    (¬ isBktFlag w.flags → Sb l i = [])

variable {X : WX} {bl : Loc} {B : BRec} {P : Pages} {C : CommitSt} {pht : Nat → Nat}
  {ht : Loc → Nat} {bnd : Loc → Option (List w8) × Option (List w8)} {Sb : Loc → Nat → List Nat}

theorem InitB.nc (H : InitB X bl B P C pht ht bnd Sb) {l : Loc} {r : NRec}
    (hr : B.ns !! l = some r) : nodeClean X.v X.t.mv.pgid'.toNat bl B l r :=
  H.clean.2.2.2.2.2.2.2.1 l r hr

theorem InitB.nk (H : InitB X bl B P C pht ht bnd Sb) {l : Loc} {r : NRec}
    (hr : B.ns !! l = some r) : nodeKeys X.v B bnd l r :=
  H.keys.2.2 l r hr

/-- A node's location is not nil. -/
theorem InitB.nonnull (H : InitB X bl B P C pht ht bnd Sb) {l : Loc} {r : NRec}
    (hr : B.ns !! l = some r) : l ≠ null :=
  (H.clean.2.2.2.2.1 _ l (H.nc hr).2.2.2.2.2.2.2.1).1

/-- A cached page's node has that page. -/
theorem InitB.nm_node (H : InitB X bl B P C pht ht bnd Sb) {p : w64} {c : Loc}
    (h : B.nm !! p = some c) : ∃ rc, B.ns !! c = some rc ∧ rc.nv.pgid' = p :=
  (H.clean.2.2.2.2.1 p c h).2

/-- A child's height is one less than its parent's. -/
theorem InitB.par_ht (H : InitB X bl B P C pht ht bnd Sb) :
    ∀ x r, B.ns !! x = some r → r.nv.parent' ≠ null → ht x + 1 = ht r.nv.parent' := by
  intro x r hr hp
  obtain ⟨rp, hrp, hpl, -, w, hw, hwp⟩ := (H.nc hr).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hp
  have hnm : B.nm !! w.pgid = some x := by rw [hwp]; exact (H.nc hr).2.2.2.2.2.2.2.1
  exact ((H.hts _ rp hrp).2 hpl w hw).1 x hnm

/-- A branch's bucket has a root page. -/
theorem InitB.root_ne (H : InitB X bl B P C pht ht bnd Sb) {l : Loc} {r : NRec}
    (hr : B.ns !! l = some r) (hl : r.nv.isLeaf' = false) : B.ib.root' ≠ W64 0 := by
  intro h0
  have := H.clean.2.2.2.2.2.2.1 h0 l r hr
  rw [hl] at this; cases this

theorem resolve_nm {B : BRec} {p : w64} {c : Loc} (h0 : B.ib.root' ≠ W64 0)
    (h : B.nm !! p = some c) : resolve B p = some c := by
  unfold resolve; rw [if_neg h0]; exact h

/-- The logical tree at a node's position. -/
theorem InitB.ltree_node (H : InitB X bl B P C pht ht bnd Sb) {l : Loc} {r : NRec} {pid : w64}
    (hr : B.ns !! l = some r) (hres : resolve B pid = some l) :
    ltree X bl pid = some (r.nv.isLeaf', r.ws) := by
  unfold ltree; rw [H.hB]; simp only; rw [hres]; simp only [hr, Option.map_some]

/-- The logical tree over a page position's subtree reads its pages. -/
theorem InitB.ltree_pages (H : InitB X bl B P C pht ht bnd Sb) {l : Loc} {r : NRec} {i : Nat}
    {w : WEntry} (hr : B.ns !! l = some r) (hl : r.nv.isLeaf' = false) (hw : r.ws[i]? = some w)
    (hnm : B.nm !! w.pgid = none) :
    ∀ q : w64, treeHas C.pages w.pgid.toNat q.toNat → ltree X bl q = (C.pages !! q.toNat).map pgRead := by
  intro q hq
  have h0 := H.root_ne hr hl
  have hpos : pagePosAt B l i w.pgid := ⟨r, w, hr, hl, hw, rfl, hnm⟩
  have hq' : treeHas X.v.pages w.pgid.toNat q.toNat := by rw [H.cpages]; exact hq
  have hfree := H.clean.2.2.2.2.2.2.2.2.2.1 l i w.pgid hpos q.toNat hq'
  rw [show W64 (q.toNat : Int) = q by simp] at hfree
  unfold ltree; rw [H.hB]; simp only
  have hres : resolve B q = none := by unfold resolve; rw [if_neg h0]; exact hfree
  rw [hres]; simp only
  unfold wpageAt; rw [if_neg h0, Option.map_map, H.cpages]; rfl

theorem uTree_N_nodup {X : WX} {bl : Loc} {P : Pages} {hwm : Nat} {n : Loc}
    {lo hi : Option (List w8)} {h : Nat} {F D : List Nat} {N : List Loc} {E : List El}
    (hu : uTree X bl P hwm n lo hi h F D N E) : N.Nodup := by
  cases hu with
  | leaf => simp
  | branch _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hnd => exact hnd

theorem uTree_mem_N {X : WX} {bl : Loc} {P : Pages} {hwm : Nat} {n : Loc}
    {lo hi : Option (List w8)} {h : Nat} {F D : List Nat} {N : List Loc} {E : List El}
    (hu : uTree X bl P hwm n lo hi h F D N E) : n ∈ N := by
  cases hu with
  | leaf => exact List.mem_singleton_self _
  | branch => exact List.mem_cons_self

theorem uEnt_N_nodup {X : WX} {bl : Loc} {P : Pages} {hwm : Nat} {n : Loc}
    {lo hi : Option (List w8)} {ws : List WEntry} {cs : List Loc} {h i : Nat} {w : WEntry} {e : UE}
    (he : uEnt X bl P hwm n lo hi ws cs h i w e) : e.N.Nodup := by
  cases he with
  | child _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hu => exact uTree_N_nodup hu
  | fin => exact List.nodup_nil

/-- **The unspilled tree from a node** (see the module doc). -/
theorem uTree_init_node (H : InitB X bl B P C pht ht bnd Sb) :
    ∀ n l r pid, B.ns !! l = some r → resolve B pid = some l → ht l < n →
      ∃ F D N E, uTree X bl P X.t.mv.pgid'.toNat l (bnd l).1 (bnd l).2 (ht l) F D N E ∧
        (lleaves (ltree X) bl n pid).flatMap (List.map wEl) = E ∧ (∀ x ∈ N, upTo B x l) ∧
        ∀ c ∈ r.cs, c ∈ N
  | 0, _, _, _, _, _, hn => absurd hn (Nat.not_lt_zero _)
  | n + 1, l, r, pid, hr, hres, hn => by
    have hnc := H.nc hr
    have hnk := H.nk hr
    obtain ⟨c1, c2, c3, c4, c5, -, c7, c8, c9, c10, -, -, c13, -, c15, c16, c17⟩ := hnc
    obtain ⟨k1, -, -, k4, -⟩ := hnk
    have hnode : X.node bl l = some r := by unfold WX.node; rw [H.hB]; exact hr
    have hL := H.ltree_node hr hres
    have hl0 := H.nonnull hr
    have huN : uNode X bl l r (bnd l).1 (bnd l).2 := by
      refine ⟨H.live l r hr, c1, c7, c2, c3, c4,
        fun w hw => ⟨k1 w hw, c5 w hw, H.bound l r hr w hw⟩, ?_⟩
      intro hp0
      have h0 : B.ib.root' ≠ W64 0 := fun e => hp0 (c9 e)
      cases c10 h0 with
      | page _ pg h2 _ hpg hid hlen hpt =>
        refine ⟨pg, hpg, ?_, hid, ?_, h2, H.ext _ pg (by rw [← H.cpages]; exact hpg)⟩
        · rw [hlen]; have : 1 ≤ 1 + pageOverflow pg := by omega
          have := Nat.mul_le_mul_right 4096 this; omega
        · cases hpt with
          | leaf _ _ hf => exact Or.inr hf
          | branch _ _ hf => exact Or.inl hf
    cases hleaf : r.nv.isLeaf' with
    | true =>
      have hcs : r.cs = [] := by
        cases hcs' : r.cs with
        | nil => rfl
        | cons c _ =>
          obtain ⟨rc, hrc, hpc⟩ := c17 c (by rw [hcs']; exact List.mem_cons_self)
          have hpn : rc.nv.parent' ≠ null := by rw [hpc]; exact hl0
          obtain ⟨rp, hrp, hpl, -⟩ := (H.nc hrc).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hpn
          rw [hpc, hr] at hrp; cases hrp
          rw [hleaf] at hpl; cases hpl
      have h0 : ht l = 0 := (H.hts l r hr).1 hleaf
      rw [h0]
      refine ⟨_, _, _, _, uTree.leaf l r _ _ (Sb l) hnode huN hleaf hcs
        (fun i w hw hb => (H.sb l r i w hr hleaf hw).1 hb)
        (fun i w hw hb => (H.sb l r i w hr hleaf hw).2 hb), ?_, ?_, ?_⟩
      · simp only [lleaves, hL, hleaf, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      · intro x hx; rw [List.mem_singleton.1 hx]; exact upTo.refl l
      · intro c hc; rw [hcs] at hc; cases hc
    | false =>
      have h0 := H.root_ne hr hleaf
      have h2 := (H.ne l r hr).2 hleaf
      obtain ⟨-, hpnd, hch⟩ := c13 hleaf
      obtain ⟨-, kind, hkch⟩ := k4 hleaf
      have hhts := (H.hts l r hr).2 hleaf
      obtain ⟨hk, hhk⟩ : ∃ k, ht l = k + 1 := by
        obtain ⟨w, hw⟩ : ∃ w, w ∈ r.ws := ⟨r.ws[0], List.getElem_mem (by omega)⟩
        cases hnm : B.nm !! w.pgid with
        | some c => exact ⟨ht c, ((hhts w hw).1 c hnm).symm⟩
        | none => exact ⟨pht w.pgid.toNat, ((hhts w hw).2 hnm).symm⟩
      -- every entry
      have hent : ∀ i (hi : i < r.ws.length), ∃ e : UE,
          uEnt X bl P X.t.mv.pgid'.toNat l (bnd l).1 (bnd l).2 r.ws r.cs hk i r.ws[i] e ∧
          e.ch = B.nm !! r.ws[i].pgid ∧
          e.E = (lleaves (ltree X) bl n r.ws[i].pgid).flatMap (List.map wEl) ∧
          (∀ x ∈ e.N, ∃ c, e.ch = some c ∧ upTo B x c) ∧ (∀ c, e.ch = some c → c ∈ e.N) := by
        intro i hi
        have hwi : r.ws[i]? = some r.ws[i] := List.getElem?_eq_getElem hi
        have hwm : r.ws[i] ∈ r.ws := List.getElem_mem hi
        cases hnm : B.nm !! r.ws[i].pgid with
        | some c =>
          obtain ⟨rc, hrc, hpg⟩ := H.nm_node hnm
          obtain ⟨-, hpar, -⟩ := hch r.ws[i] hwm
          obtain ⟨rc', hrc', hpc⟩ := hpar c hnm
          rw [hrc] at hrc'; cases hrc'
          have hpn : rc.nv.parent' ≠ null := by rw [hpc]; exact hl0
          have hhc : ht c + 1 = ht l := (hhts _ hwm).1 c hnm
          obtain ⟨F, D, N, E, hu, hE, hN, hNc⟩ :=
            uTree_init_node H n c rc r.ws[i].pgid hrc (resolve_nm h0 hnm) (by omega)
          obtain ⟨kn1, rp, j, w, hrp, hwj, hwp, hwk, hbnd⟩ := (H.nk hrc).2.2.1 hpn
          rw [hpc, hr] at hrp; cases hrp
          have hji : j = i := by
            apply nodup_idx hpnd (a := rc.nv.pgid')
            · rw [List.getElem?_map, hwj]; simp [hwp]
            · rw [List.getElem?_map, hwi]; simp [hpg]
          subst hji
          rw [hwi] at hwj; cases hwj
          rw [hbnd, hpc, wEntryBnd_eq] at hu
          have hcm : c ∈ r.cs := by
            obtain ⟨rp, hrp, -, hcin, -⟩ := (H.nc hrc).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hpn
            rw [hpc, hr] at hrp; cases hrp; exact hcin
          refine ⟨⟨some c, F, D, N, E⟩, ?_, rfl, hE.symm, fun x hx => ⟨c, rfl, hN x hx⟩,
            fun c' hc' => by cases hc'; exact uTree_mem_N hu⟩
          refine uEnt.child l _ _ r.ws r.cs hk j r.ws[j] c rc F D N E hcm
            (by unfold WX.node; rw [H.hB]; exact hrc) hpc hpg hwk.symm kn1
            ⟨(H.ne c rc hrc).1 hpn, hNc⟩ ?_
          have : ht c = hk := by omega
          rw [← this]; exact hu
        | none =>
          obtain ⟨-, hpgk⟩ := hkch i r.ws[i] hwi
          obtain ⟨pg, hpg, hcnt, -, hkey, hkeys⟩ := hpgk hnm
          rw [H.cpages] at hpg hkeys
          have hwf : treeWF C.pages X.t.mv.pgid'.toNat r.ws[i].pgid.toNat := by
            rw [← H.cpages]; exact (hch r.ws[i] hwm).2.2 hnm
          have hph : pht r.ws[i].pgid.toNat + 1 = ht l := (hhts _ hwm).2 hnm
          have hag : ∀ x ∈ subPages C.pages r.ws[i].pgid.toNat, P !! x = C.pages !! x := by
            intro x hx
            obtain ⟨pg', hpg'⟩ := treeHas_page (mem_subPages.1 hx)
            rw [hpg']; exact H.agree x pg' hpg'
          have hf := fTree_base C H.cok hpg hcnt hkey hkeys pht H.hpht P X.t.mv.pgid'.toNat
            H.chwm hag
          rw [wEntryBnd_eq] at hf
          have hph' : pht r.ws[i].pgid.toNat = hk := by omega
          rw [hph'] at hf
          refine ⟨⟨none, [], pgSlots P (subPages C.pages r.ws[i].pgid.toNat), [],
            treeEls P r.ws[i].pgid.toNat⟩, uEnt.fin l _ _ r.ws r.cs hk i r.ws[i] _ _ hf, rfl, ?_,
            fun x hx => by simp at hx, fun c' hc' => by cases hc'⟩
          show treeEls P r.ws[i].pgid.toNat = _
          rw [lleaves_pages (ltree X) bl C.pages X.t.mv.pgid'.toNat n r.ws[i].pgid hwf
            (H.ltree_pages hr hleaf hwi hnm), leavesF_els]
          unfold treeEls
          rw [← treeLeaves_sTree_agree hf.1 (fun x hx => (hag x hx).symm)]
          unfold treeLeaves
          rw [leavesF_pht C.pages X.t.mv.pgid'.toNat pht H.hpht _ n _ hwf
            (by have := pht_lt_size C.pages _ pht H.hpht _ hwf; omega) (by omega)]
      let f : Fin r.ws.length → UE := fun i => Classical.choose (hent i.1 i.2)
      have hf : ∀ i : Fin r.ws.length, _ := fun i => Classical.choose_spec (hent i.1 i.2)
      have hes : ∀ i e, (List.ofFn f)[i]? = some e → ∃ hi : i < r.ws.length, e = f ⟨i, hi⟩ := by
        intro i e he
        rw [List.getElem?_ofFn] at he
        split at he
        · rename_i hi; cases he; exact ⟨hi, rfl⟩
        · cases he
      -- the children's nodes
      have hNup : ∀ i e x, (List.ofFn f)[i]? = some e → x ∈ e.N →
          ∃ hi : i < r.ws.length, ∃ c, B.nm !! r.ws[i].pgid = some c ∧ upTo B x c := by
        intro i e x he hx
        obtain ⟨hi, rfl⟩ := hes i e he
        obtain ⟨c, hc, hup⟩ := (hf ⟨i, hi⟩).2.2.2.1 x hx
        exact ⟨hi, c, by rw [← (hf ⟨i, hi⟩).2.1]; exact hc, hup⟩
      have hcht : ∀ i (hi : i < r.ws.length) c, B.nm !! r.ws[i].pgid = some c → ht c = hk := by
        intro i hi c hc
        have := (hhts _ (List.getElem_mem hi)).1 c hc; omega
      have hcne : ∀ i j (hi : i < r.ws.length) (hj : j < r.ws.length) c, i ≠ j →
          B.nm !! r.ws[i].pgid = some c → B.nm !! r.ws[j].pgid ≠ some c := by
        intro i j hi hj c hij hci hcj
        obtain ⟨rc, hrc, hp1⟩ := H.nm_node hci
        obtain ⟨rc', hrc', hp2⟩ := H.nm_node hcj
        rw [hrc] at hrc'; cases hrc'
        apply hij
        apply nodup_idx hpnd (a := rc.nv.pgid')
        · rw [List.getElem?_map, List.getElem?_eq_getElem hi]; simp [hp1]
        · rw [List.getElem?_map, List.getElem?_eq_getElem hj]; simp [hp2]
      have hcov : ∀ c ∈ r.cs, ∃ j, ∃ hj : j < r.ws.length, (f ⟨j, hj⟩).ch = some c := by
        intro c hc
        obtain ⟨rc, hrc, hpc⟩ := c17 c hc
        have hpn : rc.nv.parent' ≠ null := by rw [hpc]; exact hl0
        obtain ⟨-, rp, j, w, hrp, hwj, hwp, -⟩ := (H.nk hrc).2.2.1 hpn
        rw [hpc, hr] at hrp; cases hrp
        have hj : j < r.ws.length := (List.getElem?_eq_some_iff.1 hwj).1
        refine ⟨j, hj, ?_⟩
        rw [(hf ⟨j, hj⟩).2.1]
        rw [List.getElem?_eq_getElem hj] at hwj; cases hwj
        rw [hwp]; exact (H.nc hrc).2.2.2.2.2.2.2.1
      refine ⟨ownF r.nv.pgid' ++ (List.ofFn f).flatMap UE.F,
        ownSl X.v r.nv.pgid' ++ (List.ofFn f).flatMap UE.D, l :: (List.ofFn f).flatMap UE.N,
        (List.ofFn f).flatMap UE.E, ?_, ?_, ?_, ?_⟩
      · rw [hhk]
        refine uTree.branch l r _ _ hk (List.ofFn f) hnode huN hleaf h2 (by simp) ?_ ?_ ?_ c16 ?_ ?_
        · intro i w e hw he
          obtain ⟨hi, rfl⟩ := hes i e he
          rw [List.getElem?_eq_getElem hi] at hw; cases hw
          exact (hf ⟨i, hi⟩).1
        · apply filterMap_nodup_of
          intro i j x y b hij hx hy hfx hfy
          obtain ⟨hi, rfl⟩ := hes i x hx
          obtain ⟨hj, rfl⟩ := hes j y hy
          rw [(hf ⟨i, hi⟩).2.1] at hfx
          rw [(hf ⟨j, hj⟩).2.1] at hfy
          exact hcne i j hi hj b (by omega) hfx hfy
        · intro c hc
          left
          obtain ⟨j, hj, hjc⟩ := hcov c hc
          exact ⟨f ⟨j, hj⟩, List.mem_ofFn.2 ⟨⟨j, hj⟩, rfl⟩, hjc⟩
        · refine List.nodup_cons.2 ⟨?_, ?_⟩
          · intro hm
            obtain ⟨e, he, hx⟩ := List.mem_flatMap.1 hm
            obtain ⟨i, hi', rfl⟩ := List.getElem_of_mem he
            obtain ⟨hi, c, hc, hup⟩ := hNup i _ l (List.getElem?_eq_getElem hi') hx
            have := hcht i hi c hc
            rcases upTo_ht H.par_ht hup with e | lt
            · subst e; omega
            · omega
          · apply nodup_flatMap_of
            · intro e he
              obtain ⟨⟨i, hi⟩, rfl⟩ := List.mem_ofFn.1 he
              exact uEnt_N_nodup (hf ⟨i, hi⟩).1
            · intro i j a b x hij ha hb hxa hxb
              obtain ⟨hi, c, hc, hup⟩ := hNup i a x ha hxa
              obtain ⟨hj, c', hc', hup'⟩ := hNup j b x hb hxb
              have e1 := hcht i hi c hc
              have e2 := hcht j hj c' hc'
              have hcc : c = c' := by
                rcases upTo_lin hup hup' with h | h
                · rcases upTo_ht H.par_ht h with e | lt
                  · exact e
                  · omega
                · rcases upTo_ht H.par_ht h with e | lt
                  · exact e.symm
                  · omega
              subst hcc
              exact hcne i j hi hj c (by omega) hc hc'
        · intro hp0; exact absurd (c10 h0) (by
            rw [hp0]; intro hw; cases hw with | page _ _ h2' => simp at h2')
      · simp only [lleaves, hL, hleaf]
        rw [List.flatMap_assoc]
        apply flatMap_of_map_eq
        apply List.ext_getElem (by simp)
        intro i h1 h2'
        simp only [List.getElem_map, List.getElem_ofFn]
        exact ((hf ⟨i, by simpa using h1⟩).2.2.1).symm
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hm
        · exact upTo.refl _
        · obtain ⟨e, he, hxe⟩ := List.mem_flatMap.1 hm
          obtain ⟨i, hi', rfl⟩ := List.getElem_of_mem he
          obtain ⟨hi, c, hc, hup⟩ := hNup i _ x (List.getElem?_eq_getElem hi') hxe
          obtain ⟨rc, hrc, -⟩ := H.nm_node hc
          obtain ⟨-, hpar, -⟩ := hch r.ws[i] (List.getElem_mem hi)
          obtain ⟨rc', hrc', hpc⟩ := hpar c hc
          rw [hrc] at hrc'; cases hrc'
          refine upTo_trans hup (upTo.up c l rc hrc (by rw [hpc]; exact hl0) ?_)
          rw [hpc]; exact upTo.refl l
      · intro c hc
        obtain ⟨j, hj, hjc⟩ := hcov c hc
        refine List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨f ⟨j, hj⟩, List.mem_ofFn.2 ⟨⟨j, hj⟩, rfl⟩,
          (hf ⟨j, hj⟩).2.2.2.2 c hjc⟩)

end init

end Spill

end bbolt
end EtcdGrove
end Perennial
