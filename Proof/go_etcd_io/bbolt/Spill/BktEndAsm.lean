/-
`Bucket.spill`'s root loop's end (U9x9, `notes/bbolt-proof-plan.md`): **lemmas for the root
bucket's tree at the end** (`BktEndTree.end_rootTree`). From the root's local facts alone
(`bktLocalOK`, not `wOKR`): a leaf node's entries are the bucket's (`mem_allEnts_nodeL`), an
uncached nested value in a leaf node is a `bvalS` (`bvalS_uncachedL`). Of an unspilled tree: it
owns every nested slot of its elements (`entCov_D`), and its base pages are covered by the walk's
positions (`uTree_F_cov`). A slot a root position covers at the end is the root's own
(`own_Lroot`, `RInv.rootExt`).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.BktEndDisj
public import Proof.go_etcd_io.bbolt.Read.TreeEnts

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section asm
variable [GooseExts]

/-- **A leaf node's entries are the bucket's** (`mem_allEnts_node` from `bktLocalOK`). -/
theorem mem_allEnts_nodeL {X : WX} (hreach : liveReach X) {bl : Loc} (hloc : bktLocalOK X bl)
    (hrt : rtOK X bl) {B : BRec} (hB : X.t.bs !! bl = some B) (h0 : B.ib.root' ≠ W64 0)
    {l : Loc} {r : NRec} (hr : B.ns !! l = some r) (hl : r.nv.isLeaf' = true) {w : WEntry}
    (hw : w ∈ r.ws) : w ∈ X.allEnts bl := by
  obtain ⟨-, B', hB', hcl, ⟨bnd, hbk⟩, -, hlive, -⟩ := hloc
  rw [hB] at hB'; cases hB'
  obtain ⟨rt, hrtI, hd⟩ := hreach.2 bl B l r hB hr (hlive l r hr)
  have hpos := node_pos X bl B hB hcl hbk.2.1 hrt h0 rt l hrtI hd r hr
  have hL := ltree_node_rbl X bl B hB hcl h0 l r hr
  rw [hl] at hL
  exact mem_allEnts_pos hrt hpos hL hw

/-- **An uncached nested bucket's value in a leaf node** is a `bvalS` (`bvalS_uncached` from
`bktLocalOK`). -/
theorem bvalS_uncachedL {X : WX} {C : CommitSt} {bl : Loc} (hloc : bktLocalOK X bl)
    (hcok : treeOK C) (hcp : X.v.pages = C.pages) {hwm : Nat} (hch : C.hwm ≤ hwm) {P : Pages}
    (hag : ∀ x pg, X.v.pages !! x = some pg → P !! x = some pg)
    {R : BRec} (hR : X.t.bs !! bl = some R) {l : Loc} {r : NRec} (hr : R.ns !! l = some r)
    (hl : r.nv.isLeaf' = true) {w : WEntry} (hw : w ∈ r.ws) (hb : isBktFlag w.flags)
    (hnc : R.bm !! w.key = none) :
    ∃ S, bvalS P hwm w.value S ∧ ∀ s, s ∈ pgSlots P S ↔ bucketCovers X.v.pages w.value s := by
  obtain ⟨-, R', hR', hcl, ⟨bnd, hbk⟩, -, -, -⟩ := hloc
  rw [hR] at hR'; cases hR'
  have hnc' := (hcl.2.2.2.2.2.2.2.1 l r hr).2.2.2.2.2.2.2.2.2.2.2.1 hl w hw hb
  have hv := hnc'.1 (by rw [hnc]; rfl)
  have hnk := hbk.2.2 l r hr
  exact bvalS_view hcok hcp hch hag hv
    (fun h0 => hnk.2.2.2.2.2 hl w hw hb h0 (by unfold opened; rw [hnc]; simp))

/-- **An unspilled tree owns every nested slot of its elements.** -/
theorem entCov_D {X : WX} {bl : Loc} {P : Pages} {hwm : Nat} {n : Loc}
    {lo hi : Option (List w8)} {h : Nat} {F D : List Nat} {N : List Loc} {E : List El}
    (hu : uTree X bl P hwm n lo hi h F D N E) :
    ∀ e ∈ E, e.1 % 2 = 1 → ∀ s, bucketCovers P e.2.2 s → s ∈ D :=
  uTree.rec (X := X) (bl := bl) (P := P) (hwm := hwm)
    (motive_1 := fun _ _ _ _ _ D _ E _ => ∀ e ∈ E, e.1 % 2 = 1 → ∀ s, bucketCovers P e.2.2 s → s ∈ D)
    (motive_2 := fun _ _ _ _ _ _ _ _ e _ =>
      ∀ x ∈ e.E, x.1 % 2 = 1 → ∀ s, bucketCovers P x.2.2 s → s ∈ e.D)
    (fun n r _ _ Sb _ _ _ _ hsb _ => by
      intro e he hb s hs
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 he
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
      have hbk : isBktFlag r.ws[i].flags := (isBkt_iff _).2 hb
      have hS := hsb i _ (List.getElem?_eq_getElem hi) hbk
      obtain ⟨x, pg, hbh, hpg, h1, h2⟩ := hs
      refine List.mem_append_right _ (List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, ?_⟩)
      exact mem_pgSlots_of ((bvalS_has hS x).1 hbh) hpg h1 h2)
    (fun _ r _ _ _ es _ _ _ _ hlen _ _ _ _ _ _ ih => by
      intro e he hb s hs
      obtain ⟨u, hu, heu⟩ := List.mem_flatMap.1 he
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hu
      have hj' : j < r.ws.length := by rw [← hlen]; exact hj
      have := ih j _ _ (List.getElem?_eq_getElem hj') (List.getElem?_eq_getElem hj) e heu hb s hs
      exact List.mem_append_right _ (List.mem_flatMap.2 ⟨_, hu, this⟩))
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih => ih)
    (fun _ _ _ _ _ _ _ w S E hfT => by
      intro e he hb s hs
      have hs' := hfT.1
      rw [← hfT.2.2] at he
      unfold treeEls at he
      obtain ⟨pg, hpg, he⟩ := List.mem_flatMap.1 he
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 he
      rw [List.mem_range] at hj
      obtain ⟨L, hL, hown, hlf, -⟩ := TreeEnts.leavesF_leaf P _ _ _ _ hs'.keys pg hpg
      have hbf : leafFlags pg j % 2 = bucketLeafFlag := by unfold bucketLeafFlag; exact hb
      obtain ⟨x, xpg, hbh, hxpg, h1, h2⟩ := hs
      have ht : treeHas P w.pgid.toNat x :=
        treeHas_trans (treeHas_of_ownHas hown) (treeHas_bucket hL hlf hj hbf hbh)
      exact mem_pgSlots_of ((hs'.has x).1 ht) hxpg h1 h2)
    hu

/-- **An unspilled tree's base pages are covered by the walk's positions.** -/
theorem uTree_F_cov {X : WX} {bl : Loc} {B : BRec} (hB : X.t.bs !! bl = some B)
    {hwm' : Nat} (hcl : bktClean X.v hwm' bl B) (h0 : B.ib.root' ≠ W64 0)
    {t : RTree} (ht : ltIs (ltree X) bl t) (hpos : X.positions bl = t.pos)
    {P : Pages} {hwm : Nat} {n : Loc} {lo hi : Option (List w8)} {h : Nat} {F D : List Nat}
    {N : List Loc} {E : List El} (hu : uTree X bl P hwm n lo hi h F D N E) :
    ∀ pid, resolve B pid = some n → pid ∈ t.pos → ∀ x ∈ F, ∃ q, coverW X x (.pos bl q) :=
  uTree.rec (X := X) (bl := bl) (P := P) (hwm := hwm)
    (motive_1 := fun n _ _ _ F _ _ _ _ => ∀ pid, resolve B pid = some n → pid ∈ t.pos →
      ∀ x ∈ F, ∃ q, coverW X x (.pos bl q))
    (motive_2 := fun _ _ _ _ _ _ _ w e _ => w.pgid ∈ t.pos → ∀ x ∈ e.F, ∃ q, coverW X x (.pos bl q))
    (fun n r _ _ _ hnode huN _ _ _ _ => by
      intro pid hres hpt x hx
      have hr := node_ns hB hnode
      exact ⟨pid, coverW_ownSl hB hres hr huN.2.2.2.2.2.2.2 (by rw [hpos]; exact hpt)
        (ownF_ownSl _ _ x hx)⟩)
    (fun n r _ _ _ es hnode huN hleaf _ hlen hent _ _ _ _ _ ih => by
      intro pid hres hpt x hx
      have hr := node_ns hB hnode
      have hL : ltree X bl pid = some (false, r.ws) := by
        simp only [ltree, hB, hres, hr, Option.map_some, hleaf]
      rcases List.mem_append.1 hx with hx | hx
      · exact ⟨pid, coverW_ownSl hB hres hr huN.2.2.2.2.2.2.2 (by rw [hpos]; exact hpt)
          (ownF_ownSl _ _ x hx)⟩
      · obtain ⟨u, hu, hxu⟩ := List.mem_flatMap.1 hx
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hu
        have hj' : j < r.ws.length := by rw [← hlen]; exact hj
        exact ih j _ _ (List.getElem?_eq_getElem hj') (List.getElem?_eq_getElem hj)
          (pos_childT ht hpt hL hj') x hxu)
    (fun _ _ _ _ _ _ _ w c rc _ _ _ _ _ hnode _ hpg _ _ _ _ ih => by
      intro hpt x hx
      have hr := node_ns hB hnode
      have hnm : B.nm !! rc.nv.pgid' = some c := (hcl.2.2.2.2.2.2.2.1 c rc hr).2.2.2.2.2.2.2.1
      rw [hpg] at hnm
      have hres : resolve B w.pgid = some c := by unfold resolve; rw [if_neg h0]; exact hnm
      exact ih w.pgid hres hpt x hx)
    (fun _ _ _ _ _ _ _ _ _ _ _ => by intro _ x hx; cases hx)
    hu

section ctx
variable {X0 X : WX} {w0 w : WDb} {B0 : BRec} {keys : List GoString} {Lroot : List Nat}
  {st : List FLStep} {Dc : GoString → List Nat} {ks : GoString → KSt}

/-- **A slot a root position covers at the end is the root's own** (`RInv.rootExt`). -/
theorem own_Lroot (hpre : spillPre X0 w0.fl) (hreach : liveReach X0) (hfv : flViewU X0 w0.fl)
    (hB0 : X0.t.bs !! X0.rl = some B0) (hk : ∀ k, k ∈ keys ↔ (B0.bm !! k).isSome)
    (hI : RInv X0 w0 B0 keys Lroot X w st Dc ks) {s : Nat} {q : w64}
    (hq : coverW X s (.pos X0.rl q)) : s ∈ Lroot := by
  obtain ⟨Dc0, hL, hDc0⟩ := hI.lroot
  obtain ⟨-, hqp, e1, he1, h1, h2⟩ := hq
  have hmem : e1 ∈ X0.extents X0.rl := by
    rw [← hI.rootExt]; exact List.mem_filterMap.2 ⟨q, hqp, he1⟩
  obtain ⟨pid, hpid⟩ := coverW_of_extent (by rw [hB0]; simp) hmem h1 h2
  rw [hL]; exact mem_rootOwn_pos hpre hreach hfv hk hDc0 hpid

end ctx

end asm

end Spill

end bbolt
end EtcdGrove
end Perennial
