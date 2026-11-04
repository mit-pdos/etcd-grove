/-
`Bucket.spill` (U9o, `notes/bbolt-proof-plan.md`): **a nested bucket's unspilled tree at the
start of the root bucket's spill**. From the spill's pre (`spillPre`, its `wOKR`), the committed
state `C` of the view (`treeOK`, its pages the view's, its mark below the writer's), and the
buffers empty (`txClean`: nothing allocated yet), a cached child bucket `c` other than the root,
with a root node, is the top of an unspilled tree (`uTree`, at the spill's page map and mark,
within `(-∞, ∞)`) whose elements are plain and are its plain entries: `bkPre`'s tree clauses
(`InitB` built with no nested bucket values, `HtB.nodeHts`, `uTree_init_node`, `bk_plain`).

The view-page premise (`hpage`) is `posShape`'s for a bucket other than the root once batch 38's
S1 lands (`0 < leafKsize ∧ ksize + vsize ≤ bboltEntryMax`).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.BktPlain
public import Proof.go_etcd_io.bbolt.Spill.BktHtNodes
public import Proof.go_etcd_io.bbolt.Rebalance.RblReady
public import Proof.go_etcd_io.bbolt.Spill.DerefRel
public import Proof.go_etcd_io.bbolt.Spill.BktFinal

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

/-- A leaf node's entries in a bucket other than the root are plain (`leafShape`,
`entriesBounded`). -/
theorem plainE_node {X : WX} (hok : wOKR X) {c : Loc} {C : BRec} (hC : X.t.bs !! c = some C)
    (hne : c ≠ X.rl) : ∀ l r, C.ns !! l = some r → r.nv.isLeaf' = true → ∀ w ∈ r.ws, plainE w := by
  intro l r hr hl w hw
  have hsh := hok.1.2.1.2.2.1 c C hC l r hr hl w hw
  have hb := hok.2.2.2.1 c C hC l r hr w hw
  exact ⟨(notBkt_iff _).1 (fun h => hne (hsh.1 h)), hb.1, hb.2⟩

/-- **A nested bucket's tree at the start of the spill** (see the module doc). -/
theorem bk_init {X : WX} {fl : FLPg} (hpre : spillPre X fl) (hreach : liveReach X)
    (C0 : CommitSt) (hcok : treeOK C0) (hcp : X.v.pages = C0.pages)
    (hch : C0.hwm ≤ X.t.mv.pgid'.toNat) (hext : pagesExt X.v.pages)
    {c : Loc} {C : BRec} (hC : X.t.bs !! c = some C) (hne : c ≠ X.rl)
    (hrn : C.bv.rootNode' ≠ null)
    (hpage : ∀ c0 p pg, posRoot C c0 → ownHas X.v.pages c0 p → X.v.pages !! p = some pg →
      pageFlags pg = leafPageFlag → ∀ i < pageCount pg,
        leafFlags pg i % 2 = 0 ∧ 0 < leafKsize pg i ∧ leafKsize pg i + leafVsize pg i ≤ bboltEntryMax) :
    ∃ rn h F D N E, X.node c C.bv.rootNode' = some rn ∧ rn.nv.parent' = null ∧
      uTree X c (spP X) X.t.mv.pgid'.toNat C.bv.rootNode' none none h F D N E ∧
      E.map (fun e => (e.2.1, e.2.2)) = lbktEnts X c ∧ plainEls E := by
  have hok := hpre.1
  have htc := hok.1
  have hcl : bktClean X.v X.t.mv.pgid'.toNat c C := (htc.2.2.2.2.2 c C hC).1
  obtain ⟨bnd, hkeys⟩ := (hok.2.1 c C hC).1
  have hlive : ∀ l r, C.ns !! l = some r → l ∈ X.live :=
    fun l r hr => wOKR_nsLive X hok c C l r hC hr
  obtain ⟨r0, hr0⟩ : ∃ r0, C.ns !! C.bv.rootNode' = some r0 := by
    obtain ⟨r, hr, -⟩ := (hcl.2.2.2.2.1 _ _ (hcl.2.2.2.1 hrn)).2; exact ⟨r, hr⟩
  have hpar : r0.nv.parent' = null := hkeys.2.1 r0 hr0
  have hres : resolve C C.ib.root' = some C.bv.rootNode' := by
    unfold resolve
    by_cases h0 : C.ib.root' = W64 0
    · rw [if_pos h0, if_neg hrn]
    · rw [if_neg h0]; exact hcl.2.2.2.1 hrn
  obtain ⟨pht, hpht⟩ := pageHts_of_viewWF X.v hok.2.2.2.2.2.2.2
  rw [hcp] at hpht
  have hHt : HtB X c C C0 pht bnd :=
    { hB := hC, clean := hcl, keys := hkeys,
      ne2 := fun l r hr hl => (hpre.2.1 c C hC l r hr (hlive l r hr)).2 hl,
      cpages := hcp, hpht := hpht, rn := hrn,
      reach := by
        intro l r hr
        obtain ⟨rt, hrt, hd⟩ := hreach.2 c C l r hC hr (hlive l r hr)
        rw [nodeRootIn_unique hrt (nodeRootIn.top _ r0 hr0 hpar)] at hd
        exact hd,
      rt := hpre.2.2.2.1 c (by rw [hC]; simp) }
  obtain ⟨ht, hhts, hfuel⟩ := hHt.nodeHts
  have hbufs : X.t.bufs = ∅ := htc.2.1.2.1
  have hI : InitB X c C (spP X) C0 pht ht bnd (fun _ _ => []) :=
    { hB := hC, clean := hcl, keys := hkeys, live := hlive,
      ne := fun l r hr => hpre.2.1 c C hC l r hr (hlive l r hr),
      bound := fun l r hr w hw => (hok.2.2.2.1 c C hC l r hr w hw).2,
      cok := hcok, cpages := hcp, chwm := hch, hpht := hpht, ext := by rw [← hcp]; exact hext,
      agree := by
        intro x pg hx
        unfold spP
        have hbp : X.bufPages !! x = none := by
          cases hb : X.bufPages !! x with
          | none => rfl
          | some pg' =>
            have := bufPages_lookup hb
            rw [hbufs] at this; simp at this
        rw [GMap.lookup_union_r _ _ _ hbp, hcp]; exact hx,
      hts := hhts,
      sb := by
        intro l r i w hr hl hw
        have hwm : w ∈ r.ws := List.mem_of_getElem? hw
        have hnb : ¬ isBktFlag w.flags := fun h =>
          hne ((htc.2.1.2.2.1 c C hC l r hr hl w hwm).1 h)
        exact ⟨fun h => absurd h hnb, fun _ => rfl⟩ }
  obtain ⟨F, D, N, E, hu, hE, -, -⟩ :=
    uTree_init_node hI X.fuel C.bv.rootNode' r0 C.ib.root' hr0 hres hfuel
  have hbnd : bnd C.bv.rootNode' = (none, none) := (hkeys.2.2 _ r0 hr0).2.1 hpar
  rw [hbnd] at hu
  obtain ⟨hpl, hents⟩ := bk_plain hC hcl hrn (plainE_node hok hC hne) hpage hE
  have hnode : X.node c C.bv.rootNode' = some r0 := by unfold WX.node; rw [hC]; exact hr0
  exact ⟨r0, ht C.bv.rootNode', F, D, N, E, hnode, hpar, hu, hents, hpl⟩

end start

end Spill

end bbolt
end EtcdGrove
end Perennial
