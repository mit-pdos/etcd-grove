/-
`Bucket.spill`'s root loop's end (U9x8, `notes/bbolt-proof-plan.md`): **the root bucket's
unspilled tree at the loop's end, given its nested values** (`end_uTree`, for
`BktEndTree.end_rootTree`). With a root node, the root bucket's record at the end (`RInv.rootOK`:
clean, searchable, its nodes non-empty below the root and branches of two entries, its entries
bounded, its logical tree finite; `spG`'s `liveReach`: every node below the root node) and the
committed state (`RInv.cok`, the view's pages the committed ones) are `InitB`'s premises but the
nested values (`hsb`: each bucket entry of a leaf node a `bvalS` with slots `Sb`), and the heights
(`HtB.nodeHts`). Its elements are the root bucket's logical leaves' (`uTree_init_node`).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.BktEndPost
public import Proof.go_etcd_io.bbolt.Spill.BktInit
public import Proof.go_etcd_io.bbolt.Spill.BktHtNodes
public import Proof.go_etcd_io.bbolt.Rebalance.RblReady

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

/-- **The view's pages are in the spill's page map** (no buffer is a view page, `spG`). -/
theorem spP_agree {X : WX} {txid : w64} {ml : Nat} {fl : FLPg} (hG : spG X txid ml fl)
    (hext : pagesExt X.v.pages) : pagesLe X.v.pages (spP X) := by
  intro x pg hx
  show (X.bufPages ∪ X.v.pages) !! x = some pg
  have hbp : X.bufPages !! x = none := by
    cases hb : X.bufPages !! x with
    | none => rfl
    | some pg' =>
      exfalso
      have h1 := bufPages_lookup hb
      have h2 := (hG.2.2.2.2.2.2.2.1 (W64 (x : Int)) (by rw [h1]; rfl)).2.2
      have hx64 : x < 2 ^ 64 := by have := hext x pg hx; omega
      rw [w64_cast_toNat hx64, hx] at h2
      cases h2
  rw [GMap.lookup_union_r _ _ _ hbp]; exact hx

/-- **The root bucket's unspilled tree at the end, given its nested values** (see the module
doc). -/
theorem end_uTree {X0 X : WX} {w0 w : WDb} {B0 B : BRec} {keys : List GoString}
    {Lroot : List Nat} {st : List FLStep} {Dc : GoString → List Nat} {ks : GoString → KSt}
    (hI : RInv X0 w0 B0 keys Lroot X w st Dc ks) (hB : X.t.bs !! X0.rl = some B)
    (hrn : B.bv.rootNode' ≠ null) (hvC : X.v = View.ofC X.v.base w.C)
    (hext : pagesExt X0.v.pages) {Sb : Loc → Nat → List Nat}
    (hsb : ∀ l r i w', B.ns !! l = some r → r.nv.isLeaf' = true → r.ws[i]? = some w' →
      (isBktFlag w'.flags → bvalS (spP X) X.t.mv.pgid'.toNat w'.value (Sb l i)) ∧
      (¬ isBktFlag w'.flags → Sb l i = [])) :
    ∃ rn h F D N E, X.node X0.rl B.bv.rootNode' = some rn ∧ rn.nv.parent' = null ∧
      rn.nv.spilled' = false ∧
      uTree X X0.rl (spP X) X.t.mv.pgid'.toNat B.bv.rootNode' none none h F D N E ∧
      (X.leaves X0.rl).flatMap (List.map wEl) = E := by
  obtain ⟨hloc, hrt, B', hB', hne⟩ := hI.rootOK
  rw [hB] at hB'; cases hB'
  obtain ⟨-, B'', hB'', hcl, ⟨bnd, hkeys⟩, -, hlive, hvwf⟩ := hloc
  rw [hB] at hB''; cases hB''
  have hcp : X.v.pages = w0.C.pages := by
    have := congrArg View.pages hvC
    simp only [View.ofC] at this
    rw [this, hI.C]
  have hext' : pagesExt X.v.pages := by rw [hI.pages]; exact hext
  have hreach : liveReach X := hI.G.2.2.2.2.1
  obtain ⟨r0, hr0⟩ : ∃ r0, B.ns !! B.bv.rootNode' = some r0 := by
    obtain ⟨r, hr, -⟩ := (hcl.2.2.2.2.1 _ _ (hcl.2.2.2.1 hrn)).2; exact ⟨r, hr⟩
  have hpar : r0.nv.parent' = null := hkeys.2.1 r0 hr0
  have hres : resolve B B.ib.root' = some B.bv.rootNode' := by
    unfold resolve
    by_cases h0 : B.ib.root' = W64 0
    · rw [if_pos h0, if_neg hrn]
    · rw [if_neg h0]; exact hcl.2.2.2.1 hrn
  obtain ⟨pht, hpht⟩ := pageHts_of_viewWF X.v hvwf
  rw [hcp] at hpht
  have hHt : HtB X X0.rl B w0.C pht bnd :=
    { hB := hB, clean := hcl, keys := hkeys,
      ne2 := fun l r hr hl => ((hne l r hr).1).2 hl,
      cpages := hcp, hpht := hpht, rn := hrn,
      reach := by
        intro l r hr
        obtain ⟨rt, hrt', hd⟩ := hreach.2 X0.rl B l r hB hr (hlive l r hr)
        rw [nodeRootIn_unique hrt' (nodeRootIn.top _ r0 hr0 hpar)] at hd
        exact hd,
      rt := hrt }
  obtain ⟨ht, hhts, hfuel⟩ := hHt.nodeHts
  have hag := spP_agree hI.G hext'
  have hInit : InitB X X0.rl B (spP X) w0.C pht ht bnd Sb :=
    { hB := hB, clean := hcl, keys := hkeys, live := hlive,
      ne := fun l r hr => (hne l r hr).1,
      bound := fun l r hr w' hw => ((hne l r hr).2 w' hw).2,
      cok := hI.cok, cpages := hcp,
      chwm := Nat.le_trans hI.hwm0 hI.mark, hpht := hpht,
      ext := by rw [← hcp]; exact hext',
      agree := fun x pg hx => hag x pg (by rw [hcp]; exact hx),
      hts := hhts, sb := hsb }
  obtain ⟨F, D, N, E, hu, hE, -, -⟩ :=
    uTree_init_node hInit X.fuel B.bv.rootNode' r0 B.ib.root' hr0 hres hfuel
  have hbnd : bnd B.bv.rootNode' = (none, none) := (hkeys.2.2 _ r0 hr0).2.1 hpar
  rw [hbnd] at hu
  have hnode : X.node X0.rl B.bv.rootNode' = some r0 := by unfold WX.node; rw [hB]; exact hr0
  have hsp : r0.nv.spilled' = false := (hcl.2.2.2.2.2.2.2.1 _ r0 hr0).2.2.2.2.2.2.1
  refine ⟨r0, ht B.bv.rootNode', F, D, N, E, hnode, hpar, hsp, hu, ?_⟩
  have hp : X.rootPid X0.rl = B.ib.root' := by unfold WX.rootPid; rw [hB]; rfl
  unfold WX.leaves; rw [hp]; exact hE

end init

end Spill

end bbolt
end EtcdGrove
end Perennial
