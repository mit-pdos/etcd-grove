/-
**A view page can be materialized** (batch 20 item 9, `notes/bbolt-proof-plan.md`): `matReady`
for a page position of a bucket with a root page (not inline), from the view's well-formedness
(every view page is a well-formed tree page: its header id, a leaf or a branch, its elements inside
it and below `MaxAllocSize`, its keys non-empty) and the writer's view cells (the page's bytes lie
in `(0, maxAddr]`, `wtxW`'s `viewCells`).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Ctx
public import Proof.go_etcd_io.bbolt.Read.TreeFacts
public import Proof.go_etcd_io.bbolt.Read.Bytes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [GooseExts]

/-- **A page of a well-formed view, readable**: its header's id, a leaf or a branch,
`ReadInodeFromPage` can read it, and its elements lie inside it. -/
theorem viewWF_page_ready (v : View) (hv : viewWF v) (id : Nat) (pg : List w8)
    (hpg : v.pages !! id = some pg) :
    pageId pg = id ∧ pg ≠ [] ∧ (pageFlags pg = leafPageFlag ∨ pageFlags pg = branchPageFlag) ∧
      pageReadable pg ∧ pageElemsIn pg := by
  obtain ⟨C, hok, hvC⟩ := hv
  have hpv : v.pages = C.pages := by rw [← hvC]; rfl
  rw [hpv] at hpg
  have hin : treePages C.pages C.root !! id = some pg := by rw [hok.2.1]; exact hpg
  unfold treePages at hin
  rw [GMap.mapLookup_filter_Some] at hin
  have hhas : treeHas C.pages C.root id := by simpa using hin.2
  have hw := Read.treeHas_treeWF C.pages C.hwm hhas hok.1.1
  have hgood := hok.1.2.1.1 id pg hpg
  cases hw with
  | page _ pg' h2 hlt hpg' hid hlen hpt =>
    rw [hpg] at hpg'; cases hpg'
    have hne : pg ≠ [] := by intro e; rw [e] at hlen; simp at hlen; omega
    refine ⟨hid, hne, ?_⟩
    cases hpt with
    | leaf _ _ hf hl _ =>
      refine ⟨Or.inl hf, ⟨?_, fun i hi => ⟨?_, ?_⟩⟩, leafWF_elemsIn pg _ hl hf⟩
      · have := hl.1; have := hl.2.1; omega
      · simp only [hf, ite_true]; exact (hgood.1 hf i hi).1
      · simp only [elemEnd, hf, ite_true]; exact (hl.2.2.1 i hi).2
    | branch _ _ hf hb _ =>
      have hnl : pageFlags pg ≠ leafPageFlag := by rw [hf]; decide
      refine ⟨Or.inr hf, ⟨?_, fun i hi => ⟨?_, ?_⟩⟩, branchWF_elemsIn pg _ _ hb hf⟩
      · have := hb.2.1; have := hb.2.2.1; omega
      · simp only [hnl, ite_false]; exact hgood.2 hf i hi
      · simp only [elemEnd, hnl, ite_false]; exact (hb.2.2.2.1 i hi).2.1

/-- **`matReady` of a view page** (pure): a bucket with a root page, a page of the well-formed
view not in the page cache, at a location whose bytes lie in `(0, maxAddr]`. -/
theorem matReady_view (X : WX) (B : BRec) (pgid : w64) (pg : List w8)
    (hroot : B.ib.root' ≠ W64 0) (hv : viewWF X.v) (hpg : X.v.pages !! pgid.toNat = some pg)
    (hpm : X.t.pm !! pgid = none)
    (hbnd : 0 < (pageLoc X.v pgid.toNat).addr ∧
      (pageLoc X.v pgid.toNat).addr + pg.length ≤ maxAddr) :
    matReady X B pgid := by
  obtain ⟨hid, -, hf, hrd, hin⟩ := viewWF_page_ready X.v hv pgid.toNat pg hpg
  refine ⟨pageLoc X.v pgid.toNat, pg, ?_, hrd, hf, hin, ?_, hpm, fun h => absurd h hroot,
    hbnd.1, hbnd.2, fun i hi => ?_⟩
  · simp only [wpageAt, hroot, ite_false, hpg, Option.map_some, pageLoc]
  · unfold pageId at hid
    apply BitVec.eq_of_toNat_eq
    exact hid
  · have := hin i hi; omega

end pure

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The writer's view page lies in `(0, maxAddr]`** (its bytes, `wtxW`'s view cells). -/
theorem wtxW_page_bounds (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (id : Nat)
    (pg : List w8) (hpg : X.v.pages !! id = some pg) (hne : pg ≠ []) :
    wtxW (GF := GF) K tx r m X ⊢
      ⌜0 < (pageLoc X.v id).addr ∧ (pageLoc X.v id).addr + pg.length ≤ maxAddr⌝ := by
  unfold wtxW
  iintro ⟨-, Hv, -⟩
  icases viewCells_page_acc _ X.v id pg hpg $$ Hv with ⟨Hb, -⟩
  iapply Read.bytesPointsto_in_bounds _ _ pg hne $$ Hb

/-- **A view page position can be materialized** (`Bucket.node`'s `matReady`, batch 20 item 9):
a bucket with a root page, a page of the view not in the page cache, under `wtxW` (the view's
well-formedness is `wOK`'s/`wOKR`'s/`bktLocalOK`'s last clause). -/
theorem wtxW_matReady (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (B : BRec)
    (pgid : w64) (pg : List w8) (hroot : B.ib.root' ≠ W64 0) (hv : viewWF X.v)
    (hpg : X.v.pages !! pgid.toNat = some pg) (hpm : X.t.pm !! pgid = none) :
    wtxW (GF := GF) K tx r m X ⊢ ⌜matReady X B pgid⌝ := by
  have hne := (viewWF_page_ready X.v hv pgid.toNat pg hpg).2.1
  iintro H
  icases wtxW_page_bounds K tx r m X pgid.toNat pg hpg hne $$ H with %Hb
  ipureintro
  exact matReady_view X B pgid pg hroot hv hpg hpm Hb

end iris

end bbolt
end EtcdGrove
end Perennial
