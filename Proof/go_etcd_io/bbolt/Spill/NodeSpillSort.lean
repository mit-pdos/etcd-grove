/-
`node.spill`'s `sort.Sort(n.children)` (U9k, `notes/bbolt-proof-plan.md`): the sort as a call spec
(`nodes_sort_wp`) over a frame `sortQ X n` that is not a wand: the heap's node objects but `n`'s
(`objsBut`, read for any child `c ≠ n`), the view's cells (for view-backed first keys) and the
heap's disjointness and the view's base; and the accessor that takes `n`'s object, its bucket's
and `sortQ` out of `wtxW` (`wtxW_sort_acc`), with the way back to `wtxW` at `n`'s new record.

The interfaces (for the assembly in `node__spill.lean`):

* `wtxW_sort_acc K tx r m X bl B n rn hb hr hlive :
    wtxW K tx r m X ⊢ objOwn X.v n (DFrac.own 1) true (.node bl rn) ∗
      objOwn X.v bl (DFrac.own 1) (decide (bl ∈ X.liveB)) (.bkt B) ∗ sortQ X n ∗
      (∀ r', ⌜r'.nv.parent' ≠ n⌝ -∗ objOwn X.v n (DFrac.own 1) true (.node bl r') -∗
        objOwn X.v bl (DFrac.own 1) (decide (bl ∈ X.liveB)) (.bkt B) -∗ sortQ X n -∗
        wtxW K tx r m (X.setNode bl n r'))`
* `nodes_sort_wp hS hK hC X bl n cs s hkids hF hlen :
    {{ isPkgInit bbolt ∗ s ↦* cs ∗ sortQ X n }}
      sort.Sort(interface.mk nodes.ty #s)
    {{ RET #(); ∃ l, s ↦* l ∗ sortQ X n ∗ ⌜cs.Perm l⌝ }}`
  for `hkids : ∀ c ∈ cs, sortKid X bl n c` (`c ≠ n`, live, a node of `bl` with entries),
  `hF : liveFresh X` and `hlen : cs.length ≤ 2 ^ 62` (Perennial's `sort.Sort` bound; nothing
  in `node.spill`'s pre bounds a node's children count, so the caller supplies it).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.SortNodes
public import Proof.go_etcd_io.bbolt.Spill.NodeSpillHeap
public import Proof.go_etcd_io.bbolt.Read.WCtx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section defs
variable [GooseExts]

/-- The first inode's key slice of node `c` among the heap's objects (nil if none). -/
def kidKs (X : WX) (c : Loc) : GoSlice :=
  match X.t.objs !! c with
  | some (.node _ rc) => ((rc.ins[0]?).map Inode.key').getD slice.nil
  | _ => slice.nil

/-- The first entry's key of node `c` among the heap's objects (empty if none). -/
def kidFk (X : WX) (c : Loc) : List w8 :=
  match X.t.objs !! c with
  | some (.node _ rc) => ((rc.ws[0]?).map WEntry.key).getD []
  | _ => []

/-- **A child the sort reads** (of `n`, in bucket `bl`): not `n`, live, a node of `bl` with
entries (`Less` reads `inodes[0]`). -/
def sortKid (X : WX) (bl n c : Loc) : Prop :=
  c ≠ n ∧ c ∈ X.live ∧ ∃ rc, X.node bl c = some rc ∧ 0 < rc.ws.length

theorem kidKs_eq {X : WX} {c bl : Loc} {rc : NRec} {it : Inode}
    (h : X.t.objs !! c = some (.node bl rc)) (hi : rc.ins[0]? = some it) : kidKs X c = it.key' := by
  simp [kidKs, h, hi]

theorem kidFk_eq {X : WX} {c bl : Loc} {rc : NRec} {w : WEntry}
    (h : X.t.objs !! c = some (.node bl rc)) (hw : rc.ws[0]? = some w) : kidFk X c = w.key := by
  simp [kidFk, h, hw]

/-- Go's order on the first keys is a strict weak order on the children. -/
theorem swo_kidFk (X : WX) :
    _root_.Perennial.slices.StrictWeakOrder
      (fun a b : Loc => decide (go.GoStringLt (kidFk X a) (kidFk X b)) = true) := by
  have H := _root_.Perennial.slices.StrictWeakOrder_goStringLt
  refine ⟨fun x => by simpa using H.strict_weak_order_irrefl _, fun x y z h1 h2 => by
    simp only [decide_eq_true_eq] at h1 h2 ⊢; exact H.strict_weak_order_trans _ _ _ h1 h2, ?_⟩
  refine ⟨fun x => ?_, fun h => ?_, fun h1 h2 => ?_⟩
  · simp only [decide_eq_true_eq]
    exact H.strict_weak_order_equiv.refl _
  · simp only [decide_eq_true_eq] at h ⊢
    exact H.strict_weak_order_equiv.symm h
  · simp only [decide_eq_true_eq] at h1 h2 ⊢
    exact H.strict_weak_order_equiv.trans h1 h2

end defs

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The heap's node objects but `n`'s.** -/
def objsBut (X : WX) (n : Loc) : IProp GF :=
  iprop([∗map] l ↦ o ∈ X.t.objs.delete n, objOwn X.v l (DFrac.own 1) (decide (l ∈ X.live)) o)

/-- **The sort's frame**: the heap's disjointness and the view's base (pure), the node objects
but `n`'s, the view's cells. -/
def sortQ (X : WX) (n : Loc) : IProp GF :=
  iprop(⌜objsDisj X.t ∧ 0 < X.v.base.addr⌝ ∗ objsBut X n ∗ viewCells wq X.v)

omit hos in
/-- **The heap with `n`'s object, its bucket's and the other node objects out**, and back at a
new record of `n`. -/
theorem wtxHeap_sort_acc (tx : Loc) (X : WX) (bl : Loc) (B : BRec) (n : Loc) (rn : NRec)
    (hb : X.t.bs !! bl = some B) (hr : B.ns !! n = some rn) :
    wtxHeap (GF := GF) tx (DFrac.own 1) X ⊢
      objOwn X.v n (DFrac.own 1) (decide (n ∈ X.live)) (.node bl rn) ∗
      objOwn X.v bl (DFrac.own 1) (decide (bl ∈ X.liveB)) (.bkt B) ∗ objsBut X n ∗
      (∀ r', ⌜r'.nv.parent' ≠ n⌝ -∗
        objOwn X.v n (DFrac.own 1) (decide (n ∈ X.live)) (.node bl r') -∗
        objOwn X.v bl (DFrac.own 1) (decide (bl ∈ X.liveB)) (.bkt B) -∗ objsBut X n -∗
        wtxHeap tx (DFrac.own 1) (X.setNode bl n r')) := by
  unfold wtxHeap objsBut
  iintro ⟨%Hok, Hf, Hrf, Hm, Hbk⟩
  have Hd := Hok.2.1
  have Ho := objs_node X.t bl B n rn Hd hb hr
  icases (BigSepM.bigSepM_delete (M := GMap Loc) Ho).1 $$ Hm with ⟨Hn, Hm⟩
  icases (BigSepM.bigSepM_delete (M := GMap Loc) (bobjs_bkt X.t bl B hb)).1 $$ Hbk with ⟨Hb, Hbk⟩
  iframe Hn Hb Hm
  iintro %r' %Hpar Hn Hb Hm
  rw [setNode_eq X bl n B r' hb]
  isplitr
  · ipureintro; exact heapOK_setNode tx X bl B n rn r' Hok hb hr Hpar
  isplitl [Hf]
  · unfold txFields; simp only [WTx.setNodeT]; iexact Hf
  iframe
  rw [objs_setNodeT X.t bl n B rn r' Hd hb hr, bobjs_setNodeT X.t bl n B r']
  dsimp only
  isplitl [Hn Hm]
  · iapply (BigSepM.bigSepM_insert_delete (M := GMap Loc)).2
    iframe
  iapply (bigSepM_insert_same (Φ := fun l B => objOwn (GF := GF) X.v l (DFrac.own 1)
    (decide (l ∈ X.liveB)) (.bkt B)) _ bl B { B with ns := B.ns.insert n r' } (bobjs_bkt X.t bl B hb)
    (by simp only [objOwn, pageOwn])).2
  iapply (BigSepM.bigSepM_delete (M := GMap Loc) (bobjs_bkt X.t bl B hb)).2
  iframe

/-- **`n`'s object, its bucket's and the sort's frame, out of `wtxW`** (`n` live), and back at a
new record of `n` (see the module doc). -/
theorem wtxW_sort_acc (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (bl : Loc) (B : BRec)
    (n : Loc) (rn : NRec) (hb : X.t.bs !! bl = some B) (hr : B.ns !! n = some rn)
    (hlive : n ∈ X.live) :
    wtxW (GF := GF) K tx r m X ⊢ objOwn X.v n (DFrac.own 1) true (.node bl rn) ∗
      objOwn X.v bl (DFrac.own 1) (decide (bl ∈ X.liveB)) (.bkt B) ∗ sortQ X n ∗
      (∀ r', ⌜r'.nv.parent' ≠ n⌝ -∗ objOwn X.v n (DFrac.own 1) true (.node bl r') -∗
        objOwn X.v bl (DFrac.own 1) (decide (bl ∈ X.liveB)) (.bkt B) -∗ sortQ X n -∗
        wtxW K tx r m (X.setNode bl n r')) := by
  iintro Hw
  icases wtxW_cells_acc K tx r m X $$ Hw with ⟨%Hbase, Hv, Hcl⟩
  ihave Hw := Hcl $$ Hv
  icases wtxW_open K tx r m X $$ Hw with ⟨#Hpk, #Hcore, #Hreg, Hh, Hv, Hst, Hclose⟩
  ihave %Hok := wtxHeap_heapOK tx (DFrac.own 1) X $$ Hh
  icases wtxHeap_sort_acc tx X bl B n rn hb hr $$ Hh with ⟨Hno, Hbo, Hm, Hback⟩
  rw [decide_eq_true hlive]
  iframe Hno Hbo
  unfold sortQ
  iframe Hm Hv
  isplitr
  · ipureintro; exact ⟨Hok.2.1, Hbase⟩
  iintro %r' %Hpar Hno Hbo ⟨-, Hm, Hv⟩
  ihave Hh := Hback $$ %r' %Hpar Hno Hbo Hm
  iapply Hclose $$ %(X.setNode bl n r') [] Hh Hv Hst
  ipureintro
  refine ⟨WX.v_setNode X bl n r', WX.setNode_handles X bl n r', ?_⟩
  rw [WX.setNode_nloc]
  unfold WX.setNode; split <;> rfl

omit hos in
/-- A child `c ≠ n`'s live object, out of `objsBut` and back. -/
theorem objsBut_kid_acc (X : WX) (n c bl : Loc) (rc : NRec)
    (ho : X.t.objs !! c = some (.node bl rc)) (hne : c ≠ n) (hl : c ∈ X.live) :
    objsBut (GF := GF) X n ⊢ objOwn X.v c (DFrac.own 1) true (.node bl rc) ∗
      (objOwn X.v c (DFrac.own 1) true (.node bl rc) -∗ objsBut X n) := by
  unfold objsBut
  have ho' : (X.t.objs.delete n) !! c = some (.node bl rc) := by
    rw [GMap.lookup_delete_ne _ (Ne.symm hne)]; exact ho
  iintro Hm
  icases (BigSepM.bigSepM_lookup_acc ho').1 $$ Hm with ⟨Ho, Hback⟩
  rw [decide_eq_true hl]
  iframe Ho
  iintro Ho
  iapply Hback
  iexact Ho

omit [GooseSemantics] [GooseInterp] go_gctx hos sem in
/-- The record of a child the sort reads, among the heap's objects. -/
theorem sortKid_obj {X : WX} {bl n c : Loc} (hd : objsDisj X.t) (hk : sortKid X bl n c) :
    ∃ B rc, X.t.bs !! bl = some B ∧ B.ns !! c = some rc ∧ X.t.objs !! c = some (.node bl rc) ∧
      0 < rc.ws.length := by
  obtain ⟨-, -, rc, hrc, hws⟩ := hk
  obtain ⟨B, hB, hns⟩ := node_bs_of hrc
  exact ⟨B, rc, hB, hns, objs_node X.t bl B c rc hd hB hns, hws⟩

/-- **A child's first key's source** (persistent, not stale), read in `objsBut`. -/
theorem objsBut_kid_src (X : WX) (bl n c : Loc) (hd : objsDisj X.t) (hF : liveFresh X)
    (hk : sortKid X bl n c) :
    objsBut (GF := GF) X n ⊢ objsBut X n ∗
      ∃ src : Src, ⌜src ≠ Src.stale⌝ ∗ srcOwn X.v (kidKs X c) src (kidFk X c) := by
  obtain ⟨B, rc, hB, hns, ho, hws⟩ := sortKid_obj hd hk
  have hne := hk.1
  have hl := hk.2.1
  obtain ⟨w, hw⟩ : ∃ w, rc.ws[0]? = some w := ⟨_, List.getElem?_eq_getElem hws⟩
  have hfr := (hF bl B c rc hB hns hl).1 w (List.mem_of_getElem? hw)
  iintro Hm
  icases objsBut_kid_acc (GF := GF) X n c bl rc ho hne hl $$ Hm with ⟨Ho, Hmb⟩
  icases (objOwn_live_node (GF := GF) X.v c (DFrac.own 1) bl rc).1 $$ Ho with ⟨Hc, Hins, Hcap, Hws, Hch, Hchcap, Hkey⟩
  ihave %Hlen := BigSepL2.bigSepL2_length $$ Hws
  obtain ⟨it, hit⟩ : ∃ it, rc.ins[0]? = some it :=
    ⟨_, List.getElem?_eq_getElem (by rw [Hlen]; exact hws)⟩
  icases BigSepL2.bigSepL2_lookup_acc hit hw $$ Hws with ⟨Hw0, Hwsb⟩
  icases (Write.wOwn_live (GF := GF) _ _ _).1 $$ Hw0 with ⟨%Hfp, #Hk0, #Hv0⟩
  ihave Hws := Hwsb $$ [Hk0 Hv0]
  · iapply (Write.wOwn_live (GF := GF) _ _ _).2; iframe; iframe #; ipureintro; exact Hfp
  ihave Ho := (objOwn_live_node (GF := GF) X.v c (DFrac.own 1) bl rc).2 $$ [Hc Hins Hcap Hws Hch Hchcap Hkey]
  · iframe
  ihave Hm := Hmb $$ Ho
  iframe Hm
  iexists w.ks
  rw [kidKs_eq ho hit, kidFk_eq ho hw]
  isplitr
  · ipureintro; exact hfr.1
  iexact Hk0

/-- **The sort's frame gives a child's struct and inodes** (`nodeHdAcc`). -/
theorem sortQ_hd (X : WX) (bl n c : Loc) (hk : sortKid X bl n c) :
    sortQ (GF := GF) X n ⊢ nodeHdAcc (sortQ X n) (kidKs X) c := by
  unfold sortQ nodeHdAcc
  iintro ⟨%Hp, Hm, Hv⟩
  obtain ⟨B, rc, hB, hns, ho, hws⟩ := sortKid_obj Hp.1 hk
  icases objsBut_kid_acc (GF := GF) X n c bl rc ho hk.1 hk.2.1 $$ Hm with ⟨Ho, Hmb⟩
  icases (objOwn_live_node (GF := GF) X.v c (DFrac.own 1) bl rc).1 $$ Ho with ⟨Hc, Hins, Hcap, Hws, Hch, Hchcap, Hkey⟩
  ihave %Hlen := BigSepL2.bigSepL2_length $$ Hws
  obtain ⟨it, hit⟩ : ∃ it, rc.ins[0]? = some it :=
    ⟨_, List.getElem?_eq_getElem (by rw [Hlen]; exact hws)⟩
  iexists DFrac.own 1, rc.nv, rc.ins, it
  isplitr
  · ipureintro; exact ⟨hit, (kidKs_eq ho hit).symm⟩
  iframe Hc Hins
  iintro ⟨Hc, Hins⟩
  iframe Hv
  isplitr
  · ipureintro; exact Hp
  iapply Hmb
  iapply (objOwn_live_node (GF := GF) X.v c (DFrac.own 1) bl rc).2
  iframe

/-- **The sort's frame gives two children's first keys' bytes** (`keyPairAcc`). -/
theorem sortQ_keys (X : WX) (bl n c d : Loc) (hF : liveFresh X) (hc : sortKid X bl n c)
    (hd : sortKid X bl n d) :
    sortQ (GF := GF) X n ⊢ keyPairAcc (sortQ X n) (kidKs X) (kidFk X) c d := by
  unfold sortQ keyPairAcc
  iintro ⟨%Hp, Hm, Hv⟩
  icases objsBut_kid_src (GF := GF) X bl n c Hp.1 hF hc $$ Hm with ⟨Hm, %sc, %Hsc, #Hkc⟩
  icases objsBut_kid_src (GF := GF) X bl n d Hp.1 hF hd $$ Hm with ⟨Hm, %sd, %Hsd, #Hkd⟩
  icases (viewCells_halves wq X.v).1 $$ Hv with ⟨Hv1, Hv2⟩
  icases srcOwn_acc wq.half X.v (kidKs X c) sc (kidFk X c) Hsc Hp.2 $$ [Hv1] with ⟨%dq1, Hk1, Hb1⟩
  · iframe Hv1; iexact Hkc
  icases srcOwn_acc wq.half X.v (kidKs X d) sd (kidFk X d) Hsd Hp.2 $$ [Hv2] with ⟨%dq2, Hk2, Hb2⟩
  · iframe Hv2; iexact Hkd
  iexists dq1, dq2
  iframe Hk1 Hk2
  iintro ⟨Hk1, Hk2⟩
  icases Hb1 $$ Hk1 with ⟨-, Hv1⟩
  icases Hb2 $$ Hk2 with ⟨-, Hv2⟩
  iframe Hm
  isplitr
  · ipureintro; exact Hp
  iapply (viewCells_halves wq X.v).2
  iframe

end heap

section sort
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **`sort.Sort(n.children)`** (see the module doc): the children slice `s` holds a
permutation of `cs` after, the frame unchanged. -/
theorem nodes_sort_wp (hS : sort.«Sort».spec (GF := GF) (hG := hG))
    (hK : internal.common.Inode.Key.spec (GF := GF) (hG := hG))
    (hC : bytes.Compare.spec (GF := GF) (hG := hG))
    (X : WX) (bl n : Loc) (cs : List Loc) (s : GoSlice) (hkids : ∀ c ∈ cs, sortKid X bl n c)
    (hF : liveFresh X) (hlen : cs.length ≤ 2 ^ 62) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ s ↦* cs ∗ sortQ (GF := GF) X n }}
      (App (Val (@! _root_.Perennial.sort.«Sort»))
        (Val #(GoInterface.ok (interface.mk nodes.ty #s))))
    {{ RET #(); ∃ l, s ↦* l ∗ sortQ X n ∗ ⌜cs.Perm l⌝ }} := by
  iintro %Φ ⟨#Hpkg, Hs, HQ⟩ HΦ
  ihave #Hsrt := nodes_sorter hK hC s (sortKid X bl n) (sortQ X n) (kidKs X) (kidFk X)
    (fun c hc => sortQ_hd X bl n c hc) (fun c d hc hd => sortQ_keys X bl n c d hF hc hd) $$ Hpkg
  ihave #Hspkg : isPkgInit (PROP := IProp GF) pkg_id.sort $$ []
  · iPkgInit
  wp_apply (hS Loc (interface.mk nodes.ty #s) (nodesR s (sortKid X bl n) (sortQ X n))
      (fun a b => decide (go.GoStringLt (kidFk X a) (kidFk X b))) cs (swo_kidFk X))
    $$ [Hs HQ] as %l' ⟨HR, %Hl'⟩
  · iframe #
    unfold nodesR
    iframe
    ipureintro; exact ⟨hkids, hlen⟩
  unfold nodesR
  icases HR with ⟨Hs, -, HQ⟩
  iapply HΦ
  iexists l'
  iframe
  ipureintro; exact Hl'.1

end sort

end Spill

end bbolt
end EtcdGrove
end Perennial
