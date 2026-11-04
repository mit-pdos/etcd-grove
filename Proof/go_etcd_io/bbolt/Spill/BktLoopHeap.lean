/-
`Bucket.spill`'s root loop (U9q, `notes/bbolt-proof-plan.md`): **the heap accessors** the loop body
uses: a child bucket's object with the transaction's `db` field and the page size
(`b.inlineable()` without a root node), and with its root node's object and the view's cells too
(`b.inlineable()`, `b.write()`).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.NodeSpillPiecesOne
public import Proof.go_etcd_io.bbolt.Spill.DerefCopy
public import Proof.go_etcd_io.bbolt.Inv.MatReady

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **A bucket's object and a live node's object (of any bucket), out of the heap**, and back
unchanged. -/
theorem wtxHeap_bkt_node_acc (tx : Loc) (dq : DFrac) (X : WX) (bl : Loc) (B : BRec) (c n : Loc)
    (C : BRec) (rn : NRec) (hb : X.t.bs !! bl = some B) (hc : X.t.bs !! c = some C)
    (hn : C.ns !! n = some rn) (hl : n ∈ X.live) :
    wtxHeap (GF := GF) tx dq X ⊢ objOwn X.v bl dq (decide (bl ∈ X.liveB)) (.bkt B) ∗
      objOwn X.v n dq true (.node c rn) ∗
      (objOwn X.v bl dq (decide (bl ∈ X.liveB)) (.bkt B) -∗ objOwn X.v n dq true (.node c rn) -∗
        wtxHeap tx dq X) := by
  iintro H
  ihave %Ho := wtxHeap_objs_node tx dq X c C n rn hc hn $$ H
  unfold wtxHeap
  icases H with ⟨%Hrl, Hf, Hrf, Hm, Hbk⟩
  icases (BigSepM.bigSepM_lookup_acc (bobjs_bkt X.t bl B hb)).1 $$ Hbk with ⟨Hbo, Hbback⟩
  icases (BigSepM.bigSepM_lookup_acc Ho).1 $$ Hm with ⟨Hno, Hnback⟩
  rw [decide_eq_true hl]
  iframe Hbo Hno
  iintro Hbo Hno
  iframe
  isplitr
  · ipureintro; exact Hrl
  isplitl [Hnback Hno]
  · iapply Hnback; iexact Hno
  iapply Hbback; iexact Hbo

/-- **A live node's inodes' slices have its entries' lengths** (the sources not stale), so they
are bounded by its entries' bound. -/
theorem wOwns_lens (v : View) :
    ∀ (ins : List Inode) (ws : List WEntry), wsLive ws →
    (∀ w ∈ ws, w.key.length + w.value.length ≤ bboltEntryMax) →
    ([∗list] it;w ∈ ins;ws, wOwn (GF := GF) v true it w) ⊢
      ⌜∀ it ∈ ins, it.key'.len.toNat + it.value'.len.toNat < 2 ^ 62⌝
  | [], [], _, _ => by
    iintro -; ipureintro; intro it hit; cases hit
  | [], _ :: _, _, _ => by
    iintro H
    icases BigSepL2.bigSepL2_nil_inv_left $$ H with %H
    cases H
  | _ :: _, [], _, _ => by
    iintro H
    icases BigSepL2.bigSepL2_nil_inv_right $$ H with %H
    cases H
  | it :: ins, w :: ws, hl, hb => by
    have hw := hl w List.mem_cons_self
    have hbw := hb w List.mem_cons_self
    have IH := wOwns_lens v ins ws (fun x hx => hl x (List.mem_cons_of_mem _ hx))
      (fun x hx => hb x (List.mem_cons_of_mem _ hx))
    iintro H
    icases BigSepL2.bigSepL2_cons.1 $$ H with ⟨Hw, H⟩
    icases (wOwn_true' v it w).1 $$ Hw with ⟨-, #Hks, #Hvs⟩
    ihave %Hk := srcOwn_len v it.key' w.ks w.key hw.1 $$ Hks
    ihave %Hv := srcOwn_len v it.value' w.vs w.value hw.2 $$ Hvs
    ihave %Hr := IH $$ H
    ipureintro
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · have h1 : x.key'.len.toNat = w.key.length := by
        rw [Hk.1, show sint.nat x.key'.len = (sint.Z x.key'.len).toNat from rfl]
        have := Hk.2; unfold sint.Z at this ⊢; rw [BitVec.toInt_eq_toNat_cond] at this ⊢
        split <;> omega
      have h2 : x.value'.len.toNat = w.value.length := by
        rw [Hv.1, show sint.nat x.value'.len = (sint.Z x.value'.len).toNat from rfl]
        have := Hv.2; unfold sint.Z at this ⊢; rw [BitVec.toInt_eq_toNat_cond] at this ⊢
        split <;> omega
      unfold bboltEntryMax at hbw
      omega
    · exact Hr x hx

variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **A live bucket's object, the transaction's `db` field and the page size, out of `wtxW`**, and
back. -/
theorem wtxW_bkt_db_acc (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (c : Loc) (C : BRec)
    (hc : X.t.bs !! c = some C) (hcl : c ∈ X.liveB) :
    wtxW (GF := GF) K tx r m X ⊢ objOwn X.v c (DFrac.own 1) true (.bkt C) ∗
      tx.[Tx, go!"db"] ↦{DFrac.own (txDbQ 1)} K.db ∗ K.db.[DB, go!"pageSize"] ↦□ W64 4096 ∗
      (objOwn X.v c (DFrac.own 1) true (.bkt C) -∗
        tx.[Tx, go!"db"] ↦{DFrac.own (txDbQ 1)} K.db -∗ wtxW K tx r m X) := by
  iintro Hw
  icases (wtxW_split K tx r m X).1 $$ Hw with ⟨Hc, Hcells, Hmap⟩
  unfold wtxCore
  icases Hc with ⟨#Hpkg', #Hcore, %Hr, #Hreg, Hh, Hfills, Hbk, Hnl, Hdbf, Hview, Hst⟩
  ihave #Hps := isBoltCoreP_pageSize K.B K.N K.db K.p K.sp K.t0 $$ [Hcore]
  · unfold BC.core; iexact Hcore
  icases wtxHeap_bkt_obj_acc tx (DFrac.own 1) X c C (bobjs_bkt X.t c C hc) $$ Hh with ⟨Ho, Hback⟩
  rw [decide_eq_true hcl, Hr.1]
  iframe Ho Hdbf Hps
  iintro Ho Hdbf
  ihave Hh := Hback $$ Ho
  iapply (wtxW_split K tx r m X).2
  unfold wtxCore
  rw [← Hr.1]
  iframe; iframe #
  ipureintro; exact ⟨rfl, Hr.2⟩

/-- **A live bucket's object, a live node of it, the view's cells, the transaction's `db` field
and the page size, out of `wtxW`**, and back. -/
theorem wtxW_bkt_root_acc (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (c : Loc) (C : BRec)
    (n : Loc) (rn : NRec) (hc : X.t.bs !! c = some C) (hcl : c ∈ X.liveB) (hn : C.ns !! n = some rn)
    (hl : n ∈ X.live) :
    wtxW (GF := GF) K tx r m X ⊢ ⌜0 < X.v.base.addr⌝ ∗ objOwn X.v c (DFrac.own 1) true (.bkt C) ∗
      objOwn X.v n (DFrac.own 1) true (.node c rn) ∗ viewCells wq X.v ∗
      tx.[Tx, go!"db"] ↦{DFrac.own (txDbQ 1)} K.db ∗ K.db.[DB, go!"pageSize"] ↦□ W64 4096 ∗
      (objOwn X.v c (DFrac.own 1) true (.bkt C) -∗ objOwn X.v n (DFrac.own 1) true (.node c rn) -∗
        viewCells wq X.v -∗ tx.[Tx, go!"db"] ↦{DFrac.own (txDbQ 1)} K.db -∗ wtxW K tx r m X) := by
  iintro Hw
  icases (wtxW_split K tx r m X).1 $$ Hw with ⟨Hc, Hcells, ⟨%l, Hmf, %Hl⟩⟩
  ihave %Hnn := mapFields_base_nonnull _ _ _ _ $$ Hmf
  unfold wtxCore
  icases Hc with ⟨#Hpkg', #Hcore, %Hr, #Hreg, Hh, Hfills, Hbk, Hnl, Hdbf, Hview, Hst⟩
  ihave #Hps := isBoltCoreP_pageSize K.B K.N K.db K.p K.sp K.t0 $$ [Hcore]
  · unfold BC.core; iexact Hcore
  icases wtxHeap_bkt_node_acc tx (DFrac.own 1) X c C c n C rn hc hc hn hl $$ Hh
    with ⟨Ho, Hno, Hback⟩
  rw [decide_eq_true hcl, Hr.1]
  iframe Ho Hno Hdbf Hps Hcells
  isplitr
  · ipureintro; exact Hnn
  iintro Ho Hno Hcells Hdbf
  rw [← decide_eq_true (p := c ∈ X.liveB) hcl]
  ihave Hh := Hback $$ Ho Hno
  iapply (wtxW_split K tx r m X).2
  unfold wtxCore
  rw [← Hr.1]
  iframe; iframe #
  isplitr
  · ipureintro; exact ⟨rfl, Hr.2⟩
  ipureintro; exact Hl

/-- **What `b.inlineable()` reads of a child bucket**, out of `wtxW` and back: its `tx` field
(persistent: not the root bucket), its `rootNode` field, its root node's struct and inodes (if
any), the transaction's `db` field, the page size, and the inodes' lengths bound. -/
theorem wtxW_inl_acc (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (c : Loc) (C : BRec)
    (nv : node) (ins : List Inode) (hc : X.t.bs !! c = some C) (hcl : c ∈ X.liveB)
    (hcr : c ≠ C.bv.tx'.[Tx, go!"root"]) (hnull : C.bv.rootNode' = null → ins = [])
    (hrn : C.bv.rootNode' ≠ null → ∃ rn, C.ns !! C.bv.rootNode' = some rn ∧ rn.nv = nv ∧
      rn.ins = ins ∧ C.bv.rootNode' ∈ X.live ∧ wsLive rn.ws ∧
      ∀ w ∈ rn.ws, w.key.length + w.value.length ≤ bboltEntryMax) :
    wtxW (GF := GF) K tx r m X ⊢ c.[Bucket, go!"tx"] ↦□ C.bv.tx' ∗
      c.[Bucket, go!"rootNode"] ↦ C.bv.rootNode' ∗
      (if C.bv.rootNode' = null then emp else C.bv.rootNode' ↦ nv ∗ nv.inodes' ↦* ins) ∗
      tx.[Tx, go!"db"] ↦{DFrac.own (txDbQ 1)} K.db ∗ K.db.[DB, go!"pageSize"] ↦□ W64 4096 ∗
      ⌜∀ it ∈ ins, it.key'.len.toNat + it.value'.len.toNat < 2 ^ 62⌝ ∗
      (c.[Bucket, go!"rootNode"] ↦ C.bv.rootNode' -∗
        (if C.bv.rootNode' = null then emp else C.bv.rootNode' ↦ nv ∗ nv.inodes' ↦* ins) -∗
        tx.[Tx, go!"db"] ↦{DFrac.own (txDbQ 1)} K.db -∗ wtxW K tx r m X) := by
  iintro Hw
  by_cases hn : C.bv.rootNode' = null
  · rw [if_pos hn, hnull hn]
    icases wtxW_bkt_db_acc K tx r m X c C hc hcl $$ Hw with ⟨Ho, Hdbf, #Hps, Hback⟩
    unfold objOwn
    icases Ho with ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10⟩
    rw [if_neg hcr]
    icases H2 with #H2
    iframe H2 H5 Hdbf Hps
    isplitr
    · ipureintro; intro it hit; cases hit
    iintro H5 - Hdbf
    iapply Hback $$ [H1 H3 H4 H5 H6 H7 H8 H9 H10] Hdbf
    dsimp only
    rw [if_neg hcr]
    iframe; iframe #
  · rw [if_neg hn]
    obtain ⟨rn, hr, rfl, rfl, hl, hlive, hbd⟩ := hrn hn
    icases wtxW_bkt_root_acc K tx r m X c C C.bv.rootNode' rn hc hcl hr hl $$ Hw
      with ⟨-, Ho, Hno, Hcells, Hdbf, #Hps, Hback⟩
    unfold objOwn
    icases Ho with ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10⟩
    rw [if_neg hcr]
    icases H2 with #H2
    icases Hno with ⟨Hn, Hins, Hcap, Hws, Hch, Hchcap, Hkey⟩
    ihave %Hlens := wOwns_lens X.v rn.ins rn.ws hlive hbd $$ [Hws]
    · iexact Hws
    iframe H2 H5 Hdbf Hps Hn Hins
    isplitr
    · ipureintro; exact Hlens
    iintro H5 ⟨Hn, Hins⟩ Hdbf
    iapply Hback $$ [H1 H3 H4 H5 H6 H7 H8 H9 H10] [Hn Hins Hcap Hws Hch Hchcap Hkey] Hcells Hdbf
    · dsimp only
      rw [if_neg hcr]
      iframe; iframe #
    · dsimp only; iframe

omit hos in
/-- A pure consequence, keeping the hypothesis. -/
theorem keep_pure {Q : IProp GF} {P : Prop} (h : Q ⊢ ⌜P⌝) : Q ⊢ Q ∗ ⌜P⌝ := by
  refine (BI.and_intro h .rfl).trans ?_
  refine persistent_and_affinely_sep_left_mp.trans ?_
  iintro ⟨%HP, HQ⟩
  iframe
  ipureintro; exact HP

/-- **Every unresolved position of a path of view pages can be materialized** (`Cursor.node`'s
premise), `wtxW` kept. -/
theorem wtxW_matReady_all (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (B : BRec)
    (pids : List w64) (hroot : B.ib.root' ≠ W64 0) (hv : viewWF X.v)
    (hp : ∀ pid ∈ pids, resolve B pid = none →
      ∃ pg, X.v.pages !! pid.toNat = some pg ∧ X.t.pm !! pid = none) :
    wtxW (GF := GF) K tx r m X ⊢ wtxW K tx r m X ∗
      ⌜∀ pid ∈ pids, resolve B pid = none → matReady X B pid⌝ := by
  apply keep_pure
  refine (BI.forall_intro fun pid => ?_).trans BI.pure_forall.2
  by_cases hm : pid ∈ pids ∧ resolve B pid = none
  · obtain ⟨pg, hpg, hpm⟩ := hp pid hm.1 hm.2
    exact (wtxW_matReady K tx r m X B pid pg hroot hv hpg hpm).trans
      (BI.pure_mono fun h _ _ => h)
  · iintro -
    ipureintro
    intro h1 h2; exact absurd ⟨h1, h2⟩ hm

end heap

end Spill

end bbolt
end EtcdGrove
end Perennial
