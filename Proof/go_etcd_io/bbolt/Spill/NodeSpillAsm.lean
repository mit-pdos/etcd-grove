/-
`node.spill`'s assembly (U9m, `notes/bbolt-proof-plan.md`): the facts `node__spill.lean` needs
to chain the sort (`Spill/NodeSpillSort`), the children's loop (`Spill/NodeSpillLoopWp`) and the
rest (`Spill/NodeSpillPieces`): an unspilled tree's root is an unspilled node (`uTree_uNode`),
its children are what the sort reads (`uTree_sortKids`), the spill's pre at the permuted state
(`spPre_perm`), the loop's end as `spEnd` (`spEnd_of_loop`), and the post back from the
permuted state (`spPost_unperm`).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.NodeSpillPerm
public import Proof.go_etcd_io.bbolt.Spill.NodeSpillSort
public import Proof.go_etcd_io.bbolt.Spill.NodeSpillPiecesDefs
public import Proof.go_etcd_io.bbolt.Spill.NodeSpec
public import Proof.go_etcd_io.bbolt.Rebalance.NodeRblBase

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section pure
variable [GooseExts]

/-- The root of an unspilled tree is an unspilled node. -/
theorem uTree_uNode {X : WX} {bl : Loc} {P : Pages} {hwm : Nat} {n : Loc} {lo hi h F D N E}
    (hu : uTree X bl P hwm n lo hi h F D N E) {r : NRec} (hn : X.node bl n = some r) :
    uNode X bl n r lo hi := by
  cases hu with
  | leaf _ r' _ _ _ hr hun => rw [hn] at hr; cases hr; exact hun
  | branch _ r' _ _ _ _ hr hun => rw [hn] at hr; cases hr; exact hun

/-- **The children of an unspilled tree's root are what the sort reads** (not the root, live,
with entries). -/
theorem uTree_sortKids {X : WX} {bl : Loc} {P : Pages} {hwm : Nat} {n : Loc} {lo hi h F D N E}
    (hu : uTree X bl P hwm n lo hi h F D N E) {rn : NRec} (hn : X.node bl n = some rn)
    (hpar : rn.nv.parent' ≠ n) : ∀ c ∈ rn.cs, sortKid X bl n c := by
  intro c hc
  cases hu with
  | leaf _ r _ _ _ hr _ _ hcs => rw [hn] at hr; cases hr; rw [hcs] at hc; cases hc
  | branch _ r _ _ h' es hr hun hleaf h2 hlen hent hchnd hcs hcsnd hNnd hpg0 =>
    rw [hn] at hr; cases hr
    rcases hcs c hc with ⟨e, he, hec⟩ | ⟨hlv, rc, hrc, -, hsp, -, hne⟩
    · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 he
      have hjl : j < rn.ws.length := by rw [← hlen]; exact (List.getElem?_eq_some_iff.1 hj).1
      have hent' := hent j _ e (List.getElem?_eq_getElem hjl) hj
      cases hent' with
      | child _ _ _ _ _ _ _ _ c' rc F' D' N' E' _ hrc hp _ _ _ hne hut =>
        simp only [Option.some.injEq] at hec
        subst hec
        refine ⟨?_, (uTree_uNode hut hrc).1, rc, hrc, hne.1⟩
        intro e; subst e; rw [hn] at hrc; cases hrc; exact hpar hp
      | fin => simp at hec
    · refine ⟨?_, hlv, rc, hrc, hne⟩
      intro e; subst e; rw [hn] at hrc; cases hrc; rw [hun.2.2.1] at hsp; cases hsp

variable {X : WX} {bl n : Loc} {B : BRec} {rn : NRec} {l : List Loc}

/-- **The spill's pre at the permuted state** (an unspilled tree's root, its children permuted). -/
theorem spPre_perm (hd : objsDisj X.t) (hB : X.t.bs !! bl = some B) (hr : B.ns !! n = some rn)
    (hp : rn.cs.Perm l) {w : WDb} {O : List Nat} {lo hi : Option (List w8)} {h : Nat}
    {F D : List Nat} {N : List Loc} {E : List El} {cs : SpCase}
    (hu : uTree X bl (spP X) X.t.mv.pgid'.toNat n lo hi h F D N E)
    (hctx : spCtx X bl n rn lo hi N cs) (hG : spG X w.wtxid (mapLen w.ms) w.fl)
    (hsl : slotInv w.fl X.t.mv.pgid'.toNat (O ++ D)) (hfr : spFree X w.fl w.wtxid F)
    (hvc : X.v = View.ofC X.v.base w.C) (hfc : ∀ y ∈ w.fl.free, ¬ coversSlot w.C.pages y.toNat)
    (hts : ∀ s ∈ treeSlots w.C, s < X.t.mv.pgid'.toNat) (hpar : parOK X bl) :
    spPre (X.setNode bl n { rn with cs := l }) w bl n { rn with cs := l } O lo hi h F D N E cs := by
  have hrn : X.node bl n = some rn := by unfold WX.node; rw [hB]; exact hr
  have hmv : (X.setNode bl n { rn with cs := l }).t.mv = X.t.mv := by rw [setNode_perm_eq hB]
  have hv : (X.setNode bl n { rn with cs := l }).v = X.v := by rw [setNode_perm_eq hB]
  have hnN : n ∈ N := uTree_head hu
  refine ⟨node_perm_self hB, spG_perm hB hr hp hG, Or.inr ⟨?_, spCtx_perm hB hr hp hnN hctx,
    by rw [hmv]; exact hsl, by rw [setNode_perm_eq hB]; exact hfr, by rw [hv]; exact hvc, hfc,
    by rw [hmv]; exact hts, parOK_perm hpar hrn hp⟩⟩
  rw [hmv, spP_perm hB]
  by_cases hleaf : rn.nv.isLeaf' = false
  · obtain ⟨h', es, rfl, rfl, rfl, rfl, rfl, hb⟩ := uBr_of_uTree hu hrn hleaf
    have hb' := uBr_perm hd hB hr hp hb
    have H := uTree_of_uBr hb'
    rw [hv, spP_perm hB] at H
    exact H
  · have hcs : rn.cs = [] := by
      cases hu with
      | leaf _ r _ _ _ hr' _ _ hcs => rw [hrn] at hr'; cases hr'; exact hcs
      | branch _ r _ _ _ _ hr' _ hl' => rw [hrn] at hr'; cases hr'; exact absurd hl' hleaf
    rw [setNode_perm_nil hB hr hcs hp]
    exact hu

end pure

/-- A nodup list of naturals below `n` has at most `n` elements. -/
theorem nodup_bounded_len (l : List Nat) (n : Nat) (hnd : l.Nodup) (hb : ∀ x ∈ l, x < n) :
    l.length ≤ n := by
  have h : l.Subperm (List.range n) := List.subperm_of_subset hnd (fun x hx => List.mem_range.2 (hb x hx))
  simpa using h.length_le

section iprop
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

variable {X : WX} {bl n : Loc} {B : BRec} {rn : NRec} {l : List Loc}

omit package_sem in
/-- **A bucket's `tx` field out of its object** (own at the root bucket, persistent otherwise). -/
theorem objOwn_bkt_tx_acc (v : View) (bl : Loc) (b : Bool) (B : BRec) :
    objOwn (GF := GF) v bl (DFrac.own 1) b (.bkt B) ⊢ ∃ dqb : DFrac,
      bl.[Bucket, go!"tx"] ↦{dqb} B.bv.tx' ∗
      (bl.[Bucket, go!"tx"] ↦{dqb} B.bv.tx' -∗ objOwn v bl (DFrac.own 1) b (.bkt B)) := by
  iintro H
  icases (objOwn_bkt_unf v bl (DFrac.own 1) b B).1 $$ H
    with ⟨H1, Htx, H3, H4, H5, H6, H7, H8, H9, H10⟩
  by_cases hroot : bl = B.bv.tx'.[Tx, go!"root"]
  · rw [if_pos hroot]
    iexists DFrac.own 1
    iframe Htx
    iintro Htx
    iapply (objOwn_bkt_unf v bl (DFrac.own 1) b B).2
    rw [if_pos hroot]
    iframe
  · rw [if_neg hroot]
    icases Htx with #Htx
    iexists DFrac.discard
    isplitr
    · iexact Htx
    · iintro _
      iapply (objOwn_bkt_unf v bl (DFrac.own 1) b B).2
      rw [if_neg hroot]
      iframe

omit package_sem in
theorem loc_elem_bounds (p a : Loc) :
    (p ↦ a : IProp GF) ⊢ ⌜0 < p.addr ∧ p.addr < maxAddr⌝ := by
  rw [typedPointsto_unseal]; unfold typedPointstoWrap
  rw [show @TypedPointsto.typedPointstoDef GF Loc _ p a (DFrac.own 1) =
    heapPointsto p (DFrac.own 1) #a from rfl]
  iintro ⟨H, -⟩
  icases heapPointsto_pos p _ _ $$ H with %H1
  icases heapPointsto_lt_maxAddr p _ _ $$ H with %H2
  ipureintro; exact ⟨H1, H2⟩

omit package_sem in
/-- Full points-tos of `Loc`s at the addresses `g i`: the addresses are distinct and bounded. -/
theorem loc_elems_addrs (vs : List Loc) (g : Nat → Loc) :
    ([∗list] i ↦ v ∈ vs, (g i ↦ v : IProp GF)) ⊢
      ⌜((List.range vs.length).map g).Nodup ∧
        ∀ i < vs.length, 0 < (g i).addr ∧ (g i).addr < maxAddr⌝ := by
  induction vs generalizing g with
  | nil => iintro _; ipureintro; simp
  | cons v vs ih =>
    have hne : ∀ j (hj : j < vs.length), (g 0 ↦ v : IProp GF) ∗
        ([∗list] i ↦ v ∈ vs, (g (i + 1) ↦ v : IProp GF)) ⊢ ⌜g 0 ≠ g (j + 1)⌝ := by
      intro j hj
      iintro ⟨H0, Ht⟩
      icases (BigSepL.bigSepL_lookup_acc (Φ := fun i v => (g (i + 1) ↦ v : IProp GF))
        (List.getElem?_eq_getElem hj)).1 $$ Ht with ⟨Hj, -⟩
      by_cases he : g 0 = g (j + 1)
      · rw [he]
        iexfalso
        rw [typedPointsto_unseal]; unfold typedPointstoWrap
        icases Hj with ⟨Hj, -⟩
        icases H0 with ⟨H0, -⟩
        rw [show @TypedPointsto.typedPointstoDef GF Loc _ (g (j + 1)) v (DFrac.own 1) =
          heapPointsto (g (j + 1)) (DFrac.own 1) #v from rfl]
        rw [show @TypedPointsto.typedPointstoDef GF Loc _ (g (j + 1)) vs[j] (DFrac.own 1) =
          heapPointsto (g (j + 1)) (DFrac.own 1) #vs[j] from rfl]
        icombine H0 Hj gives %He
        exact absurd He.1 (dfrac_own_one_op_invalid _)
      · ipureintro; exact he
    have hall : (g 0 ↦ v : IProp GF) ∗ ([∗list] i ↦ v ∈ vs, (g (i + 1) ↦ v : IProp GF)) ⊢
        ⌜∀ j : Fin vs.length, g 0 ≠ g (j.1 + 1)⌝ :=
      (forall_intro fun (j : Fin vs.length) => hne j.1 j.2).trans pure_forall.2
    have hb := (and_intro hall (and_intro (sep_elim_left.trans (loc_elem_bounds _ _))
      (sep_elim_right.trans (ih (fun i => g (i + 1)))))).trans
      ((and_mono_right pure_and.1).trans pure_and.1)
    refine BigSepL.bigSepL_cons.1.trans (hb.trans (pure_mono ?_))
    rintro ⟨hn, h0, hnd, hbs⟩
    refine ⟨?_, ?_⟩
    · rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
      refine List.nodup_cons.2 ⟨?_, ?_⟩
      · simp only [List.mem_map, List.mem_range, Function.comp]
        rintro ⟨j, hj, he⟩
        exact hn ⟨j, hj⟩ he.symm
      · exact hnd
    · intro i hi
      cases i with
      | zero => exact h0
      | succ i => exact hbs i (by simpa using hi)
omit package_sem in
/-- **A full slice of pointers has at most `2 ^ 62` elements** (`sort.Sort`'s bound): its
elements are full points-tos (`loc_elems_addrs`), at distinct addresses in `(0, maxAddr)`. (At a
fraction the bound does not follow: `arrayIndexRef` of a non-plain type is abstract, and every
element could be at one address.) -/
theorem ownSlice_loc_len (s : GoSlice) (cs : List Loc) :
    (s ↦* cs : IProp GF) ⊢ s ↦* cs ∗ ⌜cs.length ≤ 2 ^ 62⌝ := by
  iintro H
  ihave %Hl : ⌜cs.length ≤ 2 ^ 62⌝ $$ [H]
  · rw [ownSlice_unseal]; unfold ownSliceDef
    icases H with (%Hn | ⟨H, -⟩)
    · ipureintro; rw [Hn.2]; simp
    icases typedPointsto_split _ _ _ $$ H with H
    simp only [TypedPointsto.typedPointstoDef]
    icases H with ⟨-, He⟩
    icases loc_elems_addrs cs (fun i => arrayIndexRef Loc (i : Int) s.ptr) $$ He with %Ha
    ipureintro
    obtain ⟨hnd, hb⟩ := Ha
    have h := nodup_bounded_len ((List.range cs.length).map
      (fun i : Nat => (arrayIndexRef Loc (i : Int) s.ptr).addr.toNat)) (maxAddr.toNat) ?_ ?_
    · simp only [List.length_map, List.length_range, maxAddr] at h; omega
    · unfold List.Nodup at hnd ⊢
      rw [List.pairwise_map] at hnd ⊢
      refine List.Pairwise.imp_of_mem ?_ hnd
      intro i j hi hj hne he
      rw [List.mem_range] at hi hj
      have h1 := (hb i hi).1; have h2 := (hb j hj).1
      apply hne
      cases ex : arrayIndexRef Loc (i : Int) s.ptr
      cases ey : arrayIndexRef Loc (j : Int) s.ptr
      rw [ex, ey] at he; rw [ex] at h1; rw [ey] at h2
      simp only at he h1 h2
      congr 1; omega
    · intro x hx
      simp only [List.mem_map, List.mem_range] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      have := hb i hi; simp only [maxAddr] at this ⊢; omega
  iframe
  ipureintro; exact Hl

/-- **`n`'s spill's post, from the permuted state back to the start.** -/
theorem spPost_unperm (hd : objsDisj X.t) (hB : X.t.bs !! bl = some B) (hr : B.ns !! n = some rn)
    (hp : rn.cs.Perm l) {w : WDb} (hG : spG X w.wtxid (mapLen w.ms) w.fl)
    (K : BC) (tx : Loc) (r : TxReg) (m : Bool)
    {O : List Nat} {lo hi : Option (List w8)} {h : Nat} {D : List Nat} {N : List Loc}
    {E : List El} {cs : SpCase} (hn : n ∈ N) (hsp0 : rn.nv.spilled' = false) (hnc : n ∉ rn.cs)
    (err : GoInterface) :
    spPost (GF := GF) K tx r m (X.setNode bl n { rn with cs := l }) w bl n { rn with cs := l } O
      lo hi h D N E cs err ⊢ spPost K tx r m X w bl n rn O lo hi h D N E cs err := by
  have hv : (X.setNode bl n { rn with cs := l }).v = X.v := by rw [setNode_perm_eq hB]
  unfold spPost
  iintro (⟨%He, %X', %w', %st, Hw, Hdb, %Hd⟩ | ⟨%He, #Hok, %X', %w', %st, %Hf, Hr⟩)
  · ileft
    isplitr
    · ipureintro; exact He
    iexists X', w', st
    iframe
    ipureintro
    exact spDone_unperm hd hB hr hp hG hn hsp0 hnc Hd
  · iright
    isplitr
    · ipureintro; exact He
    isplitr
    · iexact Hok
    iexists X', w', st
    iframe
    ipureintro
    exact spErr_st (spErr_trans (spErr_setNode X w bl n _) Hf) (List.nil_append _)

end iprop

end Spill

end bbolt
end EtcdGrove
end Perennial
