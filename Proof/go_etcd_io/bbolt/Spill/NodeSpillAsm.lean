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
    (hsl : slotInv w.fl X.t.mv.pgid'.toNat (O ++ D)) (hfr : spFree X w.fl w.wtxid F) :
    spPre (X.setNode bl n { rn with cs := l }) w bl n { rn with cs := l } O lo hi h F D N E cs := by
  have hrn : X.node bl n = some rn := by unfold WX.node; rw [hB]; exact hr
  have hmv : (X.setNode bl n { rn with cs := l }).t.mv = X.t.mv := by rw [setNode_perm_eq hB]
  have hv : (X.setNode bl n { rn with cs := l }).v = X.v := by rw [setNode_perm_eq hB]
  have hnN : n ∈ N := uTree_head hu
  refine ⟨node_perm_self hB, spG_perm hB hr hp hG, Or.inr ⟨?_, spCtx_perm hB hr hp hnN hctx,
    by rw [hmv]; exact hsl, by rw [setNode_perm_eq hB]; exact hfr⟩⟩
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
/-- **A slice of pointers has at most `2 ^ 62` elements** (`sort.Sort`'s bound): its elements
are heap cells below `maxAddr`. Not yet (U9m): Perennial has no layout for a slice of pointers
(`go.PlainLayout` covers scalars), so the bound needs the element cells' addresses. -/
theorem ownSlice_loc_len (s : GoSlice) (cs : List Loc) (dq : DFrac) :
    (s ↦*{dq} cs : IProp GF) ⊢ s ↦*{dq} cs ∗ ⌜cs.length ≤ 2 ^ 62⌝ := by
  sorry

/-- **`n`'s spill's post, from the permuted state back to the start.** -/
theorem spPost_unperm (hd : objsDisj X.t) (hB : X.t.bs !! bl = some B) (hr : B.ns !! n = some rn)
    (hp : rn.cs.Perm l) {w : WDb} (hG : spG X w.wtxid (mapLen w.ms) w.fl)
    (K : BC) (tx : Loc) (r : TxReg) (m : Bool)
    {O : List Nat} {lo hi : Option (List w8)} {h : Nat} {D : List Nat} {N : List Loc}
    {E : List El} {cs : SpCase} (hn : n ∈ N) (hsp0 : rn.nv.spilled' = false) (err : GoInterface) :
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
    exact spDone_unperm hd hB hr hp hG hn hsp0 Hd
  · iright
    isplitr
    · ipureintro; exact He
    isplitr
    · iexact Hok
    iexists X', w', st
    iframe
    ipureintro
    exact ⟨Hf.1, Hf.2.1, by rw [Hf.2.2, hv]⟩

end iprop

end Spill

end bbolt
end EtcdGrove
end Perennial
