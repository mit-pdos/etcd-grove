/-
`node.spill` (U9e, `notes/bbolt-proof-plan.md`): the proof of its unit-internal spec
(`Spill/NodeSpec`'s `node.spill.spec'`), by Löb induction over its recursive calls (`wp_aux`: the
children's spills, the new root's). The spilled case (a piece returns at once) and the unspilled
case's assembly (U9m): the sort (`Spill/NodeSpillSort`), from the permuted state the children's
loop (`Spill/NodeSpillLoopWp`) and the rest (`Spill/NodeSpillPieces.spillTail_wp`, a `sorry`
still), back to the start (`Spill/NodeSpillAsm.spPost_unperm`). No `sorry` in this file; the
proof rests on `spillTail_wp` and `ownSlice_loc_len` (`sort.Sort`'s bound).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.NodeSpec
public import Proof.go_etcd_io.bbolt.Spill.SlotInv
public import Proof.go_etcd_io.bbolt.Spill.UTreeFrame
public import Proof.go_etcd_io.bbolt.Rebalance.Heap
public import Proof.go_etcd_io.bbolt.Spill.DerefHeap
public import Proof.go_etcd_io.bbolt.Spill.NodeSpillAsm
public import Proof.go_etcd_io.bbolt.Spill.NodeSpillLoopWp
public import Proof.go_etcd_io.bbolt.Spill.NodeSpillPieces
public import Proof.go_etcd_io.bbolt.Spill.NodeSpillPiecesOne

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

omit [GooseSemantics] [GooseInterp] go_gctx hos in
theorem node_of_bs {X : WX} {bl n : Loc} {rn : NRec} (h : X.node bl n = some rn) :
    ∃ B, X.t.bs !! bl = some B ∧ B.ns !! n = some rn := by
  unfold WX.node at h
  cases hb : X.t.bs !! bl with
  | none => rw [hb] at h; cases h
  | some B => rw [hb] at h; exact ⟨B, rfl, h⟩

/-- **`node.spill`, by Löb.** -/
theorem node.spill.wp_aux (hS : sort.«Sort».spec (GF := GF) (hG := hG))
    (hK : internal.common.Inode.Key.spec (GF := GF) (hG := hG))
    (hC : bytes.Compare.spec (GF := GF) (hG := hG))
    (hAlloc : Tx.allocate.spec (GF := GF) (hG := hG))
    (hPage : Tx.page.spec (GF := GF) (hG := hG))
    (hSplit : node.split.spec (GF := GF) (hG := hG))
    (hWrite : node.write.spec (GF := GF) (hG := hG))
    (hPut : node.put.spec (GF := GF) (hG := hG))
    (hSize : node.size.spec (GF := GF) (hG := hG))
    (hInc : TxStats.IncSpill.spec (GF := GF) (hG := hG))
    (hTxid : internal.common.Meta.Txid.spec (GF := GF) (hG := hG))
    (hPgid : internal.common.Meta.Pgid.spec (GF := GF) (hG := hG))
    (hId : internal.common.Page.Id.spec (GF := GF) (hG := hG))
    (hAssert : internal.common.Assert.spec (GF := GF) (hG := hG))
    (hFree : internal.freelist.Interface.Free.spec (GF := GF) (hG := hG)) :
    ⊢ spillIH (GF := GF) (hG := hG) := by
  unfold spillIH
  iloeb as IH
  iintro %K %tx %r %m %X %w %bl %n %rn %O %lo %hi %h %F %D %N %E %cs %Hpre %Φ ⟨Hw, Hdb⟩ HΦ
  obtain ⟨Hn, HG, Hcase⟩ := Hpre
  obtain ⟨B, HB, Hrn⟩ := node_of_bs Hn
  rcases Hcase with ⟨Hsp, Hbl, Hlive⟩ | Hu
  · -- a piece: `n.bucket.tx`, `n.spilled`, return
    icases wtxW_open K tx r m X $$ Hw with ⟨#Hpk, #Hcore, #Hreg, Hh, Hv, Hst, Hclose⟩
    ihave %Hok := wtxHeap_heapOK tx (DFrac.own 1) X $$ Hh
    have HliveB : bl ∈ X.liveB := (HG.2.2.1.2.2.1 bl B HB).1
    icases wtxHeap_setNode_bkt tx (DFrac.own 1) X bl B n rn HB Hrn $$ Hh with ⟨Hno, Hbo, Hf, Hback⟩
    rw [decide_eq_true Hlive, decide_eq_true HliveB]
    icases objOwn_node_ptr_acc X.v n (DFrac.own 1) true bl rn $$ Hno with ⟨Hn, Hnback⟩
    have hbtx : B.bv.tx' = tx := Hok.2.2.1 bl B HB
    unfold objOwn
    icases Hbo with ⟨Hb1, Hbtx, Hbo⟩
    icases typedPointsto_not_null_dup _ _ _ $$ Hn with ⟨Hn, %Hnn⟩
    iStructNamed Hn
    ihave Htxf : (∃ dqb : DFrac, bl.[Bucket, go!"tx"] ↦{dqb} tx ∗
        (bl.[Bucket, go!"tx"] ↦{dqb} tx -∗
          if bl = B.bv.tx'.[Tx, go!"root"] then bl.[Bucket, go!"tx"] ↦ B.bv.tx'
          else bl.[Bucket, go!"tx"] ↦□ B.bv.tx') : IProp GF) $$ [Hbtx]
    · rw [hbtx]
      by_cases hroot : bl = tx.[Tx, go!"root"]
      · rw [if_pos hroot]
        iexists DFrac.own 1
        iframe
        iintro H; iexact H
      · rw [if_neg hroot]
        icases Hbtx with #Hbtx
        iexists DFrac.discard
        isplitr
        · iexact Hbtx
        · iintro _; iexact Hbtx
    icases Htxf with ⟨%dqb, Htx, Htxb⟩
    wp_method_call
    wp_call
    rw [Hbl]
    wp_auto
    rw [Hsp]
    wp_auto
    ihave Hn : (n ↦ rn.nv : IProp GF)
      $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
    · iapply typedPointsto_combine _ _ _ Hnn
      simp only [TypedPointsto.typedPointstoDef]
      rw [Hbl, Hsp]
      iframe
    ihave Hno := Hnback $$ Hn
    ihave Hbtx := Htxb $$ Htx
    ihave Hh := Hback $$ %rn %(Hok.2.2.2.1 bl B n rn HB Hrn) [Hno] [Hb1 Hbtx Hbo] Hf
    · iexact Hno
    · iframe
    rw [setNode_self X bl n B rn HB Hrn]
    ihave Hw := Hclose $$ %X [] Hh Hv Hst
    · ipureintro; exact ⟨rfl, rfl, rfl⟩
    iapply HΦ
    unfold spPost
    ileft
    isplitr
    · ipureintro; rfl
    iexists X, w, []
    iframe
    ipureintro
    refine ⟨⟨rfl, rfl, rfl, HG, HG.2.1, fun s hs => hs, fun x hx => absurd rfl hx,
      fun F _ h => h, id⟩, Or.inl ⟨Hsp, rfl, rfl⟩⟩
  · -- the unspilled case: the sort, the children's loop, the rest (`spillTail_wp`), from the
    -- permuted state `Xp` (`n`'s children sorted) and back (`spPost_unperm`)
    obtain ⟨Hut, Hctx, Hsl, Hfr, Hvc, Hfc, Hts, Hpar0⟩ := Hu
    have Hun : uNode X bl n rn lo hi := uTree_uNode Hut Hn
    have Hsp0 : rn.nv.spilled' = false := Hun.2.2.1
    have Hlive : n ∈ X.live := Hun.1
    have Hbl : rn.nv.bucket' = bl := Hun.2.1
    have HnN : n ∈ N := uTree_head Hut
    icases wtxW_pers K tx r m X $$ Hw with ⟨Hw, #⟨Hpkg, Hcore, Hreg⟩⟩
    icases wtxW_heapOK K tx r m X $$ Hw with ⟨Hw, %Hok⟩
    have HliveB : bl ∈ X.liveB := (HG.2.2.1.2.2.1 bl B HB).1
    have hbtx : B.bv.tx' = tx := Hok.2.2.1 bl B HB
    have hpar : rn.nv.parent' ≠ n := Hok.2.2.2.1 bl B n rn HB Hrn
    have hd : objsDisj X.t := Hok.2.1
    have hkids := uTree_sortKids Hut Hn hpar
    have hF : liveFresh X := HG.2.2.2.1
    icases wtxW_sort_acc K tx r m X bl B n rn HB Hrn Hlive $$ Hw with ⟨Hno, Hbo, HQ, Hclose⟩
    icases (objOwn_live_node _ _ _ _ _).1 $$ Hno with ⟨Hn, Hins, Hcap, Hws, Hch, Hchcap, Hkey⟩
    icases objOwn_bkt_tx_acc X.v bl _ B $$ Hbo with ⟨%dqb, Htx, Hbo⟩
    rw [hbtx]
    icases ownSlice_loc_len _ _ $$ Hch with ⟨Hch, %Hlen⟩
    icases typedPointsto_not_null_dup _ _ _ $$ Hn with ⟨Hn, %Hnn⟩
    iStructNamed Hn
    wp_method_call
    wp_call
    rw [Hbl]
    wp_auto
    rw [Hsp0]
    wp_auto
    wp_apply (nodes_sort_wp hS hK hC X bl n rn.cs rn.nv.children' hkids hF Hlen) $$ [Hch HQ]
      as ⟨%l, Hch, HQ, %Hperm⟩
    · iframe
    ihave Hn : (n ↦ rn.nv : IProp GF)
      $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
    · iapply typedPointsto_combine _ _ _ Hnn
      simp only [TypedPointsto.typedPointstoDef]
      rw [Hbl, Hsp0]
      iframe
    ihave Hbo := Hbo $$ Htx
    ihave Hno : objOwn X.v n (DFrac.own 1) true (.node bl { rn with cs := l })
      $$ [Hn Hins Hcap Hws Hch Hchcap Hkey]
    · iapply (objOwn_live_node _ _ _ _ _).2
      iframe
      simp only [eq_self_iff_true]
      iexact Hkey
    ihave Hw := Hclose $$ %{ rn with cs := l } %hpar Hno Hbo HQ
    -- the permuted state
    have hpre' := spPre_perm hd HB Hrn Hperm Hut Hctx HG Hsl Hfr Hvc Hfc Hts Hpar0
    have hXv : (X.setNode bl n { rn with cs := l }).v = X.v := by rw [setNode_perm_eq HB]
    have hlvp : n ∈ (X.setNode bl n { rn with cs := l }).live := by
      rw [WX.setNode_live]; exact Hlive
    ihave Hdb : wdbW K tx (X.setNode bl n { rn with cs := l }).v w $$ [Hdb]
    · rw [hXv]; iexact Hdb
    wp_bind (App (App (App (Val doFor) _) _) _)
    by_cases hleaf : rn.nv.isLeaf' = true
    · have hcs0 : rn.cs = [] := by
        cases Hut with
        | leaf _ r _ _ _ hr' _ _ hcs => rw [Hn] at hr'; cases hr'; exact hcs
        | branch _ r _ _ _ _ hr' _ hl' => rw [Hn] at hr'; cases hr'; rw [hleaf] at hl'; cases hl'
      have hl0 : l = [] := by rw [hcs0] at Hperm; exact List.Perm.eq_nil Hperm.symm
      have H := fun Φ' => spill_loop_nil_wp (GF := GF) K tx r m _ bl n { rn with cs := l } n_ptr
        i_ptr «$res0_ptr» Φ' (node_perm_self HB) hlvp hl0
      unfold spLoopE spCondE spBodyE spPostE at H
      iapply (H _)
      iframe
      iintro Hw Hn Hi
      wp_pure
      wp_pure
      wp_pure
      have hend : spEnd (X.setNode bl n { rn with cs := l }) w bl n { rn with cs := l } O lo hi h D
          N E (X.setNode bl n { rn with cs := l }) w { rn with cs := l } [] [] :=
        Or.inl ⟨hleaf, rfl, rfl, rfl, rfl, rfl⟩
      have Hsend := spillTail_wp (GF := GF) (hG := hG) hAlloc hPage hSplit hWrite hPut hSize hInc
        hTxid hPgid hId hK hAssert hFree K tx r m _ w bl n { rn with cs := l } O lo hi h F D N E cs
        _ w { rn with cs := l } [] [] n_ptr tx_ptr «$res0_ptr» GoInterface.nil hpre' Hsp0 hend
      wp_bind (spillTail _ _ _)
      ihave Hwp := Hsend $$ [IH] Hw Hdb Hn tx «$res0»
      · imodintro; inext; unfold spillIH; iexact IH
      iapply wp_wand $$ Hwp
      iintro %v ⟨%hv, %err, Hres, Hn, Htx, Hpost⟩
      subst hv
      wp_pures
      wp_load
      iapply HΦ
      iapply (spPost_unperm hd HB Hrn Hperm HG K tx r m HnN Hsp0 (uTree_not_own_child Hut Hn Hsp0) err) $$ Hpost
    · have hleaf' : rn.nv.isLeaf' = false := by
        cases e : rn.nv.isLeaf'
        · rfl
        · exact absurd e hleaf
      obtain ⟨h', es, hh, hl0⟩ := spLoop_start hd HB Hrn Hperm Hut hleaf' HG Hsl Hfr Hpar0
      have H := fun Φ' => spill_loop_wp (GF := GF) K tx r m _ w bl n { rn with cs := l } O lo hi h'
        D N E es n_ptr i_ptr «$res0_ptr» GoInterface.nil Φ' hl0 Hfc
        (by rw [setNode_perm_eq HB]; exact Hts)
      unfold spLoopE spCondE spBodyE spPostE at H
      iapply (H _)
      isplitr
      · imodintro; inext; unfold spillIH; iexact IH
      iframe
      iintro %v Hv
      unfold spLoopPost
      icases Hv with (⟨%hv, Hn, Hres, %j, %XE, %wE, %rE, %esE, %stE, %TE, Hi, Hw, Hdb, %Hl⟩ |
        ⟨%hv, Hn, Hi, %err, Hres, %Herr, #Hok, %X', %w', %st, %Hf, Hst⟩)
      · subst hv
        wp_pure
        wp_pure
        wp_pure
        have hend : spEnd (X.setNode bl n { rn with cs := l }) w bl n { rn with cs := l } O lo hi h D
            N E XE wE rE stE TE :=
          Or.inr ⟨hleaf', h', esE, sint.nat j, hh, Hl.1, Hl.2, Hl.1.chs⟩
        have Hsend := spillTail_wp (GF := GF) (hG := hG) hAlloc hPage hSplit hWrite hPut hSize hInc
          hTxid hPgid hId hK hAssert hFree K tx r m _ w bl n { rn with cs := l } O lo hi h F D N E cs
          XE wE rE stE TE n_ptr tx_ptr «$res0_ptr» GoInterface.nil hpre' Hsp0 hend
        wp_bind (spillTail _ _ _)
        ihave Hwp := Hsend $$ [IH] Hw Hdb Hn tx Hres
        · imodintro; inext; unfold spillIH; iexact IH
        iapply wp_wand $$ Hwp
        iintro %v ⟨%hv, %err, Hres, Hn, Htx, Hpost⟩
        subst hv
        wp_pures
        wp_load
        iapply HΦ
        iapply (spPost_unperm hd HB Hrn Hperm HG K tx r m HnN Hsp0 (uTree_not_own_child Hut Hn Hsp0) err) $$ Hpost
      · subst hv
        wp_pures
        wp_load
        iapply HΦ
        unfold spPost
        iright
        isplitr
        · ipureintro; exact Herr
        isplitr
        · iexact Hok
        iexists X', w', st
        isplitr
        · ipureintro; exact spErr_st (spErr_trans (spErr_setNode X w bl n _) Hf) (List.nil_append _)
        iexact Hst

/-- **`node.spill.spec'`**, from `wp_aux`. -/
theorem node.spill.wp_proof' (hS : sort.«Sort».spec (GF := GF) (hG := hG))
    (hK : internal.common.Inode.Key.spec (GF := GF) (hG := hG))
    (hC : bytes.Compare.spec (GF := GF) (hG := hG))
    (hAlloc : Tx.allocate.spec (GF := GF) (hG := hG))
    (hPage : Tx.page.spec (GF := GF) (hG := hG))
    (hSplit : node.split.spec (GF := GF) (hG := hG))
    (hWrite : node.write.spec (GF := GF) (hG := hG))
    (hPut : node.put.spec (GF := GF) (hG := hG))
    (hSize : node.size.spec (GF := GF) (hG := hG))
    (hInc : TxStats.IncSpill.spec (GF := GF) (hG := hG))
    (hTxid : internal.common.Meta.Txid.spec (GF := GF) (hG := hG))
    (hPgid : internal.common.Meta.Pgid.spec (GF := GF) (hG := hG))
    (hId : internal.common.Page.Id.spec (GF := GF) (hG := hG))
    (hAssert : internal.common.Assert.spec (GF := GF) (hG := hG))
    (hFree : internal.freelist.Interface.Free.spec (GF := GF) (hG := hG)) :
    node.spill.spec' (GF := GF) (hG := hG) := by
  intro K tx r m X w bl n rn O lo hi h F D N E cs hpre
  have H := node.spill.wp_aux hS hK hC hAlloc hPage hSplit hWrite hPut hSize hInc hTxid hPgid hId
    hAssert hFree
  unfold spillIH at H
  iintro %Φ HP HΦ
  ihave #H := H
  iapply H $$ %K %tx %r %m %X %w %bl %n %rn %O %lo %hi %h %F %D %N %E %cs %hpre HP
  inext
  iintro %err Hpost
  iapply HΦ
  iexact Hpost

end proof

end Spill

end bbolt
end EtcdGrove
end Perennial
