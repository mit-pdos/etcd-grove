/-
`node.spill` (U9e, `notes/bbolt-proof-plan.md`): the proof of its unit-internal spec
(`Spill/NodeSpec`'s `node.spill.spec'`), by Löb induction over its recursive calls (`wp_aux`: the
children's spills, the new root's). Status: the spilled case (a piece returns at once) is proved;
the unspilled case is not yet (a `sorry`; its steps are listed at it).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.NodeSpec
public import Proof.go_etcd_io.bbolt.Spill.SlotInv
public import Proof.go_etcd_io.bbolt.Spill.UTreeFrame
public import Proof.go_etcd_io.bbolt.Rebalance.Heap
public import Proof.go_etcd_io.bbolt.Spill.DerefHeap

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

/-- `node.spill.spec'` as an Iris proposition (for the recursion, Löb). -/
def spillW : IProp GF :=
  iprop(∀ (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (w : WDb) (bl n : Loc) (rn : NRec)
    (O : List Nat) (lo hi : Option (List w8)) (h : Nat) (F D : List Nat) (N : List Loc)
    (E : List El) (cs : SpCase),
    ⌜spPre X w bl n rn O lo hi h F D N E cs⌝ → ∀ Φ, (wtxW K tx r m X ∗ wdbW K tx X.v w) -∗
      ▷ (∀ err, spPost K tx r m X w bl n rn O lo hi h D N E cs err -∗ Φ #err) -∗
      WP (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"spill")) (Val #())) {{ Φ }})

/-- **`node.spill`, by Löb.** -/
theorem node.spill.wp_aux : ⊢ spillW (GF := GF) (hG := hG) := by
  unfold spillW
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
      fun F _ h => h⟩, Or.inl ⟨Hsp, rfl, rfl⟩⟩
  · -- the unspilled case. Steps (`notes/bbolt-proof-plan.md`, U9e hand-off):
    -- 1. `sort.Sort(n.children)` (`Spill/SortNodes.nodes_sorter`, the children a permutation);
    -- 2. the children's loop: Löb `IH` on each child (`spCtx .child n …`, `O` the slots of the
    --    other entries and `O`), `uTree_frame` for the siblings, the parent's entries
    --    (`parentSpilled`) re-establishing `n`'s `uTree` (entry `j` replaced by finished pieces);
    -- 3. `n.children = nil`, the children killed (`wtxHeap_kill`; all spilled, `spilledN`);
    -- 4. `n.split(pageSize)` (`Spill/Split.node.split.spec`), the pieces inserted into the heap;
    -- 5. per piece: `Free` of `n`'s page (`node.free`'s body, `slotInv_free`), `allocate`
    --    (`slotInv_alloc`/`slotInv_allocHwm`, `allocRes_derefPre'`, `uTree_frame` through
    --    `derefRel`/`rebase`), `node.write` (`Spill/PageBuf`, `sTree_wLeaf`/`sTree_wBranch`),
    --    `parent.put` (child case: `parentSpilled`; top case: the new root's entries);
    -- 6. the top case's new root: Löb `IH` on it (`spCtx .top`).
    -- U9f's pure lemmas for step 2: `Spill/UTreeParent.uBr_of_uTree` (the branch facts `uBr`),
    -- `Spill/ChildStep.uBr_childStep` (one unspilled child's spill: `uBr`, `slotInv`, `spFree`
    -- after, from its `spDone`; built on `Spill/UTreeReplace2.uBr_replace`), the spilled
    -- children kept by `spilledN_frame`; after the loop `uEnt_fin_of_spilled` on every entry.
    sorry

/-- **`node.spill.spec'`**, from `wp_aux`. -/
theorem node.spill.wp_proof' : node.spill.spec' (GF := GF) (hG := hG) := by
  intro K tx r m X w bl n rn O lo hi h F D N E cs hpre
  have H := node.spill.wp_aux (GF := GF) (hG := hG)
  unfold spillW at H
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
