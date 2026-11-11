/-
`node.spill` after its children's loop (U9r, `notes/bbolt-proof-plan.md`): **the split's heap
step** (`splitStep_wp`): `n.split(uintptr(tx.db.pageSize))` on `wtxW`, from the state `X1` after
`n.children = nil` (`Spill/NodeSpillPiecesKill.wtxW_nilCh`) to a state `X2` related by
`Spill/NodeSpillSplitDefs.splitRel` (`n`'s record and its parent's reshaped, the fresh pieces and
the top case's new parent added), the returned slice the pieces' locations.
-/
module

public import Proof.go_etcd_io.bbolt.Spill.NodeSpillSplitOpen
public import Proof.go_etcd_io.bbolt.Spill.NodeSpillPiecesCode

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section code
variable [GooseExts] [GoGlobalContext]

/-- **`n.split(uintptr(tx.db.pageSize))`** as `spillTail` has it (the cells `np`, `txp`). -/
abbrev splitCall (np txp : Loc) : Expr :=
  (Let "$a0" (App (Val (GoInstruction (Convert go.int go.uintptr))) (App (Val (GoInstruction (GoLoad go.int))) (App (Val (GoInstruction (StructFieldRef DB.ty go!"pageSize"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType DB.ty)))) (App (Val (GoInstruction (StructFieldRef Tx.ty go!"db"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType Tx.ty)))) (Val #txp)))))))
      (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType node.ty) go!"split"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Val #np))) (Var "$a0")))

end code

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **The split's heap step** (see the module doc). `n` (record `rN` in `X1`, live, of bucket `bl`,
owning its inodes' capacity, its entries one per inode); its parent, if any, a live node of `bl`.
After: `splitRel`, and every piece fits a page (`pieceFits 4096`), with at least two inodes when
split. -/
theorem splitStep_wp (hSplit : node.split.spec (GF := GF) (hG := hG))
    (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X1 : WX) (bl n : Loc) (rN : NRec) (np txp : Loc)
    (hn : X1.node bl n = some rN) (hlv : n ∈ X1.live) (hbl : rN.nv.bucket' = bl)
    (hcap : rN.capOwn = true) (hsp : rN.nv.spilled' = false) (hil : rN.ins.length = rN.ws.length)
    (hbnd : insBnd rN.ins)
    (hpar : rN.nv.parent' ≠ null → ∃ rp, X1.node bl rN.nv.parent' = some rp ∧
      rN.nv.parent' ∈ X1.live)
    (hch : rN.nv.children' = slice.nil := by first | rfl | assumption)
    (Φ : val → IProp GF) :
    wtxW K tx r m X1 ∗ np ↦ n ∗ txp ↦ tx ∗
      (∀ (s : GoSlice) (xs : List (Loc × node × List Inode)) (wss : List (List WEntry))
          (pl : Loc) (rp' : NRec) (X2 : WX),
        ⌜splitRel X1 X2 bl n rN xs wss pl rp' ∧
          ∀ x ∈ xs, pieceFits 4096 x.2.2 ∧ (2 ≤ xs.length → 2 ≤ x.2.2.length)⌝ -∗
        wtxW K tx r m X2 -∗ s ↦* xs.map (·.1) -∗ np ↦ n -∗ txp ↦ tx -∗ Φ #s) ⊢
    WP (splitCall np txp) {{ Φ }} := by
  iintro ⟨Hw, Hnp, Htxp, HΦ⟩
  icases split_open K tx r m X1 bl n rN hn hlv hbl hcap hsp hil hch hpar $$ Hw
    with ⟨%pv, %pcs, %f, %dqb, %Hp, #Hpers, Hst, Hn, Hins, Hcap, Hfp, Htx, Hdb, Hpar, Hback⟩
  obtain ⟨Hnan, Hrdb⟩ := Hp
  icases Hpers with ⟨#Hpkg, #Hcore, #Hreg⟩
  ihave #Hps : (K.db.[DB, go!"pageSize"] ↦□ W64 4096 : IProp GF) $$ [Hcore]
  · iapply rbl_pageSize K; iexact Hcore
  rw [Hrdb]
  wp_auto
  wp_apply hSplit K tx r m 1 n rN.nv rN.ins f (DFrac.own 1) dqb pv pcs (W64 4096) hbnd Hnan
    (by decide) $$ [Hst Hn Hins Hcap Hfp Htx Hpar] as %s %xs ⟨Hst, Hfp, Htx, Hs, %Hflat, Hpost⟩
  · iframe; iframe #
  ihave Hb := Hback $$ %xs [Hst] [Hfp] [Htx] [Hdb] [] [Hpost]
  · iexact Hst
  · iexact Hfp
  · iexact Htx
  · iexact Hdb
  · ipureintro; exact Hflat
  · unfold splitPost; simp only [w4096, ne_eq]; iexact Hpost
  unfold splitBack
  icases Hb with ⟨%X2, %wss, %pl, %rp', Hw, %Hrel⟩
  iapply HΦ $$ %s %xs %wss %pl %rp' %X2 [] [Hw] [Hs] [Hnp] [Htxp]
  · ipureintro; exact Hrel
  · iexact Hw
  · iexact Hs
  · iexact Hnp
  · iexact Htxp

end proof

end Spill

end bbolt
end EtcdGrove
end Perennial
