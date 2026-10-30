module
public import Spec.go_etcd_io.bbolt.node__free_x
public import Proof.go_etcd_io.bbolt.WriteCursor

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `b.free()` of a bucket whose tree is its materialized root leaf `rn` (struct `nv`; an
inlineable bucket, which `Bucket.spill` frees before writing it inline): an inline bucket
(root 0) is left alone; else its root page, the root node's, is freed (`node.free.xspec`: the
page's token to the stash), and the bucket's root becomes 0. -/
abbrev Bucket.free.xspec : Prop :=
  ∀ (I : FLImpl (GF := GF)) (γd : DBNames) (γ : GName) (W : WView) (hwm : Nat) (txl : Loc)
    (txid : w64) (ρ : DBState) (bl : Loc) (B : BRec) (pmap : GoMap) (pm : GMap w64 Loc)
    (mp : Loc) (mv : internal.common.Meta) (dqt : DFrac) (F : GMap Nat (List w8)) (nv : node),
  I.FreeSpec → viewOK W → B.bv.tx' = txl → mv.txid' = txid → freedOK W ρ.fl txid F →
  B.bv.rootNode' ≠ null → nv.bucket' = bl → nv.isLeaf' = true →
  (B.ib.root' = W64 0 → nv.pgid' = W64 0) →
  (B.ib.root' ≠ W64 0 → B.bv.page' = null ∧ resolve B B.ib.root' = some B.bv.rootNode' ∧
    (∀ c l, B.nm !! c = some l → l ≠ null) ∧ nv.pgid' = B.ib.root' ∧
    treeWF W.pages hwm (uint.nat B.ib.root') ∧ pm !! B.ib.root' = none) →
  W.data.locCar ≠ 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ bl ↦ B.bv ∗ B.bv.InBucket' ↦ B.ib ∗
      B.bv.nodes' ↦$ B.nm ∗ B.bv.rootNode' ↦ nv ∗ wView W ∗
      structFieldRef Tx go!"pages" txl ↦{dqt} pmap ∗ pmap ↦${dqt} pm ∗
      structFieldRef Tx go!"db" txl ↦{dqt} W.dbl ∗ structFieldRef Tx go!"meta" txl ↦{dqt} mp ∗
      mp ↦ mv ∗ dbWR I γd W txl txid ρ ∗ pgToks γ F ∗
      (if B.ib.root' = W64 0 then emp else (uint.nat B.ib.root' ↪[γ] () : IProp GF)) }}
    (App (Val (bl @!! go.GoType.PointerType Bucket.ty @!! go!"free")) (Val #()))
  {{ RET #(); ∃ (ρ' : DBState) (F' : GMap Nat (List w8)),
      bl ↦ B.bv ∗ B.bv.InBucket' ↦ ({ B.ib with root' := W64 0 } : internal.common.InBucket) ∗
      B.bv.nodes' ↦$ B.nm ∗ B.bv.rootNode' ↦ ({ nv with pgid' := W64 0 } : node) ∗ wView W ∗
      structFieldRef Tx go!"pages" txl ↦{dqt} pmap ∗ pmap ↦${dqt} pm ∗
      structFieldRef Tx go!"db" txl ↦{dqt} W.dbl ∗ structFieldRef Tx go!"meta" txl ↦{dqt} mp ∗
      mp ↦ mv ∗ dbWR I γd W txl txid ρ' ∗ pgToks γ F' ∗
      ⌜freedOK W ρ'.fl txid F' ∧ (∃ fl, ρ' = { ρ with fl := fl }) ∧
        (B.ib.root' = W64 0 → ρ' = ρ ∧ F' = F ∧ nv.pgid' = W64 0) ∧
        (B.ib.root' ≠ W64 0 → ∃ pg, W.pages !! uint.nat B.ib.root' = some pg ∧
          F' = <[uint.nat B.ib.root' := pg]> F ∧
          ρ'.fl = ρ.fl.freePages txid B.ib.root' (1 + pageOverflow pg))⌝ }}

end spec

end bbolt
end EtcdGrove
end Perennial
