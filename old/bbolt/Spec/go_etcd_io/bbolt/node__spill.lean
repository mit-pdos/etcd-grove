module
public import Proof.go_etcd_io.bbolt.SpillNode
public import Proof.go_etcd_io.bbolt.SpillFit
public import Proof.go_etcd_io.bbolt.SpillNodeForest

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
variable [float_sem : go.FloatConvSemantics]

/-- `n.spill()` of the root node `rn` of the bucket `bl` (record `B`), during `Commit`'s spill
(`spillR`, `spillG`: `SpillState.lean`): every node of the bucket unspilled (`subU`, from the
root, its bounds `bnd` exact, its children's kind `kd`), holding its tokens and its entries'
written trees (`rtoks`, at the node's height `ht` less one: `nodeHts`; the tree written has
its leaves at one depth). Each node is split (`node.split`), its old page freed (to the stash
`F`), written to a new dirty page (`Tx.allocate`; a remap dereferences the transaction), and
put into its parent; a split root gets new parents, spilled in turn. The tree written is the
page `pid` of the new top node, its parent chain from `rn` the bucket's nodes now. Its parts fit
a page write if the split threshold is at most the page size (`splitThr`, a float fact), the
page size below 1 MiB, and every inode's key and value at most 2^28 bytes (`SpillFit.lean`).
On an error (an allocation's), what `Commit`'s rollback needs (`spillErr`). -/
abbrev node.spill.spec : Prop :=
  ∀ (I : FLImpl (GF := GF)) (γd : DBNames) (γ : GName) (W : WView) (txl : Loc) (txid : w64)
    (T : WTx) (ρ : DBState) (F : GMap Nat (List w8)) (K : Loc → Bool) (bl : Loc) (B : BRec)
    (bnd : Loc → Option (List w8) × Option (List w8)) (kd : Loc → Nat) (ht : Loc → Nat) (S : List Loc),
  I.FreeSpec → spillG (hG := hG) W txl txid T ρ F → T.bs !! bl = some B →
  B.bv.rootNode' ≠ null → (∀ r, B.ns !! B.bv.rootNode' = some r → r.nv.parent' = null) →
  bnd B.bv.rootNode' = (none, none) → subU W bl B bnd kd K B.bv.rootNode' S → nodeHts B ht →
  (∀ l, (B.ns !! l).isSome ↔ l ∈ S) →
  uint.Z (splitThr (W64 (W.ps : Int)) B.bv.FillPercent') ≤ W.ps → W.ps < 2 ^ 20 →
  (∀ l r, B.ns !! l = some r → ∀ w ∈ r.ws, w.key.length + w.value.length ≤ 2 ^ 28) →
  (∀ l r, B.ns !! l = some r → r.nv.parent' ≠ null → 0 < r.ws.length) →
  (∀ l r, B.ns !! l = some r → r.nv.isLeaf' = false → r.nv.pgid' ≠ W64 0) →
  (∀ c l, B.nm !! c = some l → c = W64 0 ∨ (W.pages !! uint.nat c).isSome) →
  (∀ l r w, B.ns !! l = some r → r.nv.isLeaf' = false → w ∈ r.ws →
    (W.pages !! uint.nat w.pgid).isSome) →
  treeOK bl B →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ spillR I γd γ W txl txid T ρ F K ∗
      [∗list] l ∈ S, ∃ r, ⌜B.ns !! l = some r⌝ ∗ rtoks γ (spillPages W T) B (bnd l) (kd l) (ht l - 1) r }}
    (App (Val (B.bv.rootNode' @!! go.GoType.PointerType node.ty @!! go!"spill")) (Val #()))
  {{ (err : GoInterface), RET #err;
      (⌜err = interface.nil⌝ ∗ ∃ (W' : WView) (T' : WTx) (ρ' : DBState) (F' : GMap Nat (List w8))
          (K' : Loc → Bool) (B' : BRec) (p : List Loc) (top : Loc) (pid : w64)
          (Q : GMap Nat (List w8)),
        spillR I γd γ W' txl txid T' ρ' F' K' ∗ wtreeQ γ Q (uint.nat pid) none none ∗
        ⌜spillG (hG := hG) W' txl txid T' ρ' F' ∧ spillFrame T T' (· = bl) ∧ W'.pages = W.pages ∧
          T'.bs !! bl = some B' ∧ B'.bv = B.bv ∧ B'.ib = B.ib ∧ B'.nm = B.nm ∧ B'.bm = B.bm ∧
          upPath B'.ns B.bv.rootNode' p top ∧ p.Nodup ∧ (∀ l, (B'.ns !! l).isSome ↔ l ∈ p) ∧
          (Q !! uint.nat pid).isSome ∧ Q ⊆ spillPages W' T' ∧ (T'.bufs !! pid).isSome ∧
          (∀ c C' l, c ≠ bl → T'.bs !! c = some C' → (C'.ns !! l).isSome → K' l = K l) ∧
          ∃ rt, B'.ns !! top = some rt ∧ rt.nv.pgid' = pid ∧ rt.nv.spilled' = true ∧
            rt.nv.parent' = null ∧ rt.cs = []⌝) ∨
      (⌜err ≠ interface.nil⌝ ∗ spillErr I γd txl txid) }}

end spec

end bbolt
end EtcdGrove
end Perennial
