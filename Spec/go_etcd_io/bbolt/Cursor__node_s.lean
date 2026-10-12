module
public import Proof.go_etcd_io.bbolt.WriteTxClean
public import Proof.go_etcd_io.bbolt.WriteTxShape
public import Proof.go_etcd_io.bbolt.PathFlags

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

/-- `c.node()` (`Cursor.node.spec`) with the bucket's shape: the nodes it materializes take
their positions' tokens, the keys stay a B+tree's, nested buckets' entries stay where they are,
if the path descended by a key `k` (`kroute`), `k` is within the leaf's bounds, and the leaf's
entries with a key are those of the path's end (`pathKey`). -/
abbrev Cursor.node.sspec : Prop :=
  ∀ (γ : GName) (cl : Loc) (cv : Cursor) (path : List elemRef) (W : WView) (hwm : Nat) (bl : Loc)
    (B : BRec) (txl : Loc) (st : TxStats) (pmap : GoMap) (pm : GMap w64 Loc) (dqp : DFrac),
  cv.bucket' = bl → wctxOK W hwm bl B txl pm → wpath W B B.ib.root' path →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ cl ↦ cv ∗ cv.stack' ↦* path ∗
      wctx W bl B txl pmap pm dqp ∗ structFieldRef Tx go!"stats" txl ↦ st ∗ bktShape γ W B }}
    (App (Val (cl @!! go.GoType.PointerType Cursor.ty @!! go!"node")) (Val #()))
  {{ (l : Loc) (B' : BRec) (st' : TxStats), RET #l;
      cl ↦ cv ∗ cv.stack' ↦* path ∗ wctx W bl B' txl pmap pm dqp ∗
      structFieldRef Tx go!"stats" txl ↦ st' ∗ bktShape γ W B' ∗
      ⌜bktClean W hwm bl B' ∧ bktGrows B B' ∧ (∃ r, B'.ns !! l = some r ∧ r.nv.isLeaf' = true) ∧
        (∀ k v, entryIn W B k v → entryIn W B' k v) ∧
        (∀ k, kroute W B k B.ib.root' path →
          ∃ bnd, bktKeysB W B' bnd ∧ keyIn (bnd l).1 (bnd l).2 k) ∧
        ∀ k P, pathKey W B k P B.ib.root' path → ∀ r, B'.ns !! l = some r →
          ∀ w ∈ r.ws, w.key = k → P w.flags⌝ }}

end spec

end bbolt
end EtcdGrove
end Perennial
