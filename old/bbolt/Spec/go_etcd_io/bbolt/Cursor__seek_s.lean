module
public import Proof.go_etcd_io.bbolt.WriteCursorLemmas
public import Proof.go_etcd_io.bbolt.WriteTxShape
public import Proof.go_etcd_io.bbolt.PathFlags

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt

section defs
variable [ext : FfiSyntax] [go_gctx : GoGlobalContext]

/-- The result `kv` of a seek is the element of the path's last element `e` at its index: of
its leaf node (`nodeKV`) or of its page (`kvResult`). -/
def seekAt (W : WView) (B : BRec) (path : List elemRef) (kv : GoSlice × GoSlice × w32) : Prop :=
  ∃ e, path.getLast? = some e ∧
    ((e.node' ≠ null ∧ ∃ r, B.ns !! e.node' = some r ∧ kv = nodeKV r.ins (sint.Z e.index')) ∨
     (e.node' = null ∧ ∃ pid pg, wpageAt W B pid = some (e.page', pg) ∧
        kv = kvResult e.page' pg (sint.Z e.index')))

/-- The key's bytes `kbs` are those of the entry at the index of the path's last element `e`
(of its leaf node's entries, or of its leaf page), if the index is inside it. -/
def seekKey (W : WView) (B : BRec) (path : List elemRef) (kbs : List w8) : Prop :=
  ∀ e, path.getLast? = some e →
    (∀ r w, e.node' ≠ null → B.ns !! e.node' = some r →
      r.ws[(sint.Z e.index').toNat]? = some w →
      ¬ (r.ins.length = 0 ∨ (r.ins.length : Int) ≤ sint.Z e.index') → w.key = kbs) ∧
    (e.node' = null → ∀ pid pg, wpageAt W B pid = some (e.page', pg) →
      ¬ (pageCount pg = 0 ∨ (pageCount pg : Int) ≤ sint.Z e.index') →
      leafKey pg (sint.Z e.index').toNat = kbs)

end defs

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `c.seek(key)` of a writer's cursor (`Cursor.seek.wspec`), with the descent's routing: the
path descends by the key (`kroute`), so its leaf is the one whose bounds hold the key; and an
entry with the key of the leaf it ends at is the one returned (`pathKey`: its flags are `f`, and
the key returned, of bytes `kbs`, is the key); the result is the element of the path's last
element (`seekAt`), and the key's bytes are that element's (`seekKey`). -/
abbrev Cursor.seek.sspec : Prop :=
  ∀ (cl : Loc) (cv : Cursor) (es : List elemRef) (W : WView) (hwm : Nat) (bl : Loc)
    (B : BRec) (txl : Loc) (pmap : GoMap) (pm : GMap w64 Loc) (dqp : DFrac)
    (key : GoSlice) (kb : List w8) (dk : DFrac),
  cv.bucket' = bl → wctxOK W hwm bl B txl pm →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ cl ↦ cv ∗ cv.stack' ↦* es ∗
      ownSliceCap elemRef cv.stack' (DFrac.own 1) ∗ wctx W bl B txl pmap pm dqp ∗ key ↦*{dk} kb }}
    (App (Val (cl @!! go.GoType.PointerType Cursor.ty @!! go!"seek")) (Val #key))
  {{ (cv' : Cursor) (path : List elemRef) (k v : GoSlice) (f : w32), RET (PairV (PairV #k #v) #f);
      ⌜cv'.bucket' = bl ∧ wpath W B B.ib.root' path ∧ kvSrcOK W hwm B (k, v, f) ∧
        kroute W B kb B.ib.root' path ∧ seekAt W B path (k, v, f) ∧
        ∃ kbs, keySrcIs W B k kbs ∧ seekKey W B path kbs ∧
          pathKey W B kb (fun fl => fl = f ∧ kbs = kb) B.ib.root' path⌝ ∗
      cl ↦ cv' ∗ cv'.stack' ↦* path ∗ ownSliceCap elemRef cv'.stack' (DFrac.own 1) ∗
      wctx W bl B txl pmap pm dqp ∗ key ↦*{dk} kb }}

end spec

end bbolt
end EtcdGrove
end Perennial
