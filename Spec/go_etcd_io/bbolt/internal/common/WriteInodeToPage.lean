/-
## `WriteInodeToPage(inodes, p)` (`internal/common/inode.go`)

**Users.** node.go:199 (`node.write`: into a page buffer from `Tx.allocate`, or a bucket value's inline page, bucket.go:849), after it sets the flags and the count. Snippet `ReqNodeRoundTrip`.
**Proof sketch.** the element area's start `16 + 16 n`; per item, `UnsafeByteSlice` of the data window (inside `bs` by the length premise), the element's setters through its typed view (`bytesPointsto_view`), the branch's `Assert(pgid != p.Id())`, two `copy`s from the item's key and value (read at their shares). The loop's invariant: the first `i` elements and data written as `nodeBody`'s prefix.
**Changes.** from `specs-ref`'s file of the same name: the page as its bytes (`writeNode`), header included, instead of a typed header and a tail; the result named by `writeNode`, read back by `writeNode_read`.
**Margin.** none: the post is what the code computes.
-/
module

public import Spec.go_etcd_io.bbolt.internal.common.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace BboltCommon

open Iris Iris.BI go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

/-- `WriteInodeToPage(ms, p)`: lays the items out after the page's header, as a leaf page if the header's flags say so and as a branch page otherwise (`writeNode`), and returns the end of what it wrote. It panics on an empty key (`nodeFits`) and, on a branch page, on a child that is the page itself (premise). Each item's key and value are read at their own shares. -/
def WriteInodeToPage.spec : Prop :=
  ∀ (s : GoSlice) (ivs : List Inode) (ms : List InodeM) (dqs : DFrac) (qk qv : Nat → DFrac)
    (p : Loc) (bs : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ s ↦*{dqs} ivs ∗
      ([∗list] k ↦ iv;m ∈ ivs;ms, ⌜iv.flags' = m.flags ∧ iv.pgid' = m.pgid⌝ ∗
        iv.key' ↦*{qk k} m.key ∗ iv.value' ↦*{qv k} m.value) ∗
      bytesPointsto p (DFrac.own 1) bs ∗
      ⌜nodeFits ms ∧ pageHeaderSize + (nodeBody true ms).length ≤ bs.length ∧
        (isLeafHdr (hdrOf bs) = false → ∀ m ∈ ms, m.pgid ≠ (hdrOf bs).id')⌝ }}
    (App (App (Val (@! go_etcd_io.bbolt.internal.common.WriteInodeToPage)) (Val #s)) (Val #p))
  {{ RET #(W32 ((pageHeaderSize + (nodeBody (isLeafHdr (hdrOf bs)) ms).length : Nat) : Int));
      s ↦*{dqs} ivs ∗
      ([∗list] k ↦ iv;m ∈ ivs;ms, ⌜iv.flags' = m.flags ∧ iv.pgid' = m.pgid⌝ ∗
        iv.key' ↦*{qk k} m.key ∗ iv.value' ↦*{qv k} m.value) ∗
      bytesPointsto p (DFrac.own 1) (writeNode bs ms) }}

end spec

end BboltCommon
end EtcdGrove
end Perennial
