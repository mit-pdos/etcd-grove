module
public import Proof.go_etcd_io.bbolt.internal.common.Init
public import Proof.go_etcd_io.bbolt.internal.common.Inodes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt.internal.common

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

/-- `WriteInodeToPage(inodes, p)`: the inodes go onto the page `p` (whose header says whether
it is a leaf): after the header, the elements, then each key and its value; the rest of the
page is untouched. It returns the end of what it wrote. It panics on an empty key, or on a
branch inode whose child is the page itself; and the layout must fit in the page (in its
`rest` bytes) and below `MaxAllocSize`. -/
abbrev WriteInodeToPage.spec : Prop :=
  ∀ (s : GoSlice) (ins : List Inode) (dq : DFrac) (ks vs : List (List w8)) (q : DFrac)
    (p : Loc) (hdr : Page) (rest : List w8),
  p.locCar ≠ 0 → ins.length < 65536 →
  ks.length = ins.length → vs.length = ins.length →
  (∀ i < ins.length, 0 < (ks.getD i []).length) →
  16 + 16 * ins.length + kvLen ks vs ins.length ≤ 2147483647 →
  16 * ins.length + kvLen ks vs ins.length ≤ rest.length →
  (hdr.flags' ≠ W16 2 → ∀ i < ins.length, (ins.getD i (zero_val Inode)).pgid' ≠ hdr.id') →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ s ↦*{dq} ins ∗ inodeData ins ks vs q ∗ p ↦ hdr ∗
      bytesPointsto (p +ₗ 16) (DFrac.own 1) rest }}
    (App (App (Val #(functions WriteInodeToPage [])) (Val #s)) (Val #p))
  {{ RET #(W32 ((16 + 16 * ins.length + kvLen ks vs ins.length : Nat) : Int));
      s ↦*{dq} ins ∗ inodeData ins ks vs q ∗ p ↦ hdr ∗
      bytesPointsto (p +ₗ 16) (DFrac.own 1)
        (writtenElems (decide (hdr.flags' = W16 2)) ks vs ins ++ kvBytes ks vs ++
          rest.drop (16 * ins.length + kvLen ks vs ins.length)) }}

end spec

end bbolt
end EtcdGrove
end Perennial
