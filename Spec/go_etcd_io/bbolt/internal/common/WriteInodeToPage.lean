/-
`WriteInodeToPage`'s spec (`internal/common/inode.go`; U0b of `notes/bbolt-proof-plan.md`).
-/
module

public import Proof.go_etcd_io.bbolt.PkgInit
public import Proof.go_etcd_io.bbolt.Model.Page

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt
namespace internal
namespace common

open Iris Iris.BI go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

/-- `WriteInodeToPage(inodes, p)`: lays the inodes `ms` out after the header of the page at `p`, as a
leaf page if its flags are `LeafPageFlag` and as a branch page otherwise: the elements, then each
key and its value (`pageBody`); the bytes after that are untouched. The header is only read. It
returns the end of what it wrote, `16 + (pageBody leaf ms).length`. It panics on an empty key
(excluded by `pageFits`) and, on a branch page, on an inode whose page id is the page's own
(premise); the layout must fit in the bytes after the header (premise). Each inode's key and value
are read through one fraction `dqb`. -/
abbrev WriteInodeToPage.spec : Prop :=
  ∀ (s : GoSlice) (ins : List Inode) (ms : List InodeM) (dqs dqb : DFrac) (p : Loc) (hdr : Page)
    (rest : List w8),
  0 < p.addr → pageFits ms → (pageBody true ms).length ≤ rest.length →
  (hdr.flags' ≠ W16 2 → ∀ m ∈ ms, m.pgid ≠ hdr.id') →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ s ↦*{dqs} ins ∗
      ([∗list] it;m ∈ ins;ms, ⌜it.flags' = m.flags ∧ it.pgid' = m.pgid⌝ ∗
        it.key' ↦*{dqb} m.key ∗ it.value' ↦*{dqb} m.value) ∗
      p ↦ hdr ∗ bytesPointsto (p +ₗ 16) (DFrac.own 1) rest }}
    (App (App (Val #(functions WriteInodeToPage [])) (Val #s)) (Val #p))
  {{ RET #(W32 ((16 + (pageBody (decide (hdr.flags' = W16 2)) ms).length : Nat) : Int));
      s ↦*{dqs} ins ∗
      ([∗list] it;m ∈ ins;ms, ⌜it.flags' = m.flags ∧ it.pgid' = m.pgid⌝ ∗
        it.key' ↦*{dqb} m.key ∗ it.value' ↦*{dqb} m.value) ∗
      p ↦ hdr ∗
      bytesPointsto (p +ₗ 16) (DFrac.own 1)
        (pageBody (decide (hdr.flags' = W16 2)) ms ++ rest.drop (pageBody true ms).length) }}

end spec

end common
end internal
end bbolt
end EtcdGrove
end Perennial
