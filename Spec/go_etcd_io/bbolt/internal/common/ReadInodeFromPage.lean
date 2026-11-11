/-
`ReadInodeFromPage`'s spec (`internal/common/inode.go`; U0b of `notes/bbolt-proof-plan.md`).
-/
module

public import Proof.go_etcd_io.bbolt.PkgInit
public import Proof.go_etcd_io.bbolt.Model.PageAt

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs
namespace internal
namespace common

open Iris Iris.BI go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

/-- `ReadInodeFromPage(p)`: a new slice of the inodes of the page `pg` at `p` (`pageInodesAt`: a
leaf's flags, key and value, a branch's page id and key), whose keys and values are slices into the
page. A page whose flags are not `LeafPageFlag` is read as a branch page. It reads the header and
the elements only, not the keys' and values' bytes. It panics on an empty key (`Assert`), which
`pageReadable` excludes; the slices it makes must lie in the address space. -/
abbrev ReadInodeFromPage.spec : Prop :=
  ∀ (p : Loc) (pg : List w8) (dq : DFrac),
  pageReadable pg → 0 < p.addr →
  (∀ i < pageCount pg, p.addr + (elemEnd pg i : Int) ≤ maxAddr) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ bytesPointsto p dq pg }}
    (App (Val #(functions ReadInodeFromPage [])) (Val #p))
  {{ (s : GoSlice), RET #s; bytesPointsto p dq pg ∗ s ↦* pageInodesAt p pg ∗
      ownSliceCap Inode s (DFrac.own 1) }}

end spec

end common
end internal
end bbolt
end EtcdGrove
end Perennial
