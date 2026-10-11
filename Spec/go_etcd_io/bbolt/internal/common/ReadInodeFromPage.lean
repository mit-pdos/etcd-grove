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

/-- `ReadInodeFromPage(p)`: a new slice of the page's inodes (`inodesOf`), whose keys and
values point into the page. It panics on a page that is not readable (a key out of bounds or
empty). -/
abbrev ReadInodeFromPage.spec : Prop :=
  ∀ (l : Loc) (pg : List w8) (q : DFrac),
  l.locCar ≠ 0 → pageReadable pg →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ bytesPointsto l q pg }}
    (App (Val #(functions ReadInodeFromPage [])) (Val #l))
  {{ (s : GoSlice), RET #s; bytesPointsto l q pg ∗ s ↦* inodesOf l pg ∗
      ownSliceCap Inode s (DFrac.own 1) }}

end spec

end bbolt
end EtcdGrove
end Perennial
