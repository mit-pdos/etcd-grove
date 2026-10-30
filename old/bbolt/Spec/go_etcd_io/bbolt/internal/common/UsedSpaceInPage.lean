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

/-- The space of the inodes `ins` after `off` bytes: each key's and value's bytes (in 64-bit
arithmetic, as Go's `uintptr`). -/
def usedSpaceFrom (off : w64) (ins : List Inode) : w64 :=
  ins.foldl (fun o it => o + (it.key'.len + it.value'.len)) off

/-- `UsedSpaceInPage(inodes, p)`: the bytes a page of these inodes uses (the header, 16 per
element, the keys and values), as a `uint32`. -/
abbrev UsedSpaceInPage.spec : Prop :=
  ∀ (s : GoSlice) (ins : List Inode) (dq : DFrac) (p : Loc) (v : Page) (dq' : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ s ↦*{dq} ins ∗ p ↦{dq'} v }}
    (App (App (Val #(functions UsedSpaceInPage [])) (Val #s)) (Val #p))
  {{ RET #(W32 (uint.Z (usedSpaceFrom (W64 16 + W64 16 * s.len) ins)));
      s ↦*{dq} ins ∗ p ↦{dq'} v }}

end spec

end bbolt
end EtcdGrove
end Perennial
