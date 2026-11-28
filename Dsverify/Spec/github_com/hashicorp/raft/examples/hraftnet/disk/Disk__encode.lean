/-
(hraft_robust R3) The spec of `disk.(*Disk).encode` (`disk.go`).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.disk.Defs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.disk.Assumptions]

open github_com.hashicorp.raft github_com.hashicorp.raft.examples.hraftnet.disk in
/-- `d.encode()` returns the bytes of `d`'s image (`encImg`), in a fresh slice. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.disk.Disk.encode.spec : Prop :=
  ∀ (d : Loc) (I : DiskImg) (stg : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.disk ∗ diskMem d I stg }}
    (App (Val (d @!! go.GoType.PointerType Disk.ty @!! go!"encode")) (Val #()))
  {{ (b : GoSlice), RET #b; diskMem d I stg ∗ b ↦* encImg I ∗ ownSliceCap w8 b (DFrac.own 1) }}

end spec

end Perennial
