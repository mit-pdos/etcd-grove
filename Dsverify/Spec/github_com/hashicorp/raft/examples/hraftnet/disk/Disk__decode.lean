/-
(hraft_robust R3) The spec of `disk.(*Disk).decode` (`disk.go`).
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
/-- `d.decode(b)`, on a fresh `*Disk` and the bytes of a well-formed image `I`, returns nil and leaves `d` at
`I` (nothing staged). -/
abbrev github_com.hashicorp.raft.examples.hraftnet.disk.Disk.decode.spec : Prop :=
  ∀ (d : Loc) (b : GoSlice) (I : DiskImg), I.Ok →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.disk ∗ diskMem0 d ∗
      b ↦*□ encImg I }}
    (App (Val (d @!! go.GoType.PointerType Disk.ty @!! go!"decode")) (Val #b))
  {{ RET #interface.nil; diskMem d I (W64 0) }}

end spec

end Perennial
