/-
(hraft_robust R3) The spec of `disk.(*Snaps).decode` (`snap.go`).
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
/-- `s.decode(b)`, on a fresh `*Snaps` and the bytes of a well-formed image `S`, returns nil and leaves `s` at
`S` (the configuration's servers in a fresh slice). -/
abbrev github_com.hashicorp.raft.examples.hraftnet.disk.Snaps.decode.spec : Prop :=
  ∀ (s : Loc) (b : GoSlice) (S : SnapImg), S.Ok →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.disk ∗ snapsMem0 s ∗
      b ↦*□ encSnap S }}
    (App (Val (s @!! go.GoType.PointerType Snaps.ty @!! go!"decode")) (Val #b))
  {{ RET #interface.nil; snapsMem s S }}

end spec

end Perennial
