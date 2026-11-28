/-
(hraft_robust R3) The spec of `disk.(*Snaps).encode` (`snap.go`).
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
/-- `s.encode()` returns the bytes of `s`'s image (`encSnap`), in a fresh slice. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.disk.Snaps.encode.spec : Prop :=
  ∀ (s : Loc) (S : SnapImg),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.disk ∗ snapsMem s S }}
    (App (Val (s @!! go.GoType.PointerType Snaps.ty @!! go!"encode")) (Val #()))
  {{ (b : GoSlice), RET #b; snapsMem s S ∗ b ↦* encSnap S ∗ ownSliceCap w8 b (DFrac.own 1) }}

end spec

end Perennial
