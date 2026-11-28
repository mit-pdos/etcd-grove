/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__restoreSnapshot.lean (241f27e).
-/
/-
`raft.(*Raft).restoreSnapshot`'s spec (API-internal): the snapshot store has no snapshots, nothing is restored.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.core.Laws

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std
open github_com.hashicorp.raft github_com.hashicorp.raft.gprot github_com.hashicorp.raft.proto

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

/-- `(*Raft).restoreSnapshot`: (stage 3) a fresh snapshot store (`isSnapStore`, latest none): `List`
returns none, nothing is restored; returns nil. -/
abbrev github_com.hashicorp.raft.Raft.restoreSnapshot.spec : Prop :=
  ∀ (r : Loc) (x : GoInterfaceOk) (ownSS : SnapLatest → IProp GF) (eof : GoInterface) (tid : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗
     r.[Raft, go!"snapshots"] ↦□ (GoInterface.ok x) ∗ isSnapStore x ownSS eof ∗ ownSS none ∗
     rtok tid }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"restoreSnapshot")) (Val #()))
  {{ RET #interface.nil; ownSS none ∗ rtok tid }}

end spec

end Perennial
