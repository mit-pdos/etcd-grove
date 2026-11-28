/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__getRPCHeader.lean (241f27e).
-/
/-
`raft.(*Raft).getRPCHeader`'s spec (written by MAIN-C for `electSelf`/`preElectSelf`; any
main-goroutine subsystem may use it): a header with version 3 and the server's id bytes.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.main.MainCLemmas
public import Dsverify.Proof.github_com.hashicorp.raft.iface.Net

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

/-- `(*Raft).getRPCHeader()`. -/
abbrev github_com.hashicorp.raft.Raft.getRPCHeader.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"getRPCHeader")) (Val #()))
  {{ (h : RPCHeader), RET #h; hdrOk h i }}

end spec

end Perennial
