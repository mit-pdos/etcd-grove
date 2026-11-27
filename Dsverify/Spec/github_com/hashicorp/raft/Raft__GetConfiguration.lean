/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__GetConfiguration.lean (241f27e).
-/
/-
`raft.Raft.GetConfiguration`'s spec (stage 4 interface).
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

/-- `(*Raft).GetConfiguration()` (stage 4), on any goroutine: a `*configurationsFuture` (already
answered `nil`; the client never calls `Error()` in scope) whose `configurations` field holds, as
latest, a copy of the latest configuration cell's value (`getLatestConfiguration`: no servers, or a
valid configuration, `cfgOpt`; it may not be committed). -/
abbrev github_com.hashicorp.raft.Raft.GetConfiguration.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"GetConfiguration")) (Val #()))
  {{ (fi : GoInterface), RET #fi; ∃ (f : Loc) (cf : configurations),
      ⌜fi = interface.mkOk (go.GoType.PointerType configurationsFuture.ty) #f⌝ ∗
      f.[configurationsFuture, go!"configurations"] ↦ cf ∗ cfgOpt γ cf.latest' }}

end spec

end Perennial
