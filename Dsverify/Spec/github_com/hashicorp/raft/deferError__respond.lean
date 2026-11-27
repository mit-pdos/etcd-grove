/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/deferError__respond.lean (241f27e).
-/
/-
`raft.(*deferError).respond`'s spec (raft-internal interface, notes/raft-iface.md). (stage 2, REPL-4: on any `*deferError`; through `*logFuture`, `*verifyFuture`, `*leadershipTransferFuture` by promotion, e.g. `deferError.respond_logFuture`.) With the responder side and an answer meeting its predicate (the first time), or after a response (a no-op).
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

/-- `(*deferError).respond` on the `*deferError` `d` (stage 2, REPL-4: any `*deferError`, e.g.
`triggerDeferErrorCh`'s; the futures' promoted calls are its instances, `deferError.respond_logFuture`):
with the responder side and an answer meeting its predicate (the first time), or after a response
(a no-op). -/
abbrev github_com.hashicorp.raft.deferError.respond.spec : Prop :=
  ∀ (d : Loc) (Q : GoInterface → IProp GF) (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ ((deferResp d Q ∗ Q err) ∨ deferDone d) }}
    (App (Val (d @!! go.GoType.PointerType deferError.ty @!! go!"respond")) (Val #err))
  {{ RET #(); deferDone d }}

end spec

end Perennial
