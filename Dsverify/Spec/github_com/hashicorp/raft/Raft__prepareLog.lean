/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__prepareLog.lean (241f27e).
-/
/-
`raft.(*Raft).prepareLog`'s spec (internal to the FSM subsystem: only `processLogs` calls it). On an
entry of the server's log (a command, a no-op or a configuration entry: `srvOwn_facts`), it returns
`nil` for a no-op and a fresh `commitTuple{l, future}` otherwise (the protocol version is 3, so a
configuration entry is sent; the default case, which panics, is unreachable).
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

/-- `(*Raft).prepareLog(l, future)`: `nil` for a no-op entry, a fresh tuple `{l, future}` for a
command, a configuration entry or (stage 2) a barrier. -/
abbrev github_com.hashicorp.raft.Raft.prepareLog.spec : Prop :=
  ∀ (r l fp : Loc) (k : Nat) (e : Entry),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗
     r.[Raft, go!"protocolVersion"] ↦□ (W64 3) ∗ logPtr l k e ∗
     ⌜e.kind = kCommand ∨ e.kind = kNoop ∨ e.kind = kConfig ∨ e.kind = kBarrier⌝ }}
    (App (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"prepareLog")) (Val #l)) (Val #fp))
  {{ (tp : Loc), RET #tp;
      (⌜e.kind = kNoop ∧ tp = null⌝) ∨
      (⌜e.kind = kCommand ∨ e.kind = kConfig ∨ e.kind = kBarrier⌝ ∗ tp ↦ commitTuple.mk l fp) }}

end spec

end Perennial
