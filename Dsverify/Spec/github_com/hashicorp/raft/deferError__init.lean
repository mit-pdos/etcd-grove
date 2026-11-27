/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/deferError__init.lean (241f27e).
-/
/-
`raft.(*deferError).init`'s spec (raft-internal interface, notes/raft-iface.md). Called through `*logFuture` (promoted). Makes the answer channel for an answer predicate `Q` chosen by the caller: the responder's and the client's sides (`deferResp`/`deferWait` given the other fields).
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

/-- `(*deferError).init`: Called through `*logFuture` (promoted). Makes the answer channel for an answer predicate `Q` chosen by the caller: the responder's and the client's sides (`deferResp`/`deferWait` given the other fields). -/
abbrev github_com.hashicorp.raft.deferError.init.spec : Prop :=
  ∀ (f : Loc) (Q : GoInterface → IProp GF) (ch0 : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ (f.[logFuture, go!"deferError"]).[deferError, go!"errCh"] ↦ ch0 }}
    (App (Val (f @!! go.GoType.PointerType logFuture.ty @!! go!"init")) (Val #()))
  {{ RET #(); ∃ (ch : Loc) (γe : SpscNames), ⌜ch ≠ chan.nil⌝ ∗
      (f.[logFuture, go!"deferError"]).[deferError, go!"errCh"] ↦ ch ∗
      isSpsc (V := GoInterface) γe ch (fun n v => iprop(⌜n = 0⌝ ∗ Q v)) (fun sent => iprop(⌜sent ≠ []⌝)) ∗
      spscProducer γe ([] : List GoInterface) ∗ spscConsumer γe ([] : List GoInterface) }}

end spec

end Perennial
