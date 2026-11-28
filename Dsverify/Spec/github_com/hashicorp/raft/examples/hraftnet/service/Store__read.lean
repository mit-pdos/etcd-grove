/-
`service.Store.read`'s spec (the hraft kit's state machine, notes/dsv-hraft.md, S6).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.service.FsmDefs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.service.Assumptions]

open github_com.hashicorp.raft.examples.hraftnet.service github_com.hashicorp.raft
  github_com.hashicorp.raft.proto github_com.hashicorp.raft.gprot

/-- `s.read()` (S6, a read of the FSM's state outside the log): the register after a committed prefix
`es` the frontier has passed, ending with a command, at least as long as an index the store had applied
(`k0`, or `0`). -/
abbrev github_com.hashicorp.raft.examples.hraftnet.service.Store.read.spec : Prop :=
  ∀ (γ : GNames) (fc : FCtx GF) (alb : GName) (i : SID) (s : Loc) (k0 : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.service ∗
      isStore γ fc alb i s ∗ (⌜k0 = 0⌝ ∨ appliedLb alb k0) }}
    (App (Val (s @!! go.GoType.PointerType Store.ty @!! go!"read")) (Val #()))
  {{ (res : result), RET #res; ∃ es : RLog, frLb fc es ∗
      ⌜lastCmd es ∧ k0 ≤ es.length ∧ res = result.mk (regOf es).isSome ((regOf es).getD [])⌝ }}

end spec

end Perennial
