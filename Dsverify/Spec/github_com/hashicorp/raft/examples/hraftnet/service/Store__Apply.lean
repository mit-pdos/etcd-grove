/-
`service.Store.Apply`'s spec (the hraft kit's state machine, notes/dsv-hraft.md, S5).
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

/-- `s.Apply(l)`, the committed command `e` at index `k` (the next command after `k0`, the entries in
between no commands), applied by server `i`'s FSM goroutine: no panic; the register moves past `k`
(and the frontier, if it was at `k0`), and the response means `respP`. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.service.Store.Apply.spec : Prop :=
  ∀ (γ : GNames) (fc : FCtx GF) (alb : GName) (i : SID) (s l : Loc) (k0 k : Nat) (e : Entry),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.service ∗
      isStore γ fc alb i s ∗ fsmOwn alb k0 ∗ logPtr l k e ∗ ⌜k0 < k ∧ e.kind = kCommand⌝ ∗
      CIdx γ k e ∗ durLb γ i k ∗ noCmdBetween γ k0 k }}
    (App (Val (s @!! go.GoType.PointerType Store.ty @!! go!"Apply")) (Val #l))
  {{ (r : GoInterface), RET #r; fsmOwn alb k ∗ respP γ fc alb k r }}

end spec

end Perennial
