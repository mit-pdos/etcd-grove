/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/NewObserver.lean (241f27e).
-/
/-
`raft.NewObserver`'s spec (raft-internal interface, notes/raft-iface.md). An observer with no channel, not blocking, whose filter meets `filterOk` (for the server `i` at `r` it will be registered with).
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

/-- `NewObserver`: An observer with no channel, not blocking, whose filter meets `filterOk` (for the server `i` at `r` it will be registered with). -/
abbrev github_com.hashicorp.raft.NewObserver.spec : Prop :=
  ∀ (γ : GNames) (i : SID) (r : Loc) (fl : GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ filterOk γ i r fl }}
    (App (App (App (Val (@! github_com.hashicorp.raft.NewObserver)) (Val #chan.nil)) (Val #false)) (Val #fl))
  {{ (o : Loc), RET #o; obsOk γ i r o }}

end spec

end Perennial
