/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__requestConfigChange.lean (241f27e).
-/
/-
`raft.Raft.requestConfigChange`'s spec (stage 4 interface).
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

/-- `(*Raft).requestConfigChange(req, timeout)` (stage 4), for a request in scope (`cfgReqOk`): a fresh
`*configurationChangeFuture` sent on `configurationChangeCh` (`ccfP`; the client keeps the waiting side,
`futWait`), or `errorFuture{ErrEnqueueTimeout}` after the timeout (`errorFuture{ErrRaftShutdown}`
never: `shutdownCh` is never closed). The main loop answers it: a follower or candidate with
`ErrNotLeader`, the leader through `appendConfigurationEntry`. -/
abbrev github_com.hashicorp.raft.Raft.requestConfigChange.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (rq : configurationChangeRequest)
    (tmo : time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i ∗ ⌜cfgReqOk γ rq⌝ }}
    (App (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"requestConfigChange")) (Val #rq))
      (Val #tmo))
  {{ (fi : GoInterface), RET #fi; futWait fi cfgChangeQ }}

end spec

end Perennial
