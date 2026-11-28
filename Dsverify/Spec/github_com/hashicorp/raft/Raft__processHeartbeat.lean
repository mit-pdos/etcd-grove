/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__processHeartbeat.lean (241f27e).
-/
/-
`raft.(*Raft).processHeartbeat`'s spec (raft-internal: `NewRaft` registers it with the transport's
`SetHeartbeatHandler`; this triple is what gives `hbHandler γ i` for the method value). Runs on any
goroutine (the transport's), concurrently with the main loop: it changes no protocol state (fix
`ae71703`), only reads the term and state cells and `lastLock`, sets the leader and the last
contact, and sends one response.
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

/-- `(*Raft).processHeartbeat`: given a heartbeat `RPC` for `i` (`hbRpcP`) and the calling
thread's quarter token, it answers it (success only in `i`'s current term while `i` follows, with
the term witness) and returns the token. -/
abbrev github_com.hashicorp.raft.Raft.processHeartbeat.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (rpc : RPC) (tid : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i ∗
      hbRpcP γ i rpc ∗ rtok tid }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"processHeartbeat")) (Val #rpc))
  {{ RET #(); rtok tid }}

end spec

end Perennial
