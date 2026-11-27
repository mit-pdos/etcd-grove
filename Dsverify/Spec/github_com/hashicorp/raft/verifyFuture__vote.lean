/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/verifyFuture__vote.lean (241f27e).
-/
/-
`raft.verifyFuture.vote`'s spec (replication subsystem, internal; stage 2).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.ReplBase

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

/-- `(*verifyFuture).vote(leader)` (stage 2), by a replication goroutine of the leader `i` for
voter `j` (`heartbeat`, `notifyAll`): the future `v` was registered by the leader `i` of `T` at
the snapshot `sv` (stage 4: with the leader's log `L` then), its notify channel being `verifyCh`
(`vch`). A `true` vote spends `j`'s vote token for `v` and carries `j`'s witness of being in `T`
after `sv` and (stage 4, fix `6c3454c`) that `j` is a voter of `L`'s latest configuration; a `false`
vote needs nothing.
Under the vote lock: if `v` was already notified, nothing; otherwise the vote is counted (`true`)
and, at a quorum or on a `false` vote, `v` goes back to the leader loop on `verifyCh`
(`verifyVoted`). -/
abbrev github_com.hashicorp.raft.verifyFuture.vote.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (T : Nat) (sv : Snap) (L : RLog) (vch : Loc)
    (j : SID) (v : Loc) (b : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i ∗
     r.[Raft, go!"verifyCh"] ↦□ vch ∗ verifyReg γ rc i T sv L vch v ∗ isSrv γ j ∗
     (⌜b = false⌝ ∨ voteTok rc v j ∗ respWit γ j T sv ∗ ⌜j ∈ cfgOfC γ.cv L⌝) }}
    (App (Val (v @!! go.GoType.PointerType verifyFuture.ty @!! go!"vote")) (Val #b))
  {{ RET #(); True }}

end spec

end Perennial
