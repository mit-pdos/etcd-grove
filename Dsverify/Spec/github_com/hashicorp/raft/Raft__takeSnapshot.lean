/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__takeSnapshot.lean (241f27e).
-/
/-
`raft.(*Raft).takeSnapshot`'s spec (stage 3, raft-internal: the snapshot goroutine; crosses the FSM goroutine, the main loop and the snapshot store).
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

/-- `(*Raft).takeSnapshot()`, on the snapshot goroutine: asks the FSM goroutine for a snapshot
(`fsmSnapshotCh`, answered at its position `x ≥ 1` with an `FSMSnapshot`), the main loop for the
configurations (`configurationsCh`, answered with `durLb γ i x`, `applLb rc x` and `compLb rc x`), creates a sink in
the snapshot store, has the FSMSnapshot persist into it, closes it (the snapshot `(x, tx)` becomes the
latest unless an install's is newer: `snapCell`), sets the last snapshot (`lastLockInv`) and compacts
the log up to `x` (`compactLogs`); returns the sink's id and nil. Or `ErrNothingNewToSnapshot` (the
FSM applied nothing yet) or `ErrLeadershipTransferInProgress` (the leader loop refused the
configurations), or (stage 4) an `errors.New` leaf error (`fmt.Errorf("cannot take snapshot now, wait
until the configuration entry at %v has been applied (have applied %v)", …)`, whose Perennial model
is `errors.New(format)`, `fmt.wp_Errorf_snapCfgErr`: the committed configuration's index is above `x`,
reachable while the FSM goroutine lags behind `lastApplied`; review T1-5: a `*errorString`, so
`runSnapshots`' `errors.Is(err, ErrNothingNewToSnapshot)` is a leaf comparison, `errors.wp_Is_leaf`;
interface stage 4 before the review: `errOk err`). The other
`fmt.Errorf` branches of the Go code are refuted: the stores and the FSM never fail (their contracts)
(stage 3: also the committed index's, `x ≥ 1 = committedIndex`). The snapshot's configuration is the
committed log's at `x` (`snapCfg`, from `cfgReqQ`). -/
abbrev github_com.hashicorp.raft.Raft.takeSnapshot.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (tid : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i ∗ rtok tid }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"takeSnapshot")) (Val #()))
  {{ (id : GoString) (err : GoInterface), RET (PairV #id #err); rtok tid ∗
      (⌜err = interface.nil⌝ ∨ isRaftErr .nothingNewToSnapshot err ∨
        isRaftErr .leadershipTransferInProgress err ∨
        ⌜∃ x : Loc, err = interface.mkOk (go.GoType.PointerType errors.errorString.ty) #x⌝) }}

end spec

end Perennial
