/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Base.lean (241f27e).
The package fact of hashicorp/raft's package (the hraft kit, notes/dsv-hraft.md), proved by the
generated `Init.lean` (`etc/dsv/hraft.py`'s `special`: the lab's `initialize.lean`).
-/
/-
Shared definitions of the proofs of the `raft` package: its `isPkgInit`. (Only the package
initialization is established here; the protocol ghost state and invariant live under
`raft/gprot/`, the raft-internal shared predicates under `raft/core/`.)

`isPkgInit` (`pkgGlobals`, raft-iface R1): the package's global variables as initialized —
the error variables made by `errors.New` (each holds a fixed `*errorString`, pairwise distinct:
`errVals`), the three stable-store keys (read-only byte slices), and `nextObserverID`'s atomic
counter (an invariant). `isRaftErr c err`: `err` is the value of the error variable of code `c`.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.GooseLang.Lifting
public import Perennial.Proof.errors.Base
public import Perennial.Proof.errors.NewVar
public import Perennial.Proof.fmt.Base
public import Perennial.Proof.io.Base
public import Perennial.Proof.strconv.Base
public import Perennial.Proof.sync.Base
public import Perennial.Proof.sync.atomic.Base
public import Perennial.Proof.time.Base
public import Perennial.Proof.bytes.Base
public import Perennial.Proof.context.Base
public import Perennial.Proof.strings.Base
public import Perennial.Proof.github_com.goose_lang.primitive.Base
public import Dsverify.Code.github_com.hashicorp.raft
public import Dsverify.GeneratedProof.github_com.hashicorp.raft

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace github_com.hashicorp.raft

/-- The package's error variables (all made by `errors.New`). -/
inductive RaftErr where
  | leader | notLeader | notVoter | leadershipLost | abortedByRestore | raftShutdown
  | enqueueTimeout | nothingNewToSnapshot | unsupportedProtocol | cantBootstrap
  | leadershipTransferInProgress | incompatibleLogStore | shortBuffer | transportShutdown
  | pipelineShutdown | logNotFound | pipelineReplicationNotSupported
  deriving DecidableEq

/-- Every error code. -/
def RaftErr.all : List RaftErr :=
  [.leader, .notLeader, .notVoter, .leadershipLost, .abortedByRestore, .raftShutdown,
   .enqueueTimeout, .nothingNewToSnapshot, .unsupportedProtocol, .cantBootstrap,
   .leadershipTransferInProgress, .incompatibleLogStore, .shortBuffer, .transportShutdown,
   .pipelineShutdown, .logNotFound, .pipelineReplicationNotSupported]

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The global variable of an error code. -/
def RaftErr.var : RaftErr → GoString
  | .leader => ErrLeader
  | .notLeader => ErrNotLeader
  | .notVoter => ErrNotVoter
  | .leadershipLost => ErrLeadershipLost
  | .abortedByRestore => ErrAbortedByRestore
  | .raftShutdown => ErrRaftShutdown
  | .enqueueTimeout => ErrEnqueueTimeout
  | .nothingNewToSnapshot => ErrNothingNewToSnapshot
  | .unsupportedProtocol => ErrUnsupportedProtocol
  | .cantBootstrap => ErrCantBootstrap
  | .leadershipTransferInProgress => ErrLeadershipTransferInProgress
  | .incompatibleLogStore => ErrIncompatibleLogStore
  | .shortBuffer => errShortBuffer
  | .transportShutdown => ErrTransportShutdown
  | .pipelineShutdown => ErrPipelineShutdown
  | .logNotFound => ErrLogNotFound
  | .pipelineReplicationNotSupported => ErrPipelineReplicationNotSupported

/-- The message of an error code (`errors.New`'s argument). -/
def RaftErr.msg : RaftErr → GoString
  | .leader => go!"node is the leader"
  | .notLeader => go!"node is not the leader"
  | .notVoter => go!"node is not a voter"
  | .leadershipLost => go!"leadership lost while committing log"
  | .abortedByRestore => go!"snapshot restored while committing log"
  | .raftShutdown => go!"raft is already shutdown"
  | .enqueueTimeout => go!"timed out enqueuing operation"
  | .nothingNewToSnapshot => go!"nothing new to snapshot"
  | .unsupportedProtocol => go!"operation not supported with current protocol version"
  | .cantBootstrap => go!"bootstrap only works on new clusters"
  | .leadershipTransferInProgress => go!"leadership transfer in progress"
  | .incompatibleLogStore =>
      go!"log store does not implement some required methods or malformed"
  | .shortBuffer => go!"encoding: short buffer"
  | .transportShutdown => go!"transport shutdown"
  | .pipelineShutdown => go!"append pipeline closed"
  | .logNotFound => go!"log not found"
  | .pipelineReplicationNotSupported => go!"pipeline replication not supported"

/-- The error variables hold the values `f` (pairwise distinct `*errorString`s, never written
again). -/
def errVals (f : RaftErr → GoInterface) : IProp GF :=
  iprop(⌜Function.Injective f⌝ ∗
    [∗list] c ∈ RaftErr.all, globalAddr c.var ↦□ f c ∗ errors.newVar c.var c.msg)

instance errVals_persistent f : Persistent (errVals (GF := GF) f) := by
  unfold errVals; infer_instance

/-- `err` is the value of the error variable of code `c`. -/
def isRaftErr (c : RaftErr) (err : GoInterface) : IProp GF :=
  iprop(∃ f : RaftErr → GoInterface, errVals f ∗ ⌜f c = err⌝)

instance isRaftErr_persistent c err : Persistent (isRaftErr (GF := GF) c err) := by
  unfold isRaftErr; infer_instance

/-- The namespace of `nextObserverID`'s invariant. -/
def nextObserverIDN : Namespace := (nroot.@"raft").@"nextObserverID"

/-- The package's initialized globals (persistent). -/
def pkgGlobals : IProp GF :=
  iprop((∃ f : RaftErr → GoInterface, errVals f) ∗
    (∃ s : GoSlice, globalAddr keyCurrentTerm ↦□ s ∗ s ↦*□ (go!"CurrentTerm" : List w8)) ∗
    (∃ s : GoSlice, globalAddr keyLastVoteTerm ↦□ s ∗ s ↦*□ (go!"LastVoteTerm" : List w8)) ∗
    (∃ s : GoSlice, globalAddr keyLastVoteCand ↦□ s ∗ s ↦*□ (go!"LastVoteCand" : List w8)) ∗
    inv nextObserverIDN (∃ n : w64, globalAddr nextObserverID ↦ n))

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.hashicorp.raft :=
  define_is_pkg_init pkgGlobals
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.hashicorp.raft :=
  build_get_is_pkg_init_wf

end init

end github_com.hashicorp.raft

end Perennial
end
