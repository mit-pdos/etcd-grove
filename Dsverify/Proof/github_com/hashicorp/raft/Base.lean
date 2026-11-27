/-
The package fact of hashicorp/raft's package (the hraft kit, notes/dsv-hraft.md): its `errors.New` variables (`errors.newVar`). The stable-store keys and
`nextObserverID` are not in it yet (stage S0, the translation only; the port of the lab's proof, S2,
gives it the lab's `pkgGlobals`).
-/
module

public import Dsverify.GeneratedProof.github_com.hashicorp.raft
public import Perennial.Proof.errors.Base
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

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace github_com.hashicorp.raft

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.hashicorp.raft :=
  define_is_pkg_init iprop(errors.newVar ErrLeader go!"node is the leader" ∗
    errors.newVar ErrNotLeader go!"node is not the leader" ∗
    errors.newVar ErrNotVoter go!"node is not a voter" ∗
    errors.newVar ErrLeadershipLost go!"leadership lost while committing log" ∗
    errors.newVar ErrAbortedByRestore go!"snapshot restored while committing log" ∗
    errors.newVar ErrRaftShutdown go!"raft is already shutdown" ∗
    errors.newVar ErrEnqueueTimeout go!"timed out enqueuing operation" ∗
    errors.newVar ErrNothingNewToSnapshot go!"nothing new to snapshot" ∗
    errors.newVar ErrUnsupportedProtocol go!"operation not supported with current protocol version" ∗
    errors.newVar ErrCantBootstrap go!"bootstrap only works on new clusters" ∗
    errors.newVar ErrLeadershipTransferInProgress go!"leadership transfer in progress" ∗
    errors.newVar ErrIncompatibleLogStore go!"log store does not implement some required methods or malformed" ∗
    errors.newVar ErrTransportShutdown go!"transport shutdown" ∗
    errors.newVar ErrPipelineShutdown go!"append pipeline closed" ∗
    errors.newVar ErrLogNotFound go!"log not found" ∗
    errors.newVar ErrPipelineReplicationNotSupported go!"pipeline replication not supported" ∗
    errors.newVar errShortBuffer go!"encoding: short buffer")
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.github_com.hashicorp.raft :=
  build_get_is_pkg_init_wf

end def_

end github_com.hashicorp.raft
end Perennial
