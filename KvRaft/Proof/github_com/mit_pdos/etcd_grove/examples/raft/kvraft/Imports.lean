/-
The part `KvRaft/`'s smoke test (notes/kvraft-part.md): one import closure holding kvraft's and
kvcheck's translations together with raft-noax's node API (`Api`, `RestartNode`), the net
extension's `net.Listen` and the bodied `durable`'s `Write` over fsExt, which no other tree can
hold at once (each declares main-tree names). `etc/copy-part.py` takes the part's own modules as
its roots: what they import is what the part copies.
-/
module

public import KvRaft.GeneratedProof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft
public import KvRaft.GeneratedProof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck
public import KvRaft.Spec.go_etcd_io.raft.v3.Api
public import KvRaft.Spec.go_etcd_io.raft.v3.RestartNode
public import KvRaft.Spec.net.Listen
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.lib.durable.Write
-- what kvraft's glue proofs (wire.go, addrs.go, timeout.go) stand on: `net.Conn`'s calls, raft's
-- message predicates and getters
public import KvRaft.Spec.net.Conn__Read
public import KvRaft.Spec.net.Conn__Write
public import KvRaft.Spec.net.Conn__Close
public import KvRaft.Proof.go_etcd_io.raft.v3.InvPb
public import KvRaft.Spec.go_etcd_io.raft.v3.raftpb.Message__GetType
public import KvRaft.Spec.go_etcd_io.raft.v3.raftpb.Message__GetTo
public import KvRaft.Spec.go_etcd_io.raft.v3.raftpb.Message__GetFrom
public import KvRaft.Spec.go_etcd_io.raft.v3.raftpb.Message__GetTerm
public import KvRaft.Spec.go_etcd_io.raft.v3.raftpb.Message__GetLogTerm
public import KvRaft.Spec.go_etcd_io.raft.v3.raftpb.Message__GetIndex
public import KvRaft.Spec.go_etcd_io.raft.v3.raftpb.Message__GetCommit
public import KvRaft.Spec.go_etcd_io.raft.v3.raftpb.Message__GetVote
public import KvRaft.Spec.go_etcd_io.raft.v3.raftpb.Message__GetReject
public import KvRaft.Spec.go_etcd_io.raft.v3.raftpb.Message__GetRejectHint
public import KvRaft.Spec.go_etcd_io.raft.v3.raftpb.Message__GetContext
public import KvRaft.Spec.go_etcd_io.raft.v3.raftpb.Message__GetEntries
public import KvRaft.Spec.go_etcd_io.raft.v3.raftpb.MessageType__Enum
public import KvRaft.Spec.go_etcd_io.raft.v3.raftpb.MessageType__String
public import KvRaft.Spec.go_etcd_io.raft.v3.raftpb.ConfState__GetVoters
public import KvRaft.Spec.go_etcd_io.raft.v3.raftpb.ConfState__GetLearners
public import KvRaft.Spec.go_etcd_io.raft.v3.raftpb.ConfState__GetVotersOutgoing
public import KvRaft.Spec.go_etcd_io.raft.v3.raftpb.ConfState__GetLearnersNext
public import KvRaft.Spec.go_etcd_io.raft.v3.raftpb.ConfState__GetAutoLeave
public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Base
public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Codec
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.putBytes
public import Perennial.Proof.context.Results
public import Perennial.Proof.time.Link
public import Perennial.Proof.sync.Link

@[expose] public section

namespace Perennial

#check @EtcdGrove.RestartNode.spec
#check @net.Listen.spec
#check @EtcdGrove.github_com.mit_pdos.etcd_grove.examples.lib.durable.Write.spec

end Perennial
