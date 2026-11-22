/-
`putConfState(buf, cs)` (`examples/raft/kvnet/wire.go`, the client protocol's configuration):
`buf` with the conf state at `p` appended (`encConf`, `Codec.lean`: the voters, learners, outgoing
voters and next learners, each as `putIDs` writes them, then auto-leave), the conf state (`nil`,
read as the zero one, or owned at `dq`: `csOpt`) only read.
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Base
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Codec
public import KvNet.Proof.go_etcd_io.raft.v3.InvPb

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]

/-- See the file header. -/
abbrev putConfState.spec : Prop :=
  ∀ (buf : GoSlice) (B : List w8) (p : Loc) (dq : DFrac) (c : ConfStateM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet ∗
      buf ↦* B ∗ ownSliceCap w8 buf (DFrac.own 1) ∗ csOpt p dq c }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvnet.putConfState)) (Val #buf)) (Val #p))
  {{ (s : GoSlice), RET #s; s ↦* (B ++ encConf c) ∗ ownSliceCap w8 s (DFrac.own 1) ∗
      csOpt p dq c }}

end spec

end raft_kvnet
end EtcdGrove
end Perennial
