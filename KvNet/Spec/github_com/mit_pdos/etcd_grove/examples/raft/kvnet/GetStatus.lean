/-
`GetStatus(b)` (`examples/raft/kvnet/client.go`) on any bytes (a replica's answer to a status request,
on which the protocol puts no obligation): with `good`, the status's `Conf` is a fresh conf state, owned,
its `AutoLeave` set (what kvcheck's `checker.conf` keeps). Nothing is said of the other fields (no caller
reads them in a proof).
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
abbrev GetStatus.spec : Prop :=
  ∀ (b : GoSlice) (dq : DFrac) (bs : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet ∗
      b ↦*{dq} bs }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvnet.GetStatus)) (Val #b))
  {{ (s : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Status) (good : Bool),
      RET (PairV #s #good);
      if good then ∃ c : ConfStateM, csPts s.Conf' (DFrac.own 1) c true else True }}

end spec

end raft_kvnet
end EtcdGrove
end Perennial
