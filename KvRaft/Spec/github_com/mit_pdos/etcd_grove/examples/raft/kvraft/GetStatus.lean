/-
`GetStatus(b)` (`examples/raft/kvraft/client.go`) on any bytes (a replica's answer to a status request,
on which the protocol puts no obligation): with `good`, the status's `Conf` is a fresh conf state, owned,
its `AutoLeave` set (what kvcheck's `checker.conf` keeps). Nothing is said of the other fields (no caller
reads them in a proof).
-/
module

public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Base
public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Codec
public import KvRaft.Proof.go_etcd_io.raft.v3.InvPb

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]

/-- See the file header. -/
abbrev GetStatus.spec : Prop :=
  ∀ (b : GoSlice) (dq : DFrac) (bs : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft ∗
      b ↦*{dq} bs }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvraft.GetStatus)) (Val #b))
  {{ (s : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Status) (good : Bool),
      RET (PairV #s #good);
      if good then ∃ c : ConfStateM, csPts s.Conf' (DFrac.own 1) c true else True }}

end spec

end kvraft
end EtcdGrove
end Perennial
