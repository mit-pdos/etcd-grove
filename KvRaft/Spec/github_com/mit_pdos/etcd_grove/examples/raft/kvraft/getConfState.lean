/-
`getConfState(b)` (`examples/raft/kvraft/wire.go`): what `putConfState` wrote at the start of `b`
(`encConf c`), read back: a fresh conf state holding `c`, owned, its `AutoLeave` set (`csPts … true`),
and the rest of `b`, at `b`'s fraction. Stated of bytes `putConfState` wrote.
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
abbrev getConfState.spec : Prop :=
  ∀ (b : GoSlice) (dq : DFrac) (c : ConfStateM) (r : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft ∗
      b ↦*{dq} (encConf c ++ r) }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvraft.getConfState)) (Val #b))
  {{ (p : Loc) (rest : GoSlice), RET (PairV (PairV #p #rest) #true);
      csPts p (DFrac.own 1) c true ∗ rest ↦*{dq} r }}

end spec

end kvraft
end EtcdGrove
end Perennial
