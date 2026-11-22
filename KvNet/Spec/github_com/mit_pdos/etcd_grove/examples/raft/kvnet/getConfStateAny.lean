/-
`getConfState(b)` (`examples/raft/kvnet/wire.go`) on any bytes (`getConfState.specAny`, for a decoder of
bytes from the network: kvcheck's `GetStatus`): if `ok`, a fresh conf state, owned, its `AutoLeave` set,
holding some `c`, and the rest of `b` holding some bytes at `b`'s fraction; if not, the rest is nil.
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
abbrev getConfState.specAny : Prop :=
  ∀ (b : GoSlice) (dq : DFrac) (bs : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet ∗
      b ↦*{dq} bs }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvnet.getConfState)) (Val #b))
  {{ (p : Loc) (rest : GoSlice) (ok : Bool), RET (PairV (PairV #p #rest) #ok);
      if ok then ∃ (c : ConfStateM) (r : List w8), csPts p (DFrac.own 1) c true ∗ rest ↦*{dq} r
      else ⌜rest = slice.nil⌝ }}

end spec

end raft_kvnet
end EtcdGrove
end Perennial
