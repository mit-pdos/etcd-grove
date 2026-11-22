/-
`putMsg(buf, m)` (`examples/raft/kvnet/wire.go`): `buf` with the message at `l` appended
(`encMsg`, `Wire.lean`: its scalars, reject, reject hint, context, entries, then its snapshot or
none), the message only read and given back as it was (`msgPtsC`, at any fractions, with or
without its entries' capacity). Its responses are not written.
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Base
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Wire
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
abbrev putMsg.spec : Prop :=
  ∀ (buf : GoSlice) (B : List w8) (l : Loc) (dq dqe : DFrac) (cap : Bool) (st : MsgSt),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet ∗
      buf ↦* B ∗ ownSliceCap w8 buf (DFrac.own 1) ∗ msgPtsC l dq dqe cap st }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvnet.putMsg)) (Val #buf)) (Val #l))
  {{ (s : GoSlice), RET #s; s ↦* (B ++ encMsg st) ∗ ownSliceCap w8 s (DFrac.own 1) ∗
      msgPtsC l dq dqe cap st }}

end spec

end raft_kvnet
end EtcdGrove
end Perennial
