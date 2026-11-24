/-
`EncodeDisrupt(what, to)` (`examples/raft/kvnet/client.go`): `ReqDisrupt`'s payload, a fresh slice
holding `what` and `to` (8 bytes each, little-endian), with its capacity.
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Base
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Codec

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Net

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]

/-- See the file header. -/
abbrev EncodeDisrupt.spec : Prop :=
  ∀ (what to : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvnet.EncodeDisrupt)) (Val #what))
      (Val #to))
  {{ (s : GoSlice), RET #s; s ↦* (u64Le what ++ u64Le to) ∗ ownSliceCap w8 s (DFrac.own 1) }}

end spec

end raft_kvnet
end EtcdGrove
end Perennial
