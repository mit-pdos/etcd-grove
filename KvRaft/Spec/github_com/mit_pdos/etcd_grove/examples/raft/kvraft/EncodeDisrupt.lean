/-
`EncodeDisrupt(what, to)` (`examples/raft/kvraft/client.go`): `ReqDisrupt`'s payload, a fresh slice
holding `what` and `to` (8 bytes each, little-endian), with its capacity.
-/
module

public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Base
public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Codec

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Iris Iris.BI Net

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]

/-- See the file header. -/
abbrev EncodeDisrupt.spec : Prop :=
  ∀ (what to : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvraft.EncodeDisrupt)) (Val #what))
      (Val #to))
  {{ (s : GoSlice), RET #s; s ↦* (u64Le what ++ u64Le to) ∗ ownSliceCap w8 s (DFrac.own 1) }}

end spec

end kvraft
end EtcdGrove
end Perennial
