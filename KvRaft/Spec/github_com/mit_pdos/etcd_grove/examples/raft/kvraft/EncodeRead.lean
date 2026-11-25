/-
`EncodeRead(seq, key)` (`examples/raft/kvraft/client.go`): `ReqRead`'s payload, a fresh slice
holding the sequence number (8 bytes, little-endian) and the key (`putB`), with its capacity.
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
abbrev EncodeRead.spec : Prop :=
  ∀ (seq : w64) (key : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvraft.EncodeRead)) (Val #seq))
      (Val #key))
  {{ (s : GoSlice), RET #s; s ↦* (u64Le seq ++ putB key) ∗ ownSliceCap w8 s (DFrac.own 1) }}

end spec

end kvraft
end EtcdGrove
end Perennial
