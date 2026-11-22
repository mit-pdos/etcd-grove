/-
`EncodeRead(seq, key)` (`examples/raft/kvnet/client.go`): `ReqRead`'s payload, a fresh slice
holding the sequence number (8 bytes, little-endian) and the key (`putB`), with its capacity.
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
abbrev EncodeRead.spec : Prop :=
  ∀ (seq : w64) (key : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvnet.EncodeRead)) (Val #seq))
      (Val #key))
  {{ (s : GoSlice), RET #s; s ↦* (u64Le seq ++ putB key) ∗ ownSliceCap w8 s (DFrac.own 1) }}

end spec

end raft_kvnet
end EtcdGrove
end Perennial
