/-
`getMap(b)` (codec.go) on any bytes `bs` (`getMap.specAny`, for a decoder of bytes from the network:
kvcheck's `GetStatus`): if `ok`, a map and the rest of the bytes (given back as `getMap.spec`'s); if not,
nothing (the caller drops the bytes).
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Base
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Codec

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
abbrev getMap.specAny : Prop :=
  ∀ (b : GoSlice) (dq : DFrac) (bs : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet ∗ b ↦*{dq} bs }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvnet.getMap)) (Val #b))
  {{ (mK : Loc) (rest : GoSlice) (ok : Bool), RET (PairV (PairV #mK #rest) #ok);
      if ok then ∃ (K : GMap GoString GoString) (r : List w8), mK ↦$ K ∗ rest ↦*{dq} r ∗
        (rest ↦*{dq} r -∗ b ↦*{dq} bs)
      else True }}

end spec

end raft_kvnet
end EtcdGrove
end Perennial
