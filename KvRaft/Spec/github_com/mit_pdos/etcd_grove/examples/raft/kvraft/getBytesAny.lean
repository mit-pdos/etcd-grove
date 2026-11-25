/-
`getBytes(b)` (codec.go) on any bytes `bs` (`getBytes.specAny`, for a decoder of bytes from the network:
kvcheck's `GetStatus`): if `ok`, the bytes are `putB x ++ r` and `v`, `rest` hold `x` and `r` (given
back as `getBytes.spec`'s); if not, `b`'s bytes are given back.
-/
module

public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Base
public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Codec

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
abbrev getBytes.specAny : Prop :=
  ∀ (b : GoSlice) (dq : DFrac) (bs : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft ∗ b ↦*{dq} bs }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvraft.getBytes)) (Val #b))
  {{ (v rest : GoSlice) (ok : Bool), RET (PairV (PairV #v #rest) #ok);
      if ok then ∃ x r : List w8, ⌜bs = putB x ++ r⌝ ∗ v ↦*{dq} x ∗ rest ↦*{dq} r ∗
        (v ↦*{dq} x -∗ rest ↦*{dq} r -∗ b ↦*{dq} bs)
      else b ↦*{dq} bs }}

end spec

end kvraft
end EtcdGrove
end Perennial
