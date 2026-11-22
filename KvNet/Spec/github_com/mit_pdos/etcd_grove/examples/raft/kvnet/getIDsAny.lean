/-
`getIDs(b)` (storage.go) on any bytes `bs` (`getIDs.specAny`, for a decoder of bytes from the network:
kvcheck's `GetStatus`): if `ok`, the bytes are `encIDs xs ++ r`, read into a fresh slice holding `xs`, and
`rest` holds `r` (with the wand back to `b`, as `getIDs.spec`'s); if not, `rest` is nil and `b`'s bytes
are given back.
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
abbrev getIDs.specAny : Prop :=
  ∀ (b : GoSlice) (dq : DFrac) (bs : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet ∗ b ↦*{dq} bs }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvnet.getIDs)) (Val #b))
  {{ (ids rest : GoSlice) (ok : Bool), RET (PairV (PairV #ids #rest) #ok);
      if ok then ∃ (xs : List w64) (r : List w8), ⌜bs = encIDs xs ++ r⌝ ∗ ids ↦* xs ∗
        rest ↦*{dq} r ∗ (rest ↦*{dq} r -∗ b ↦*{dq} bs)
      else ⌜rest = slice.nil⌝ ∗ b ↦*{dq} bs }}

end spec

end raft_kvnet
end EtcdGrove
end Perennial
