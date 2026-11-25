/- Lean-first (no Rocq counterpart).

`getUint64(b)` (`examples/raft/kvraft/storage.go`) on any bytes `bs` (`getUint64.spec` takes at least
eight): `ok` with the word `x` of the first eight bytes and the rest (`getUint64.spec`'s post), or not
`ok` when `bs` is shorter than eight bytes (the rest then the nil slice) (for a decoder of untrusted bytes: `GetConfChange`).
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
abbrev getUint64.specAny : Prop :=
  ∀ (b : GoSlice) (dq : DFrac) (bs : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft ∗ b ↦*{dq} bs }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvraft.getUint64)) (Val #b))
  {{ (x : w64) (rest : GoSlice) (ok : Bool), RET (PairV (PairV #x #rest) #ok);
      if ok then ⌜bs = u64Le x ++ bs.drop 8⌝ ∗ rest ↦*{dq} bs.drop 8 ∗
        (rest ↦*{dq} bs.drop 8 -∗ b ↦*{dq} bs)
      else ⌜bs.length < 8 ∧ rest = slice.nil⌝ ∗ b ↦*{dq} bs }}

end spec

end kvraft
end EtcdGrove
end Perennial
