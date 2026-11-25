-- The copy for the part `KvRaft/` of `RaftNoAx/Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvdurablenoax/getUint64.lean` (etc/copy-part.py; rerun it, do not edit).
/- Lean-first (no Rocq counterpart).

`getUint64(b)` (storage.go): what `putUint64` wrote at the start of `b` (`u64Le x`), the rest
(a slice of `b`, which gives it back) and `ok`. Stated of bytes `putUint64` wrote (what
`openStorage` reads), so `ok` is `true`.
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
abbrev getUint64.spec : Prop :=
  ∀ (b : GoSlice) (dq : DFrac) (x : w64) (r : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft ∗ b ↦*{dq} (u64Le x ++ r) }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvraft.getUint64)) (Val #b))
  {{ (rest : GoSlice), RET (PairV (PairV #x #rest) #true);
      rest ↦*{dq} r ∗ (rest ↦*{dq} r -∗ b ↦*{dq} (u64Le x ++ r)) }}

end spec

end kvraft
end EtcdGrove
end Perennial
