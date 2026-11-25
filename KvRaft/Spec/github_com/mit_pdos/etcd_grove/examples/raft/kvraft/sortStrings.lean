-- The copy for the part `KvRaft/` of `RaftNoAx/Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvdurablenoax/sortStrings.lean` (etc/copy-part.py; rerun it, do not edit).
/- Lean-first (no Rocq counterpart). kvreconf's spec (the same Go text), ported.

`sortStrings(ks)` (kv.go, D22 S-r): `ks`, sorted in place by `less` (an insertion sort); stated
as a permutation of its elements (see `less.spec`).
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
abbrev sortStrings.spec : Prop :=
  ∀ (ks : GoSlice) (xs : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft ∗ ks ↦* xs }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvraft.sortStrings)) (Val #ks))
  {{ RET #(); ∃ ys : List GoString, ks ↦* ys ∗ ⌜ys.Perm xs⌝ }}

end spec

end kvraft
end EtcdGrove
end Perennial
