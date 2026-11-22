-- The copy for the part `KvNet/` of `RaftNoAx/Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvdurablenoax/sortStrings.lean` (etc/copy-part.py; rerun it, do not edit).
/- Lean-first (no Rocq counterpart). kvreconf's spec (the same Go text), ported.

`sortStrings(ks)` (kv.go, D22 S-r): `ks`, sorted in place by `less` (an insertion sort); stated
as a permutation of its elements (see `less.spec`).
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
abbrev sortStrings.spec : Prop :=
  ∀ (ks : GoSlice) (xs : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet ∗ ks ↦* xs }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvnet.sortStrings)) (Val #ks))
  {{ RET #(); ∃ ys : List GoString, ks ↦* ys ∗ ⌜ys.Perm xs⌝ }}

end spec

end raft_kvnet
end EtcdGrove
end Perennial
