/- Lean-first (no Rocq counterpart).

`sortStrings(ks)` (kv.go, D22 S-r): `ks`, sorted in place by `less` (an insertion sort); stated
as a permutation of its elements (see `less.spec`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kv

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]

/-- See the file header. -/
abbrev sortStrings.spec : Prop :=
  ∀ (ks : GoSlice) (xs : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kv ∗ ks ↦* xs }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.kv.sortStrings)) (Val #ks))
  {{ RET #(); ∃ ys : List GoString, ks ↦* ys ∗ ⌜ys.Perm xs⌝ }}

end spec

end kv
end EtcdGrove
end Perennial
