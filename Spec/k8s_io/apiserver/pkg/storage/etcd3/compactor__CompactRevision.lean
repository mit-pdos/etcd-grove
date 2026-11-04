/-
`(*compactor).CompactRevision()` (`compact.go`): the latest compaction revision the compactor has
observed (K2 of `notes/k8s-compactor-plan.md`). Lean-first (no Rocq counterpart).

A revision some compactor recorded in `compact_rev_key` and the cluster reached, or `0`; not one
etcd has necessarily compacted (`nonissues/k8s-apiserver-compactrevision-ahead-of-etcd.md`).
Monotone: at least every earlier answer (`compactRevLb`).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.CompactorDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [sync_sem : sync.Assumptions]

/-- See the file header. -/
abbrev compactor.CompactRevision.spec : Prop :=
  ∀ (c cl : Loc) (γk : KVNames) (recorded : w64 → IProp GF) (γc : CompactorNames) (r0 : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗
      isCompactor c cl γk recorded γc ∗ compactRevLb γc r0 }}
    (App (Val (c @!! go.GoType.PointerType k8s_io.apiserver.pkg.storage.etcd3.compactor.ty @!!
      go!"CompactRevision")) (Val #()))
  {{ (r : w64), RET #r; recRevOk γk recorded r ∗ compactRevLb γc r ∗
      ⌜(sint.Z r0).toNat ≤ (sint.Z r).toNat⌝ }}

end spec

end k8s
end EtcdGrove
end Perennial
