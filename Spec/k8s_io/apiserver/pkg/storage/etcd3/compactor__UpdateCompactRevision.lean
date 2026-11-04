/-
`(*compactor).UpdateCompactRevision(rev)` (`compact.go`): the compactor's revision raised to `rev`
if larger (`max`), a `0` ignored (K2 of `notes/k8s-compactor-plan.md`). Lean-first (no Rocq
counterpart). `rev` recorded and reached (or `0`): what the mutex's invariant keeps.
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
abbrev compactor.UpdateCompactRevision.spec : Prop :=
  ∀ (c cl : Loc) (γk : KVNames) (recorded : w64 → IProp GF) (γc : CompactorNames) (rev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗
      isCompactor c cl γk recorded γc ∗ recRevOk γk recorded rev }}
    (App (Val (c @!! go.GoType.PointerType k8s_io.apiserver.pkg.storage.etcd3.compactor.ty @!!
      go!"UpdateCompactRevision")) (Val #rev))
  {{ RET #(); compactRevLb γc rev }}

end spec

end k8s
end EtcdGrove
end Perennial
