/-
`(*compactor).Stop()` (`compact.go`): stop the compactor, once (`stopOnce`): close `stop`, then
wait for the loop goroutine (K2 of `notes/k8s-compactor-plan.md`). Lean-first (no Rocq
counterpart). Returns, with nothing: `sync.Once` passes out only a persistent result (a revision
of Draft 2, which had `Stop` give back the loop's thread token; the wait group is `sync.join`'s, its
one `Add` needing no token).
`onClose` is `nil` (`StartCompactorPerEndpoint`'s closure is Q1 (c)).
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
abbrev compactor.Stop.spec : Prop :=
  ∀ (c cl : Loc) (γk : KVNames) (recorded : w64 → IProp GF) (γc : CompactorNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗
      isCompactor c cl γk recorded γc }}
    (App (Val (c @!! go.GoType.PointerType k8s_io.apiserver.pkg.storage.etcd3.compactor.ty @!!
      go!"Stop")) (Val #()))
  {{ RET #(); True }}

end spec

end k8s
end EtcdGrove
end Perennial
