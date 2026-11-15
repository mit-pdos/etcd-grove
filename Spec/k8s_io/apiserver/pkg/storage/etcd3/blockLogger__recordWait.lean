/-
`(*blockLogger).recordWait(waitTime)` (`k8s.io/apiserver/pkg/storage/etcd3/block_logger.go:59-86`)
on a block logger (`blockLoggerOk`), from any goroutine: returns (under its mutex it counts the
wait, and at most once an interval logs through `klog.V(3).InfoS`). Proved (k8s 7f-5a-P step 3)
over the candidate text `klog.Verbose.InfoS.spec` (a callee hypothesis, no axiom). Lean-first (no
Rocq counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.WatchDefs

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
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

/-- See the file header. -/
abbrev blockLogger.recordWait.spec : Prop :=
  ∀ (l : Loc) (d : time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗ blockLoggerOk l }}
    (App (Val (l @!! go.GoType.PointerType k8s_io.apiserver.pkg.storage.etcd3.blockLogger.ty @!!
      go!"recordWait")) (Val #d))
  {{ RET #(); True }}

end spec

end k8s
end EtcdGrove
end Perennial
