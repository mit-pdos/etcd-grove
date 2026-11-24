/-
`newBlockLogger(interval, threshold, msg, objectType, groupResource, clock)`
(`k8s.io/apiserver/pkg/storage/etcd3/block_logger.go:46-57`) with a clock whose `Now()` returns (the
watcher passes `clock.RealClock{}`): a block logger (`blockLoggerOk`). Proved (k8s 7f-5a-P step 3).
Lean-first (no Rocq counterpart).
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
abbrev newBlockLogger.spec : Prop :=
  ∀ (iv th : time.Duration) (msg ot : GoString)
    (gr : k8s_io.apimachinery.pkg.runtime.schema.GroupResource) (ck : GoInterfaceOk),
  (msg.length : Int) ≤ maxAddr →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗ clockNowOk ck }}
    (App (App (App (App (App (App (Val (@! k8s_io.apiserver.pkg.storage.etcd3.newBlockLogger))
      (Val #iv)) (Val #th)) (Val #msg)) (Val #ot)) (Val #gr)) (Val #(GoInterface.ok ck)))
  {{ (l : Loc), RET #l; blockLoggerOk l }}

end spec

end k8s
end EtcdGrove
end Perennial
