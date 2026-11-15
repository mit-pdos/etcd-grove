/-
## `(*Read).sendReadIndex(requestIndex)` (internal helper)

**Users.** `requestCurrentIndex` (`read.go:152,199,213`), with a context it registered.

**Proof sketch.** `uint64ToBigEndianBytes` (`be64 id`), `context.WithTimeout(context.Background(),
RequestTimeout())` (W0's `Context.WithTimeout.spec`, `ctxOk_background`), `rf.ReadIndex(cctx,
ctx)` (`readEnv`'s, R1's `node.ReadIndex.spec`), `cancel()`, `errors.Is`, the logger's `Warn` and
the metric (W0's zap, 4b's metrics).

**Changes.** Restated over `readEnv`. **Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.read.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Read

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.read.Assumptions]

/-- Sends the read request of the registered context `be64 id`: `nil` or a read path error. -/
def Read.sendReadIndex.spec : Prop :=
  ∀ (r : Loc) (srv rf : GoInterface) (rγ : Raft.Cluster) (γi : IdUtil.IdSpace)
    (A : Nat → IProp GF) (id : w64) (Q : List Raft.LogEntry → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.read ∗
      r.[go_etcd_io.etcd.server.v3.etcdserver.read.Read, go!"server"] ↦□ srv ∗
      r.[go_etcd_io.etcd.server.v3.etcdserver.read.Read, go!"raft"] ↦□ rf ∗
      readEnv srv rf rγ γi A ∗ Raft.readCtx rγ (be64 id) Q }}
    (App (Val (r @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.read.Read.ty @!!
      go!"sendReadIndex")) (Val #id))
  {{ (err : GoInterface), RET #err; (⌜err = GoInterface.nil⌝ ∨ readErr err) }}

end spec
end Read
end EtcdGrove
end Perennial
