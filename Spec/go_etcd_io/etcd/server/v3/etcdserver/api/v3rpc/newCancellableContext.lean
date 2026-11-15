/-
`v3rpc.newCancellableContext` (`v3rpc/interceptor.go:278`; k8s 7f-4, the require-leader branch).
Lean-first (no Rocq counterpart); the vocabulary is
`Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/InvCancellable.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvCancellable

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`newCancellableContext(parent)`** over a context `parent` described by `cd`: a fresh
`*cancellableContext` `l` whose embedded context is `c1 = WithCancel(parent)`, the `*cancelCtx` `c`
(done when `parent` is or when `l` is cancelled: the descriptor `cd` with fresh Done names `γ'` and
no Done proposition), with its handle (`v3rpc.ccHandle`: the fields read-only, the lock's writer
guard and its reader slots in a thread pool at `v3rpc.ctxErrLvl`), `c`'s `Value` chain over
`parent` (`ctxValueFrom`) and `c`'s `Context` field. `threadBound GF ≤ 2^30`: the reader slots
(`2^30 - 1`) cover every live thread. -/
abbrev v3rpc.newCancellableContext.spec : Prop :=
  ∀ (parent : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      context.isContext parent cd ∗ ⌜threadBound GF ≤ 2 ^ 30⌝ }}
    (App (Val (@! v3rpc.newCancellableContext)) (Val #(interface.ok parent)))
  {{ (l c : Loc) (γ' : context.ContextNames), RET #l;
      v3rpc.ccHandle l (interface.mk (go.GoType.PointerType _root_.Perennial.context.cancelCtx.ty) #c)
        { cd with PDone := iprop(True), Done_gn := γ' } ∗
      _root_.Perennial.context.ctxValueFrom parent
        (interface.mk (go.GoType.PointerType _root_.Perennial.context.cancelCtx.ty) #c) ∗
      _root_.Perennial.context.ctxField c ↦□ (interface.ok parent : GoInterface) }}

end spec

end EtcdGrove
end Perennial
