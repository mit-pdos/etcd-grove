/-
`(*clientv3.watcher).Watch(ctx, key, opts...)` (`client/v3/watch.go`; (the watch slice's unit W-C). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvWatch

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3 client

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`w.Watch(ctx, key, opts...)`**, the contract's watch (`isEtcdRangeWatcher`'s triple at `w`):
a range watch under the watcher's prefix from `rev ≥ 0` returns an SPSC channel of responses
satisfying `rangeWatchElem` at the server's model, which may be closed, with the consumer's
side. -/
abbrev watcher.Watch.spec : Prop :=
  ∀ (V : WEnv GF) (w : Loc) (ctx : GoInterfaceOk) (cs : context.ContextDesc (IProp GF))
    (key : GoString) (sl : GoSlice) (gs : List (OpFull → OpFull)) (rev : w64) (sr : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      isPkgInit (PROP := IProp GF) pkg_id.context ∗ isClientWatcher V w ∗
      context.isContext ctx cs ∗ optsAt sl gs ∗
      ⌜(opWatchModel key gs).isRangeWatch rev = true ∧ ¬ opWatchPanics key gs ∧
        0 ≤ sint.Z rev ∧
        KeyRangeUnder V.pfx (opWatchModel key gs).key (opWatchModel key gs).base.rangeEnd⌝ ∗
      startOk V sr rev }}
    (App (App (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.watcher.ty @!! go!"Watch")) (Val #(GoInterface.ok ctx))) (Val #key)) (Val #sl))
  {{ (ch : Loc) (γ : EtcdWatchNames), RET #ch;
      isSpsc γ.spsc ch (rangeWatchElem (EM := V.EM) γ V.pfx (opWatchModel key gs) rev)
        (fun _ => iprop(True)) ∗
      spscConsumer γ.spsc ([] : List go_etcd_io.etcd.client.v3.WatchResponse) ∗
      monoListIdxOwn γ.cur 0 (rev - W64 1) ∗ monoListIdxOwn γ.cur2 0 (rev - W64 1) }}

end spec

end EtcdGrove
end Perennial
