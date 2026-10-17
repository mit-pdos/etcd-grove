/-
`(*clientv3.kv).GetStream(ctx, key, opts...)` (`client/v3/kv.go`), translated for etcd#21330
(`pr-verify/etcd-21330`), which adds its empty-key check. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvKVConn

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `kv.GetStream(ctx, key, opts...)` on a `*kv`, **for a get whose key is empty** after the
options (`(opGetModel key gs).key = []`: `WithPrefix` and `WithFromKey` replace an empty key by
`"\x00"`, so `GetStream("", WithPrefix())` is not covered): `OpGet(key, opts...)` (options that
do not panic and keep the range type, with a resource `R`, given back: `optsAtRes`), then a nil
channel and `rpctypes.ErrEmptyKey` itself (the value of the global, not through `ContextError`),
a non-nil client error, with no RPC (the spec asks for no connection: `kvObjAt` is not a
premise, and no `RangeStream` registration). A partial spec (progressive verification): a
non-empty key's stream (the `RangeStream` call and the receiving goroutine) is not specified. -/
abbrev kv.GetStream.spec : Prop :=
  ∀ (api : Loc) (ci : GoInterfaceOk) (key : GoString) (sl : GoSlice)
    (gs : List (OpFull → OpFull)) (R : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ optsAtRes sl gs R ∗ R ∗
      ⌜¬ opGetPanics gs ∧ (opGetModel key gs).t = W64 1 ∧ (opGetModel key gs).key = []⌝ ∗
      emptyKeyOk }}
    (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
        go!"GetStream")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #sl))
  {{ (ch : GoChan) (err : GoInterface), RET (PairV #ch #err); R ∗
      ⌜ch = chan.nil ∧ err ≠ GoInterface.nil ∧ clientErr err⌝ ∗
      globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrEmptyKey ↦□ err ∗ go_etcd_io.etcd.cache.v3.statusErrOk err }}

end spec

end EtcdGrove
end Perennial
