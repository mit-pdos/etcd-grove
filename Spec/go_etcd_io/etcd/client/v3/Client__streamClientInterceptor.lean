/-
`c.streamClientInterceptor(optFuncs...)` (`client/v3/retry_interceptor.go`, names only; item 5): the
client's stream interceptor, installed at dial. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvClientNew

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

/-- `c.streamClientInterceptor(optFuncs...)` on a client `New` builds (`retryClientOk`), with
options each building the interceptor's options (`optApplyOk`): etcd's stream interceptor
(`etcdStreamInterceptor`, what grpc's `NewStream` axiom assumes). -/
abbrev Client.streamClientInterceptor.spec : Prop :=
  ∀ (c : Loc) (sl : GoSlice) (ros : List go_etcd_io.etcd.client.v3.retryOption),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ retryClientOk c ∗
      sl ↦*□ ros ∗ [∗list] ro ∈ ros, optApplyOk ro.applyFunc' }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
      go!"streamClientInterceptor")) (Val #sl))
  {{ (f : GoFunc), RET #f; ⌜etcdStreamInterceptor f⌝ }}

end spec

end EtcdGrove
end Perennial
