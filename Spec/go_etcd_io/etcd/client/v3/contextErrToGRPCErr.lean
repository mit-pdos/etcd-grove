/-
`clientv3.contextErrToGRPCErr` (`client/v3/retry_interceptor.go`).

Users: `waitRetryBackoff`.

Proof sketch: `errors.Is` against the context errors, `status.Error` (2a: a status of code
`Canceled`, `DeadlineExceeded` or `Unknown` is an indefinite call error).

Changes: new (no old spec).

Margin: none.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.ApiLease

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ClientV3

open Iris Iris.BI EtcdModel EtcdWire
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `contextErrToGRPCErr(err)` of a context's error: an indefinite gRPC error. -/
def contextErrToGRPCErr.spec : Prop :=
  ∀ (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ context.isCtxErr err }}
    (App (Val (@! go_etcd_io.etcd.client.v3.contextErrToGRPCErr)) (Val #err))
  {{ (e : GoInterface), RET #e; indefCall e }}

end spec

end ClientV3
end EtcdGrove
end Perennial
