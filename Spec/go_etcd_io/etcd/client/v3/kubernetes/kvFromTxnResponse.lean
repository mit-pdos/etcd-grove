/-
`kvFromTxnResponse(resp)` (`client/v3/kubernetes/client.go`; phase 3 of `notes/k8s-etcd3-plan.md`).
Lean-first (no Rocq counterpart).

A transaction's range response (`resp.GetResponseRange()`): its key-value if it has exactly one,
else `nil`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.kubernetes.Defs
public import Proof.go_etcd_io.etcd.client.v3.kubernetes.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kubernetes

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.kubernetes.Assumptions]

/-- See the file header. -/
abbrev kvFromTxnResponse.spec : Prop :=
  ∀ (p : Loc) (rev : w64) (kvs : List EtcdKv) (more : Bool) (count : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.kubernetes ∗
      opRespMsg p (.range rev kvs more count) }}
    (App (Val (@! go_etcd_io.etcd.client.v3.kubernetes.kvFromTxnResponse)) (Val #p))
  {{ (kv : Loc), RET #kv; kvOut kv (single kvs) }}

end spec

end kubernetes
end EtcdGrove
end Perennial
