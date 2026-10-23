/-
`kubernetes.New(cfg)` (`client/v3/kubernetes/client.go`; stage 6e of `notes/k8s-etcd3-plan.md`):
`clientv3.New(cfg)`'s client, wrapped: a `*kubernetes.Client` `kc` holding it and itself as its
`Kubernetes` interface (read-only from here: what `etcd3.New` takes), or `clientv3.New`'s error.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.New
public import Proof.go_etcd_io.etcd.client.v3.kubernetes.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kubernetes

open Iris Iris.BI client

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.kubernetes.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- See the file header. -/
abbrev New.spec : Prop :=
  ∀ (cfg : go_etcd_io.etcd.client.v3.Config) (eps : List GoString) (V : WEnv GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.kubernetes ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      clientCfgOk cfg eps ∗ ⌜threadBound GF ≤ 2 ^ 31⌝ }}
    (App (Val (@! go_etcd_io.etcd.client.v3.kubernetes.New)) (Val #cfg))
  {{ (kc : Loc) (err : GoInterface), RET (PairV #kc #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ cl : Loc,
        kc ↦□ (go_etcd_io.etcd.client.v3.kubernetes.Client.mk cl
          (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.kubernetes.Client.ty)
            #kc)) ∗
        isNewClient cl eps V ∗ (⌜cfg.MaxUnaryRetries' = W64 1⌝ -∗ clientKVOnce cl eps)) ∨
      ⌜err ≠ GoInterface.nil⌝ }}

end spec

end kubernetes
end EtcdGrove
end Perennial
