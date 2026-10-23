/-
`New(c, compactor, codec, newFunc, newListFunc, reverseKeyFunc, prefix, resourcePrefix,
groupResource, transformer, leaseManagerConfig, decoder, versioner)`
(`k8s.io/apiserver/pkg/storage/etcd3/store.go`; stage 6e of `notes/k8s-etcd3-plan.md`). Lean-first
(no Rocq counterpart).

A store over the kubernetes client `c` (its `clientv3.Client` `cl`: what `isStore` asks of the
client, at the members `ms`), whose objects the codec, versioner, transformer and decoder handle as
`S` describes (`contractOk`): `isStore sp c` of the configuration of these, with the path prefix
`prefix` (`pfx0`) and some metrics tracker. `newFunc` returns a non-`nil` object (the watcher's object
type is its `reflect` type's name).

Premises: `prefix` is a clean absolute path (`path.Join("/", prefix)` is `prefix`, with no
trailing `/`: `PathCleanAbs`), `resourcePrefix` starts with `/` and is not `/`. And the
`clientv3.Client`'s `ctx` field, read-only (`Ctx()`, for the feature checker): the client's
`New` spec does not give it yet ("From the etcd client proof" of `notes/k8s-etcd3-plan.md`).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Store
public import Spec.path.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

/-- See the file header. -/
abbrev New.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (Obj : Type) [DecidableEq Obj] (S : ObjSpec GF Obj) (kc cl : Loc) (ms : List (client.SrvAt GF))
    (V : client.WEnv GF) (γh : GName) (cmp codec : GoInterface) (nf nlf rkf : GoFunc)
    (pfx0 rp : GoString) (gr : k8s_io.apimachinery.pkg.runtime.schema.GroupResource)
    (vi ti di : GoInterfaceOk) (lmc : k8s_io.apiserver.pkg.storage.etcd3.LeaseManagerConfig),
  path.PathCleanAbs pfx0 → go!"/" <+: rp → rp ≠ go!"/" →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗
      kc ↦□ (go_etcd_io.etcd.client.v3.kubernetes.Client.mk cl
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.kubernetes.Client.ty)
          #kc)) ∗
      isNewClient cl (ms.map client.SrvAt.addr) V ∗
      client.clientWriteOnce cl (ms.map client.SrvAt.addr) ∗
      ([∗list] x ∈ ms, client.kvRegsAt x) ∗ ⌜∀ x ∈ ms, ∀ op, x.γr.kv.wl.writes op⌝ ∗
      (∃ cx : GoInterface, structFieldRef go_etcd_io.etcd.client.v3.Client go!"ctx" cl ↦□ cx) ∗
      contractOk S codec vi ti di ∗
      □ (∀ Φ : val → IProp GF, ▷ (∀ x : GoInterface, ⌜x ≠ GoInterface.nil⌝ -∗ Φ #x) -∗
        WP (App (Val #nf) (Val #())) {{ Φ }}) }}
    (App (App (App (App (App (App (App (App (App (App (App (App (App
      (Val (@! k8s_io.apiserver.pkg.storage.etcd3.New)) (Val #kc)) (Val #cmp)) (Val #codec))
      (Val #nf)) (Val #nlf)) (Val #rkf)) (Val #pfx0)) (Val #rp)) (Val #gr))
      (Val #(GoInterface.ok ti))) (Val #lmc)) (Val #(GoInterface.ok di))) (Val #(GoInterface.ok vi)))
  {{ (sp : Loc) (err : GoInterface), RET (PairV #sp #err); ⌜err = GoInterface.nil⌝ ∗
      ∃ mt lt : Loc, isStore sp
        ⟨S, codec, vi, ti, di, pfx0, rp, gr, kc, cl, ms, V, mt, lt, γh⟩ }}

end spec

end k8s
end EtcdGrove
end Perennial
