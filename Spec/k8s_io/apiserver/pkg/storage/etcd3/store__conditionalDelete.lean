/-
`(*store).conditionalDelete(ctx, key, out, v, nil, validateDeletion, nil, false)`
(`k8s.io/apiserver/pkg/storage/etcd3/store.go`; phase 4 of `notes/k8s-etcd3-plan.md`). Lean-first
(no Rocq counterpart).

`Delete`'s loop on the prepared key `key`: read the key (`getCurrentState`), check
`validateDeletion` on the object (`validateOk`), try the conditional delete (`deleteOnce`), and
retry on a conflict from the state the conflict saw. With the caller's updates at the members
(`k8sAuRW`, the model's `delete` as the write, `W` its token), the outcome is the model's
`delete` (`delOut`): at the state the write fired at, or at the read a read-like answer ("not
found", `validateDeletion`'s error) came from, or an error of the client.

For now no preconditions, no cached object, and decode errors not expected.
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Steps

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
abbrev store.conditionalDelete.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (Obj : Type) [DecidableEq Obj] (E : Type) (sp : Loc) (c : StoreCfg GF Obj) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (key : GoString) (out : GoInterface) (o0 : Obj)
    (rv0 : GoString) (v : _root_.Perennial.reflect.Value) (p : Loc)
    (validate : Obj → Nat → Option E) (vf : GoFunc) (W : IProp GF) (Q Φ : KVState → IProp GF),
  c.pfx <+: key →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗ isStore sp c ∗
      ctxOk ci cd ∗ ctxErrClient ci cd ∗ c.S.objAt out o0 rv0 ∗
      ⌜reflectM.reflElem v c.S.objTy p⌝ ∗ W ∗
      ([∗list] x ∈ c.ms, k8sAuRW x.γr.kv c (delStep key validate) W Q Φ) ∗
      validateOk c validate vf }}
    (App (App (App (App (App (App (App (App (Val (sp @!! go.GoType.PointerType
      k8s_io.apiserver.pkg.storage.etcd3.store.ty @!! go!"conditionalDelete"))
      (Val #(GoInterface.ok ci))) (Val #key)) (Val #out)) (Val #v)) (Val #null)) (Val #vf))
      (Val #GoInterface.nil)) (Val #false))
  {{ (err : GoInterface), RET #err; delOut c key validate W Q Φ err out }}

end spec

end k8s
end EtcdGrove
end Perennial
