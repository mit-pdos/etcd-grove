/-
`(*store).conditionalDelete(ctx, key, out, v, nil, validateDeletion, nil, false)`
(`k8s.io/apiserver/pkg/storage/etcd3/store.go`; phase 4 of `notes/k8s-etcd3-plan.md`). Lean-first
(no Rocq counterpart).

`Delete`'s loop on the prepared key `key`: read the key (`getCurrentState`), check
`validateDeletion` on the object (`validateOk`), try the conditional delete (`deleteOnce`), and
retry on a conflict from the state the conflict saw. With the caller's updates at the members
(`k8sAuRW`, D30n: handing the caller's timeless token `W` at the linearization point), the outcome
is the model's `delete` (`delOut`): at the state the write fired at, or at a read whose state the
answer ("not found", `validateDeletion`'s error) came from (the first read's through `rwInv`, a
conflict's directly), or an error of the client.

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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

/-- See the file header. -/
abbrev store.conditionalDelete.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (Obj : Type) [DecidableEq Obj] (E : Type) [KUserErr E] (sp : Loc) (c : StoreCfg GF Obj) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (key : GoString) (out : GoInterface) (o0 : Obj)
    (rv0 : GoString) (v : _root_.Perennial.reflect.Value) (p : Loc)
    (validate : Obj → Nat → Option E) (vf : GoFunc) (W : IProp GF) [Timeless W]
    (Φ : KVState → IProp GF),
  c.pfx <+: key → key.length ≤ 2 ^ 27 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗ isStore sp c ∗
      ctxOk ci cd ∗ ctxErrClient ci cd ∗ c.S.objAt out o0 rv0 ∗
      ⌜reflectM.reflElem v c.S.objTy p⌝ ∗ W ∗
      ([∗list] x ∈ c.ms, k8sAuRW x.γr.kv c (delStep key validate) W Φ) ∗
      validateOk c validate vf }}
    (App (App (App (App (App (App (App (App (Val (sp @!! go.GoType.PointerType
      k8s_io.apiserver.pkg.storage.etcd3.store.ty @!! go!"conditionalDelete"))
      (Val #(GoInterface.ok ci))) (Val #key)) (Val #out)) (Val #v)) (Val #null)) (Val #vf))
      (Val #GoInterface.nil)) (Val #false))
  {{ (err : GoInterface), RET #err; delOut c key validate Φ err out }}

end spec

end k8s
end EtcdGrove
end Perennial
