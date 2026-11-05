/-
`(*store).Delete(ctx, key, out, preconditions, validateDeletion, cachedExistingObject, opts)`
(`k8s.io/apiserver/pkg/storage/etcd3/store.go`; phase 4 of `notes/k8s-etcd3-plan.md`). Lean-first
(no Rocq counterpart).

A delete, retried on conflicts: with the caller's updates at the members (`k8sAuRW`: persistent,
firing as a plain read any number of times, and once as the linearization point, handing the
caller's timeless token `W` back, D30n), its outcome is `correctness.Model`'s `delete`
(`delOut`): at the state the update fired at as the linearization point (`Φ σ`): the write
(`out` the deleted object at the new revision), or a read-like answer ("not found", a failed
precondition, `validateDeletion`'s error, nothing changed); or an error of the client. `validateDeletion` is the caller's
callback, answering `validate` (`validateOk`).

The preconditions `pp` hold `pr` (`preAt`; `nil`: none), checked as the model's `pre`
(`ObjCodec.preOk`: the object's UID and resource version string); the cached object `cx` is `nil`
or one the key held at its resource version (`cachedOk`, `versionAt`; stage 7b). For now the key is
valid, and the caller does not ask to delete a malformed object (`opts.ExpectTransformOrDecodeError` false: then the feature
gate `AllowUnsafeMalformedObjectDeletion` does not matter, D30d).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Steps
public import Proof.k8s_io.apiserver.pkg.storage.Defs

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
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

/-- See the file header. -/
abbrev store.Delete.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (Obj : Type) [DecidableEq Obj] (E : Type) [KUserErr E] (sp : Loc) (c : StoreCfg GF Obj) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (key : GoString) (out : GoInterface) (o0 : Obj)
    (rv0 : GoString) (pp : Loc) (pr : KPre) (cx : GoInterface) (ca : Option (Obj × w64))
    (opts : k8s_io.apiserver.pkg.storage.DeleteOptions)
    (validate : Obj → Nat → Option E) (vf : GoFunc) (W : IProp GF) [Timeless W]
    (Φ : KVState → IProp GF) (k : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗ isStore sp c ∗
      ⌜prepareKeyM c.resourcePrefix key false = some k ∧ (c.pathPrefix ++ k).length ≤ opKeyMax ∧
        opts.ExpectTransformOrDecodeError' = false⌝ ∗
      ctxOk ci cd ∗ ctxErrClient ci cd ∗ c.S.objAt out o0 rv0 ∗ preAt pp pr ∗
      cachedOk c (c.pathPrefix ++ k) cx ca ∗ W ∗
      ([∗list] x ∈ c.ms, k8sAuRW x.γr.kv c (delStep (c.pathPrefix ++ k) (c.S.preOk pr) validate) W Φ) ∗
      validateOk c validate vf }}
    (App (App (App (App (App (App (App (Val (sp @!! go.GoType.PointerType
      k8s_io.apiserver.pkg.storage.etcd3.store.ty @!! go!"Delete")) (Val #(GoInterface.ok ci)))
      (Val #key)) (Val #out)) (Val #pp)) (Val #vf)) (Val #cx)) (Val #opts))
  {{ (err : GoInterface), RET #err;
      delOut c (c.pathPrefix ++ k) (c.S.preOk pr) validate Φ err out }}

end spec

end k8s
end EtcdGrove
end Perennial
