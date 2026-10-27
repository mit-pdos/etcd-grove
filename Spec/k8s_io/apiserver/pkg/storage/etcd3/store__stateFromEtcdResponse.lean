/-
`(*store).stateFromEtcdResponse(ctx, kv, rev, key, v, false, false)`
(`k8s.io/apiserver/pkg/storage/etcd3/store.go`; phase 4 of `notes/k8s-etcd3-plan.md`). Lean-first
(no Rocq counterpart).

The store's reading of a key's key-value `kv` (a response's, `kvOut`), decoded into a fresh object
of the type of `v` (`conversion.EnforcePtr(out)`'s `reflect.Value`: `reflect.New(v.Type())`): no
key-value is "not found" at the response's revision `rev`; a key-value gives a new `*objState`
holding the store's reading of it (`stOfKv`). The key-value's value decodes (what a state of the
store gives, `kvWf`), so the transformer's and the decoder's errors do not arise.

For now `ignoreNotFound` is `false` (`Delete`'s), and so is `expectTransformOrDecodeError` (D30d:
`AllowUnsafeMalformedObjectDeletion` not asked for).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.State

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
abbrev store.stateFromEtcdResponse.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (Obj : Type) [DecidableEq Obj] (sp : Loc) (c : StoreCfg GF Obj) (ctx : GoInterface)
    (kvp : Loc) (mkv : Option EtcdKv) (rev : w64) (key : GoString)
    (v : _root_.Perennial.reflect.Value) (p : Loc),
  (∀ kv, mkv = some kv → ∃ o b, c.S.dec kv.value = some (o, b)) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗ isStore sp c ∗
      kubernetes.kvOut kvp mkv ∗ ⌜reflectM.reflElem v c.S.objTy p⌝ }}
    (App (App (App (App (App (App (App (Val (sp @!! go.GoType.PointerType
      k8s_io.apiserver.pkg.storage.etcd3.store.ty @!! go!"stateFromEtcdResponse")) (Val #ctx))
      (Val #kvp)) (Val #rev)) (Val #key)) (Val #v)) (Val #false)) (Val #false))
  {{ (st : Loc) (err : GoInterface), RET (PairV #st #err);
      match mkv with
      | none => ⌜st = null⌝ ∗ storageErrIs err (W64 1) key rev
      | some kv => ⌜err = GoInterface.nil⌝ ∗ ∃ s, ownState c st s ∗ ⌜stOfKv c kv s⌝ }}

end spec

end k8s
end EtcdGrove
end Perennial
