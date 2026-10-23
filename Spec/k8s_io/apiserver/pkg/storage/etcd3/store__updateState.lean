/-
`(*store).updateState(st, userUpdate)` (`k8s.io/apiserver/pkg/storage/etcd3/store.go`; phase 4 of
`notes/k8s-etcd3-plan.md`). Lean-first (no Rocq counterpart).

The caller's `tryUpdate` (`tryUpdateOk`, the model's `f`) on the state's object and metadata, then
`PrepareObjectForStorage` on its result: the result without its resource version and no TTL, or
`tryUpdate`'s error. The state keeps everything but its object, which `tryUpdate` took.
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
abbrev store.updateState.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (Obj : Type) [DecidableEq Obj] (E : Type) [KUserErr E] (sp : Loc) (c : StoreCfg GF Obj) (st : Loc)
    (s : OState Obj) (f : Obj → Nat → Except E Obj) (uf : GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗ isStore sp c ∗
      ownState c st s ∗ tryUpdateOk c f uf }}
    (App (App (Val (sp @!! go.GoType.PointerType
      k8s_io.apiserver.pkg.storage.etcd3.store.ty @!! go!"updateState")) (Val #st)) (Val #uf))
  {{ (ret : GoInterface) (ttl : w64) (err : GoInterface), RET (PairV (PairV #ret #ttl) #err);
      (∃ x, ownStateX c st s x) ∗
      match f s.o (uint.nat s.rev) with
      | .ok o' => ⌜err = GoInterface.nil ∧ ttl = W64 0⌝ ∗ c.S.objAt ret o' []
      | .error e => ⌜err ≠ GoInterface.nil ∧ KUserErr.is e err⌝ }}

end spec

end k8s
end EtcdGrove
end Perennial
