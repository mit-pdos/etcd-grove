/-
`refreshOnError(st, err, getCurrentState)` (`k8s.io/apiserver/pkg/storage/etcd3/store.go`; phase 4
of `notes/k8s-etcd3-plan.md`). Lean-first (no Rocq counterpart).

For a state just read from etcd (`current`): the state and the error, unchanged (the closure is not
called; the state's object is not read, `ownStateX`). The stale case (a cached object, `Delete`'s `cachedExistingObject`) is not used yet.
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

/-- See the file header. -/
abbrev refreshOnError.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (Obj : Type) [DecidableEq Obj] (c : StoreCfg GF Obj) (st : Loc) (s : OState Obj)
    (err : GoInterface) (f : GoFunc) (x : GoInterface),
  s.current = true →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗ ownStateX c st s x }}
    (App (App (App (Val (@! k8s_io.apiserver.pkg.storage.etcd3.refreshOnError)) (Val #st))
      (Val #err)) (Val #f))
  {{ (st' : Loc) (err' : GoInterface), RET (PairV #st' #err');
      ⌜st' = st ∧ err' = err⌝ ∗ ownStateX c st s x }}

end spec

end k8s
end EtcdGrove
end Perennial
