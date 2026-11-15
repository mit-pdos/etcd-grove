/-
`interpretWatchError(err)` (`k8s.io/apiserver/pkg/storage/etcd3/errors.go:31-50`): `rpctypes.ErrCompacted`
becomes `NewResourceExpired`'s `*StatusError` (a `Failure` status), a corrupt-object error a
`*StatusError` (excluded by `kErrOk`), any other error is returned as is. Proved (k8s 7f-5a-P step 3).
Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.WatchDefs

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
abbrev interpretWatchError.spec : Prop :=
  ∀ (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗ kErrOk err }}
    (App (Val (@! k8s_io.apiserver.pkg.storage.etcd3.interpretWatchError)) (Val #err))
  {{ (err' : GoInterface), RET #err';
      ⌜err' = err⌝ ∨
      ∃ (p : Loc) (st : k8s_io.apimachinery.pkg.apis.«meta».v1.Status),
        ⌜err' = interface.mkOk (go.GoType.PointerType k8s_io.apimachinery.pkg.api.errors.StatusError.ty) #p ∧
          st.Status' = go!"Failure"⌝ ∗
        p ↦ k8s_io.apimachinery.pkg.api.errors.StatusError.mk st }}

end spec

end k8s
end EtcdGrove
end Perennial
