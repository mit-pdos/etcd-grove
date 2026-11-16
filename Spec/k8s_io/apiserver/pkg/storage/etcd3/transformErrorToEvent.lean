/-
`transformErrorToEvent(err)` (`k8s.io/apiserver/pkg/storage/etcd3/watcher.go:779-789`): an Error
`watch.Event` whose object is the `Failure` status of `interpretWatchError(err)` (an `APIStatus`) or
of `NewInternalError` of it. Returns a non-`nil` event pointer and the status, both owned (the caller
makes the status read-only: `statusFailureAt`). Proved (k8s 7f-5a-P step 3).
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
abbrev transformErrorToEvent.spec : Prop :=
  ∀ (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗ kErrOk err }}
    (App (Val (@! k8s_io.apiserver.pkg.storage.etcd3.transformErrorToEvent)) (Val #err))
  {{ (p : Loc), RET #p; ∃ (ev : k8s_io.apimachinery.pkg.watch.Event) (sp : Loc)
      (st : k8s_io.apimachinery.pkg.apis.«meta».v1.Status),
      p ↦ ev ∗ sp ↦ st ∗
      ⌜ev.Type' = go!"ERROR" ∧
        ev.Object' = interface.mkOk (go.GoType.PointerType k8s_io.apimachinery.pkg.apis.«meta».v1.Status.ty) #sp ∧
        st.Status' = go!"Failure"⌝ }}

end spec

end k8s
end EtcdGrove
end Perennial
