/-
`interpretListError(err, false, continueKey, keyPrefix)` (`k8s.io/apiserver/pkg/storage/etcd3/
errors.go:66-75`) of a client error, not paging: `err == rpctypes.ErrCompacted` (an `EtcdError`
value, D1: a comparable struct) gives `NewResourceExpired(expired)`, a 410; else `err` itself.
Either is `listErr`. Proved (stage 7e-2, `notes/k8s-7e-2-draft.md` §3.5; the precondition the
client branch of `unkErr`, `kClientErr`, a form settled at Prove with D1). Lean-first (no Rocq
counterpart).

(k8s 7f-5a-P, E5, ledger 2026-11-15) Over any `paging`: with paging (`syncPaginated`'s call), an
`ErrCompacted` goes to `handleCompactedErrorForPaging`, given that the prefix encodes the continue
key (`encOkL`, so that the untranslated `utilruntime.HandleError` is not reached); its post
`listErrF` adds the status's `Failure` (the watcher's `sendError` needs it).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.ListDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.KList

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
abbrev interpretListError.spec : Prop :=
  ∀ [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (Obj : Type) [DecidableEq Obj] (c : StoreCfg GF Obj) (err : GoInterface) (paging : Bool)
    (ck kp : GoString),
  (paging = true → k8s_etcd3.encOkL ck kp = true) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗ kClientErr err }}
    (App (App (App (App (Val (@! k8s_io.apiserver.pkg.storage.etcd3.interpretListError)) (Val #err))
      (Val #paging)) (Val #ck)) (Val #kp))
  {{ (e : GoInterface), RET #e; listErrF c e }}

end spec

end k8s
end EtcdGrove
end Perennial
