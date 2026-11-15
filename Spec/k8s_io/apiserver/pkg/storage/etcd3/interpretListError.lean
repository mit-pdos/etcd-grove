/-
`interpretListError(err, false, continueKey, keyPrefix)` (`k8s.io/apiserver/pkg/storage/etcd3/
errors.go:66-75`) of a client error, not paging: `err == rpctypes.ErrCompacted` (an `EtcdError`
value, D1: a comparable struct) gives `NewResourceExpired(expired)`, a 410; else `err` itself.
Either is `listErr`. Proved (stage 7e-2, `notes/k8s-7e-2-draft.md` §3.5; the precondition the
client branch of `unkErr`, `kClientErr`, a form settled at Prove with D1). Lean-first (no Rocq
counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.ListDefs

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
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (Obj : Type) [DecidableEq Obj] (c : StoreCfg GF Obj) (err : GoInterface) (ck kp : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗ kClientErr err }}
    (App (App (App (App (Val (@! k8s_io.apiserver.pkg.storage.etcd3.interpretListError)) (Val #err))
      (Val #false)) (Val #ck)) (Val #kp))
  {{ (e : GoInterface), RET #e; listErr c e }}

end spec

end k8s
end EtcdGrove
end Perennial
