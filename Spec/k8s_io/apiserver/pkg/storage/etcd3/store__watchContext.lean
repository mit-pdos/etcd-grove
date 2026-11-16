/-
`(*store).watchContext(ctx)` (`k8s.io/apiserver/pkg/storage/etcd3/store.go:1154-1163`): is
`clientv3.WithRequireLeader(ctx)`, so any triple of that call (`WithRequireLeader.spec`'s, with
`WithRequireLeader.isContext_of_post` and `watchCtx_of_post`) is one of this call; the receiver is not
read. Proved (k8s 7f-5a-P step 3). Lean-first (no Rocq counterpart).
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
abbrev store.watchContext.spec : Prop :=
  ∀ (sp : Loc) (ctx : GoInterface) (P : IProp GF) (Ψ : GoInterface → IProp GF),
  (∀ Φ : val → IProp GF, P -∗ ▷ (∀ c : GoInterface, Ψ c -∗ Φ #c) -∗
    WP (App (Val (@! go_etcd_io.etcd.client.v3.WithRequireLeader)) (Val #ctx)) {{ Φ }}) →
  ∀ Φ : val → IProp GF,
  isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗ P -∗
  ▷ (∀ c : GoInterface, Ψ c -∗ Φ #c) -∗
  WP (App (Val (sp @!! go.GoType.PointerType k8s_io.apiserver.pkg.storage.etcd3.store.ty @!!
    go!"watchContext")) (Val #ctx)) {{ Φ }}

end spec

end k8s
end EtcdGrove
end Perennial
