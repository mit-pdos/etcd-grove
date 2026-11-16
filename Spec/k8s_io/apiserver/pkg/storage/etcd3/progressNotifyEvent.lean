/-
`progressNotifyEvent(rev)` (`k8s.io/apiserver/pkg/storage/etcd3/event.go:86-92`): a fresh `*event`,
owned, at the revision `rev`, a progress notification, not (yet) the initial-events-end bookmark
(`startWatching` sets that flag on the one it queues after the initial events). Proved (k8s 7f-5a-P
step 3). Lean-first (no Rocq counterpart).
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
abbrev progressNotifyEvent.spec : Prop :=
  ∀ (rev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 }}
    (App (Val (@! k8s_io.apiserver.pkg.storage.etcd3.progressNotifyEvent)) (Val #rev))
  {{ (p : Loc), RET #p; ∃ ev : k8s_io.apiserver.pkg.storage.etcd3.event, p ↦ ev ∗
      ⌜ev.rev' = rev ∧ ev.isProgressNotify' = true ∧ ev.isInitialEventsEndBookmark' = false⌝ }}

end spec

end k8s
end EtcdGrove
end Perennial
