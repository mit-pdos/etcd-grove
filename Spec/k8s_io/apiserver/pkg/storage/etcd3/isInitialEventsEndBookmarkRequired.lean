/-
`isInitialEventsEndBookmarkRequired(opts)` (`k8s.io/apiserver/pkg/storage/etcd3/watcher.go:225-230`):
with `WatchList` on (`watchListOn`), whether `SendInitialEvents` is set to `true` with
`AllowWatchBookmarks` (`kModeOf`'s `bmReq`). Proved (k8s 7f-5a-P step 3). Lean-first (no Rocq
counterpart).
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
abbrev isInitialEventsEndBookmarkRequired.spec : Prop :=
  ∀ (opts : k8s_io.apiserver.pkg.storage.ListOptions) (sie : Option Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗
      sendInitIs opts.SendInitialEvents' sie ∗ watchListOn }}
    (App (Val (@! k8s_io.apiserver.pkg.storage.etcd3.isInitialEventsEndBookmarkRequired)) (Val #opts))
  {{ RET #(decide (sie = some true ∧ opts.Predicate'.AllowWatchBookmarks' = true)); True }}

end spec

end k8s
end EtcdGrove
end Perennial
