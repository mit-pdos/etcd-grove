/-
`parseKV(kv)` (`k8s.io/apiserver/pkg/storage/etcd3/event.go:53-64`): a fresh `*event`, owned, of
the key-value `kv` of an initial list (`syncPaginated`): its key, value and mod revision, created,
an initial event (`kEvIs`'s `.kv` case; any state). Proved (k8s 7f-5a-P step 3). Lean-first (no Rocq
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
abbrev parseKV.spec : Prop :=
  ∀ (l : Loc) (v : EtcdKv) (σ : KVState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗ kvValAt l v }}
    (App (Val (@! k8s_io.apiserver.pkg.storage.etcd3.parseKV)) (Val #l))
  {{ (p : Loc), RET #p; ∃ ev : k8s_io.apiserver.pkg.storage.etcd3.event, p ↦ ev ∗
      kEvIs σ ev (KRaw.kv v) }}

end spec

end k8s
end EtcdGrove
end Perennial
