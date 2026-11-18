/- Lean-first (no Rocq counterpart).

`watchOptions(in)` (watch.go): a watch's `storage.ListOptions`, `watchOptsV x p`
(`predicate(in)` with `AllowWatchBookmarks := in.Bookmarks`; `ProgressNotify`, `RecordTimestamps`
false), its `SendInitialEvents` a fresh cell `p` (`sendInitOwn`) as `in.SendInit` says (`sieOfL`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.WRun

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI k8s
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev watchOptions.spec : Prop :=
  ∀ (x : Input),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.watchOptions)) (Val #x))
  {{ (p : Loc), RET #(watchOptsV x p); sendInitOwn p (sieOfL x) }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
