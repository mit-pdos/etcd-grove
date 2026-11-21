/-
`checkVersionCompatibility(name, server, minCluster)` (`util.go`; rafthttp stage 6e, 2026-10-24).
Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Stream

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

/-- **`checkVersionCompatibility(name, server, minCluster)`** of two versions (not `nil`; read-only, 2026-11-20, prove-smalllibs: `Major`/`Minor` read them): the
local server version and minimum cluster version (`version.Version`'s and `MinClusterVersion`'s,
parsed: valid, so not `nil`, read-only) and an error (`nil`, or an `Errorf` error when a version is too low). -/
abbrev rafthttp.checkVersionCompatibility.spec : Prop :=
  ∀ (name : GoString) (server minCluster : Loc) (xs xm : github_com.Masterminds.semver.v3.Version),
  server ≠ null → minCluster ≠ null →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      server ↦□ xs ∗ minCluster ↦□ xm }}
    (App (App (App (Val (@! rafthttp.checkVersionCompatibility)) (Val #name)) (Val #server))
      (Val #minCluster))
  {{ (ls lm : Loc) (err : GoInterface), RET (PairV (PairV #ls #lm) #err); ⌜ls ≠ null ∧ lm ≠ null⌝ ∗
      (∃ x : github_com.Masterminds.semver.v3.Version, ls ↦□ x) ∗ (∃ x : github_com.Masterminds.semver.v3.Version, lm ↦□ x) }}

end spec

end EtcdGrove
end Perennial
