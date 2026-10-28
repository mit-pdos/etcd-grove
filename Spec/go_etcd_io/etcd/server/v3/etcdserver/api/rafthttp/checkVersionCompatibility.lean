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

/-- **`checkVersionCompatibility(name, server, minCluster)`** of two versions (not `nil`): the
local server version and minimum cluster version (`version.Version`'s and `MinClusterVersion`'s,
parsed: valid, so not `nil`) and an error (`nil`, or an `Errorf` error when a version is too low). -/
abbrev rafthttp.checkVersionCompatibility.spec : Prop :=
  ∀ (name : GoString) (server minCluster : Loc),
  server ≠ null → minCluster ≠ null →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp }}
    (App (App (App (Val (@! rafthttp.checkVersionCompatibility)) (Val #name)) (Val #server))
      (Val #minCluster))
  {{ (ls lm : Loc) (err : GoInterface), RET (PairV (PairV #ls #lm) #err); ⌜ls ≠ null ∧ lm ≠ null⌝ }}

end spec

end EtcdGrove
end Perennial
