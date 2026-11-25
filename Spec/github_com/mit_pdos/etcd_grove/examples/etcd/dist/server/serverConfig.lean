/- Lean-first (no Rocq counterpart).

`server.serverConfig(c, lg)` (`examples/etcd/dist/server`): the member's `config.ServerConfig`, `memberCfg`
(`MemberDefs.lean`) of `c`, `lg`, the initial cluster's map, the member's URL slices and the server's feature
gate (`features.NewDefaultServerFeatureGate`'s: `CompactHashCheck` and `LeaseCheckpoint` off). The map's keys are
the initial cluster's names (distinct), each slice the one peer URL of its entry (`iuP`); the map, its slices and
the URL slices read-only.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.MemberDefs
public import Proof.go_etcd_io.etcd.server.v3.features.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist
namespace server

open Iris Iris.BI Net go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver etcdstart
open github_com.mit_pdos.etcd_grove.examples.etcd.dist

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.Assumptions]

/-- See the file header. -/
abbrev serverConfig.spec : Prop :=
  ∀ (cv : github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.Config)
    (pl : List github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.Peer) (lg : Loc),
  (pl.map (·.Name')).Nodup →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.server ∗
      cv.Cluster' ↦*□ pl }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.serverConfig)) (Val #cv))
      (Val #lg))
  {{ (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig), RET #cfg;
      ∃ (cluster : Loc) (M : GMap GoString GoSlice) (pu cu : GoSlice) (fgp : Loc),
      ⌜cfg = memberCfg cv lg cluster pu cu (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.pkg.v3.featuregate.featureGate.ty) #fgp) ∧ fgp ≠ null ∧
        ∀ n, (M.lookup n).isSome ↔ n ∈ pl.map (·.Name')⌝ ∗
      cluster ↦$□ M ∗ ([∗map] n ↦ sl ∈ M, sl ↦*□ iuP pl n) ∗
      pu ↦*□ [httpURL cv.Peer'] ∗ cu ↦*□ [httpURL cv.Client'] ∗
      isFeatureGate (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.pkg.v3.featuregate.featureGate.ty) #fgp) ∗ featureIs (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.pkg.v3.featuregate.featureGate.ty) #fgp) go!"CompactHashCheck" false ∗
      featureIs (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.pkg.v3.featuregate.featureGate.ty) #fgp) go!"LeaseCheckpoint" false }}

end spec

end server
end etcd_dist
end EtcdGrove
end Perennial

end
