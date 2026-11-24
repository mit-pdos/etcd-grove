/-
`bootstrapNewClusterNoWAL(cfg, prt)` (`bootstrap.go:379-414` at the etcd pin; claim #34, stage 2,
2026-11-25: translated with its body, `bootstrapCluster`'s callee). Lean-first. Its vocabulary:
`BootParts.lean` (`clusterBuilt`) and `BootValues.lean` (`bootGo`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BootParts

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`bootstrapNewClusterNoWAL(cfg, prt)` at a first start of a new cluster**: `bootstrapCluster`'s
spec (`bootstrapCluster.spec`, whose case `bwal == nil && cfg.NewCluster` this is). -/
abbrev bootstrapNewClusterNoWAL.spec : Prop :=
  ∀ (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs) (H : http.HttpNet GF)
    (prt : GoInterface),
  bootCfgFresh cfg U → bootGo.bootURLsPlain U → crypto.fips140.GodebugFips140Off →
  bootGo.initMapOk U cfg.InitialClusterToken' →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      zapLoggerOk cfg.Logger' ∗ bootCfgRO cfg U ∗ http.roundTripperOk H prt }}
    (App (App (Val (@! bootstrapNewClusterNoWAL)) (Val #cfg)) (Val #prt))
  {{ (c : Loc) (err : GoInterface), RET (PairV #c #err);
      ⌜err ≠ GoInterface.nil⌝ ∨ ⌜err = GoInterface.nil⌝ ∗
      ∃ bc : bootstrappedCluster, c ↦ bc ∗
        ⌜bc.nodeID' = bootGo.id cfg U ∧ bc.remotes' = slice.nil ∧ bootGo.membersOk cfg U⌝ ∗
        clusterBuilt bc.cl' U cfg }}

end spec

end EtcdGrove
end Perennial
