/-
`bootstrapCluster(cfg, bwal, prt)` (`bootstrap.go:330-345` at the etcd pin `edc800c6f`, through
`bootstrapNewClusterNoWAL`, `:379-414`; names-only, a callee of `bootstrap`'s proof, `?` in the
server's link until stage 2 proves it). Lean-first; claim #34, stage 3 (2026-11-23),
`notes/bootstrap-proof-plan.md` §7.3. Its vocabulary: `Proof/.../etcdserver/BootParts.lean`
(`clusterBuilt`) and `BootValues.lean` (`bootGo`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BootParts

@[expose] public section

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

/-- **`bootstrapCluster(cfg, nil, prt)` at a first start of a new cluster**: for a configuration
`bootCfgFresh` covers (`NewCluster`, no discovery) whose initial cluster's URLs are plain
(`bootGo.bootURLsPlain`, where `URL.String()` is `bootGo.urlStr`), with its URLs read-only
(`bootCfgRO`), a zap logger and a round tripper of some network `H` (`rafthttp.NewRoundTripper`'s
post): an error, or the record `bc` with this member's id `bootGo.id` (`bootOk`'s `Hid`), no remotes
(`Hrms Hrmsi Hrms0`), the initial cluster's facts (`bootGo.membersOk`), and the cluster as
`NewClusterFromURLsMap` leaves it (`clusterBuilt`: owned field by field, not yet shared).

Why it is true of Go: `bwal == nil && cfg.NewCluster` (`:334`) calls `bootstrapNewClusterNoWAL`.
`VerifyBootstrap()` (`config.go`) errors unless the configuration's name is an entry
(`hasLocalMember`) and the URLs are consistent; `NewClusterFromURLsMap` (`cluster.go:79-94`) builds
`NewCluster`'s literal and one `NewMember(name, urls, token, nil)` per entry (`computeMemberID`, so the
ids are `bootGo.memberID` of the URLs' strings, which for plain URLs are `bootGo.urlStr`), erroring on
a repeated or zero id (so on success `membersOk`), and `genID()` sets `cid` to `bootGo.cid`;
`MemberByName(cfg.Name)` (`:387`) is the configuration's entry, so `m.ID` is `bootGo.id`;
`isMemberBootstrapped` (`:388`) GETs the other members' `/members` through `prt` and errors if one
answers with this member already in it; `ShouldDiscover()` is false (`bootCfgFresh`). The record
`&bootstrappedCluster{remotes: nil, cl, nodeID: m.ID}` (`:409-413`). -/
abbrev bootstrapCluster.spec : Prop :=
  ∀ (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs) (H : http.HttpNet GF)
    (prt : GoInterface),
  bootCfgFresh cfg U → bootGo.bootURLsPlain U →
  -- (claim #34, stage 2, 2026-11-25, the ledger's entry of that date) `crypto/sha1.Sum`'s environment
  -- premise, and the initial cluster's ids distinct (`NewClusterFromURLsMap`'s)
  crypto.fips140.GodebugFips140Off → bootGo.initMapOk U cfg.InitialClusterToken' →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      zapLoggerOk cfg.Logger' ∗ bootCfgRO cfg U ∗ http.roundTripperOk H prt }}
    (App (App (App (Val (@! bootstrapCluster)) (Val #cfg)) (Val #(null : Loc))) (Val #prt))
  {{ (c : Loc) (err : GoInterface), RET (PairV #c #err);
      ⌜err ≠ GoInterface.nil⌝ ∨ ⌜err = GoInterface.nil⌝ ∗
      ∃ bc : bootstrappedCluster, c ↦ bc ∗
        ⌜bc.nodeID' = bootGo.id cfg U ∧ bc.remotes' = slice.nil ∧ bootGo.membersOk cfg U⌝ ∗
        clusterBuilt bc.cl' U cfg }}

end spec

end EtcdGrove
end Perennial
