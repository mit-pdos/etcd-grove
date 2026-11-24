/-
`(*config.ServerConfig).VerifyBootstrap()` (`config.go:207-221`) (claim #34, stage 2, 2026-11-25: translated with its body). Lean-first. The
configuration's fields are read through `p`, read-only (`↦□`), as the other `ServerConfig` specs.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.config.Defs
public import GeneratedProof.go_etcd_io.etcd.server.v3.config
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Base
public import Proof.net.http.Boundary

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **`c.VerifyBootstrap()`** (the configuration's URLs read-only, a zap logger; the initial
cluster's URLs at most `2^62` in all: `URLsMap.String`'s `sort.Strings`): an error, or the
configuration's name an entry of the initial cluster (`hasLocalMember`). -/
abbrev config.ServerConfig.VerifyBootstrap.spec : Prop :=
  ∀ (p : Loc) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (m : GMap GoString GoSlice)
    (urls : GoString → List _root_.Perennial.net.url.URL) (peer : List _root_.Perennial.net.url.URL),
  (m.domList.map (fun k => (urls k).length)).sum ≤ 2 ^ 62 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.config ∗ structFieldRef go_etcd_io.etcd.server.v3.config.ServerConfig go!"Name" p ↦□ cfg.Name' ∗ structFieldRef go_etcd_io.etcd.server.v3.config.ServerConfig go!"InitialPeerURLsMap" p ↦□ cfg.InitialPeerURLsMap' ∗
      structFieldRef go_etcd_io.etcd.server.v3.config.ServerConfig go!"PeerURLs" p ↦□ cfg.PeerURLs' ∗ structFieldRef go_etcd_io.etcd.server.v3.config.ServerConfig go!"Logger" p ↦□ cfg.Logger' ∗ structFieldRef go_etcd_io.etcd.server.v3.config.ServerConfig go!"DiscoveryCfg" p ↦□ cfg.DiscoveryCfg' ∗
      cfg.InitialPeerURLsMap' ↦$□ m ∗ ([∗map] k ↦ sl ∈ m, sl ↦*□ urls k) ∗ cfg.PeerURLs' ↦*□ peer ∗
      zapLoggerOk cfg.Logger' }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.config.ServerConfig.ty @!! go!"VerifyBootstrap")) (Val #()))
  {{ (err : GoInterface), RET #err;
      ⌜err ≠ GoInterface.nil ∨ err = GoInterface.nil ∧ (m.lookup cfg.Name').isSome⌝ }}

end spec

end EtcdGrove
end Perennial
