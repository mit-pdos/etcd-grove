/-
`(*config.ServerConfig).advertiseMatchesCluster()` (`config.go:249-298`; names only: it calls
`netutil.URLStringsEqual`, an untranslated package, `notes/bootstrap-proof-plan.md` §7.5 S3; not
proved, a hypothesis of the results that reach it (claim #34, stage 2, 2026-11-25: specified). Lean-first. The
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

/-- **`c.advertiseMatchesCluster()`** (the configuration's URLs read-only, a zap logger): some
error. Go: it sorts the advertised and the configured URLs of this member, compares them with
`netutil.URLStringsEqual` (resolving host names under a 30-second context) and formats the
difference into an error; it writes nothing the caller owns and does not panic on these values. -/
abbrev config.ServerConfig.advertiseMatchesCluster.spec : Prop :=
  ∀ (p : Loc) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (m : GMap GoString GoSlice)
    (urls : GoString → List _root_.Perennial.net.url.URL) (peer : List _root_.Perennial.net.url.URL),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.config ∗ structFieldRef go_etcd_io.etcd.server.v3.config.ServerConfig go!"Name" p ↦□ cfg.Name' ∗ structFieldRef go_etcd_io.etcd.server.v3.config.ServerConfig go!"InitialPeerURLsMap" p ↦□ cfg.InitialPeerURLsMap' ∗
      structFieldRef go_etcd_io.etcd.server.v3.config.ServerConfig go!"PeerURLs" p ↦□ cfg.PeerURLs' ∗ structFieldRef go_etcd_io.etcd.server.v3.config.ServerConfig go!"Logger" p ↦□ cfg.Logger' ∗ structFieldRef go_etcd_io.etcd.server.v3.config.ServerConfig go!"DiscoveryCfg" p ↦□ cfg.DiscoveryCfg' ∗
      cfg.InitialPeerURLsMap' ↦$□ m ∗ ([∗map] k ↦ sl ∈ m, sl ↦*□ urls k) ∗ cfg.PeerURLs' ↦*□ peer ∗
      zapLoggerOk cfg.Logger' }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.config.ServerConfig.ty @!! go!"advertiseMatchesCluster")) (Val #()))
  {{ (err : GoInterface), RET #err; True }}

end spec

end EtcdGrove
end Perennial
