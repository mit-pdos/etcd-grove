/-
**The interim bootstrap axiom at a first start in one process, no other member's peer address served**
(2026-11-27): `bootstrap(cfg)`'s spec at a first start of a member whose initial cluster has one peer URL per entry,
the other members in the same process and none of them serving its peer address yet
(`Spec/.../etcdserver/bootstrapUnserved.lean`). It replaces the Iris premise `Hprem₅` of
`etcd_restart_robust_single_process` (restartN's first-start contracts, `bootstrapContract` inside
`etcdstart.bootPremise`): restartN's members derive their contracts from it (`etcdstart.bootPremiseF_of_specUnserved`).
**Interim: retired when #34 proves `bootstrap`** at these clusters (its restated spec, with what
`isMemberBootstrapped`'s GETs need), as `bootstrap.specDist` and `bootstrap.specOne` retire.

**Why an axiom and not a theorem.** As `bootstrap.wp_proof_dist`'s (`bootstrapDist.lean`): `bootstrap`'s Go is
translated with its body and #34 proves it over its callees' specs, but at `bootstrap.spec`, which gives
`isMemberBootstrapped`'s GETs no right; their failure at unserved addresses is not proved yet (no spec of the HTTP
client at an address no server is registered at).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.bootstrapUnserved

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [MemStorReg GF]

/-- **Interim trust boundary: `bootstrap(cfg)` at a first start, no other member's peer address served**
(`bootstrap.specUnserved`; interim, retired when #34 proves `bootstrap`). Until 2026-11-27 its content was the
closed theorem's Iris premise `Hprem₅` (restartN's first-start contracts); it is `bootstrap.spec` at `bootstrap.specDist`'s
shape, with the other members' peer addresses' rights lent for the call.

Why it is true of Go (at the etcd pin `d26dd5da6`, `server/etcdserver/`): it is `bootstrap.wp_proofOne`'s first start
(`bootstrapOne.lean`) but for `isMemberBootstrapped` (`bootstrap.go:388`). That sends, through the round tripper
`bootstrap` makes fresh (`bootstrap.go:72`, `rafthttp.NewRoundTripper`: no pooled connection), `GET <url>/members` to
each other member's peer URL (`cluster_util.go:41-55`, `:69-121`, `getRemotePeerURLs` `:131-141`: the URLs of the
members of another name, here `http://a` with `a ∈ addrs`), and answers `false` on any error, the one-member answer. Each
GET fails:
* no HTTP server answers at `a`: one is registered only by `http.register`, which takes the listener's
  `netListenerAt`, holding `addrClaim a`, which the caller lends here for the whole call;
* no raw listener at `a` answers: one may listen at `a` without the claim (`listen_au`), but `a`'s net protocols are
  net/http's opaque `httpNetCliP`/`httpNetSrvP` (`httpAddrNet a`), so it writes nothing a client reads; the GET then
  ends in an error (refused, EOF, or the client's timeout `BootstrapTimeoutEffective`, 1s by default,
  `config/config.go:345-350`);
* no proxy: `addrClaim` is given only at program start, for numeric loopback addresses (`goose_adequacy_start`,
  `hAsLit`, `Proof/runtime/Start.lean`), which `http.ProxyFromEnvironment` (`client/pkg/transport/transport.go:42`)
  never proxies; no other process binds them (`addrsUnclaimed`).
Go evidence: `examples/etcd/restartN`'s `TestRun` probes every peer address at each first boot (`bootstrapping
cluster`, logged right before `bootstrapCluster`) and finds none accepting; with the members served in between (the
example before 2026-11-27) it finds them. -/
axiom bootstrap.wp_proofUnserved : bootstrap.specUnserved (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
