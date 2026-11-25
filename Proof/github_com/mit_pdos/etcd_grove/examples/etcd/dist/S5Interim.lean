/- Lean-first (no Rocq counterpart).

# Interim peer transport for etcd's distributed theorems (until phase 7 S5 across machines)

`notes/etcd-dist-plan.md`, "Interim transport". A member's peer address (its one peer URL `http://a`, served by
etcd's peer handler, dialed by the other members' rafthttp and leasehttp round trippers) is set by the deployment's
start to the opaque peer protocols `httpPeerSvc` (`httpAddrAt a`), as S2's interface sets a client address to
grpc's opaque `grpcCliPI`/`grpcSrvPI` (`grpcAddrAt`). With it:
* `http_addr_set` is a theorem (`addr_set_proto`). `S5Draft`'s unindexed `httpAddrAt` is not instantiated: the
  protocol is indexed by the cluster and the member (`httpPeerSvc γ.cl id`), so `S5Draft` must gain those indices
  before its fields are these (`notes/etcd-dist-plan.md` §17.3);
* the member-side axioms are `NewServer_dist` (`etcdserver.NewServer` with the network across machines),
  `NewPeerHandler_dist` and `PeerServe_dist` (etcd's peer handler served on the member's peer listener);
* `noProxyEnv`: the member's process has no HTTP proxy variable set (four `osEnvIs k ""`), which `NewServer_dist`
  takes: the program checks the variables first (`examples/etcd/dist/server`'s `proxyEnvSet`).

The protocols are opaque: no proof can establish `httpPeerSvc`'s dialer protocol of any bytes, nor its acceptor
protocol, so no program but the member-side axioms' (the transport inside `NewServer_dist`, the server inside
`PeerServe_dist`) writes on a connection to a peer address; a program holding `httpAddrAt a` may dial, listen
(`listen_au`) and accept at `a`, and can write nothing there through the net extension. (Two other routes reach a
peer address, found by the 2026-11-24 review, `notes/etcd-dist-plan.md` §17.3: the names-only
`leasehttp.RenewHTTP` axiom, any URL, still open; and the single-process HTTP registry, `httpProtoFree`/`http.reserve`,
which the one-process start hands out beside `addrUnset`: closed: `http.reserve` takes the address's net protocols as
net/http's, `httpAddrNet`, whose producer `httpAddrFree_set` spends the pending set, which `http_addr_set` needs too.) Defined here: no axiom.
-/
module

public import GooseLang.Ext.Net.Proto
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SrvRaftLog
public import Proof.os.EnvIs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI Net

/-! ## The peer protocols -/

/-- **What is written on a connection to a member's peer address** (opaque; trusted text with no law, as grpc's
`grpcCliPI`/`grpcSrvPI`): the dialer's protocol (`.1`, what etcd's rafthttp and leasehttp round trippers write: HTTP/1.1
requests of etcd's peer API, from a member of the deployment's cluster) and the acceptor's (`.2`, what etcd's peer
handler served by net/http writes back). Its intended reading, S5's: the HTTP protocols of etcd's peer API, each
request carrying raft's message invariant (the in-process network's `raftProto`). Opaque so that no program but the
member-side axioms writes or learns anything of such a connection. (2026-11-25, the review of
`bootstrap.wp_proof_dist`) The dialer's requests include `bootstrap`'s `GET /members` (`isMemberBootstrapped`,
before the member is a started server: read-only, no raft message), which etcd's peer handler answers with its
cluster's members (`etcdhttp/peer.go:112-120`); `bootstrap.wp_proof_dist` relies on that answer being etcd's
(a `null` element would panic it). **Indexed by the cluster `cl` (raft's cluster names, allocated once per cluster)
and the address's member `id`** (the 2026-11-24 review of `NewServer_dist`: unindexed, a second ghost cluster with the
same configuration could use the same addresses, and a duplicate member panics raft, `tocommit out of range`): an
address is set once (`addrUnset` is spent), so only one cluster's members, and only the member `id`, are at it.
(2026-11-25, N5, `notes/etcd-dist-plan.md` §19: by the cluster, not the member's whole `SrvRaft` record, which
holds the member's own storage registry `reg`: every member reads the other members' addresses at its own record, so
an index by the record could not be met at three members; `notes/axiom-review/s5-cluster-index.md`.) -/
opaque httpPeerSvc [GooseExts] {GF : BundledGFunctors} (cl : Cluster) (id : w64) :
    Proto GF × Proto GF := (fun _ _ => iprop(True), fun _ _ => iprop(True))

section addr
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **The peer address `a` is member `id`'s of the cluster of the server raft `γ` and serves etcd's peer API**
(persistent, no heap): `a`'s protocols are `httpPeerSvc γ.cl id`'s (by `γ`'s cluster only: two members' records,
which differ in their storage registries, read the same fact). -/
def httpAddrAt (γ : SrvRaft) (id : w64) (a : GoString) : IProp GF :=
  addrProto (Gg := Gg) a (httpPeerSvc (GF := GF) γ.cl id).1 (httpPeerSvc (GF := GF) γ.cl id).2

instance httpAddrAt_persistent (γ : SrvRaft) (id : w64) (a : GoString) :
    Persistent (httpAddrAt (Gg := Gg) γ id a) := by
  unfold httpAddrAt; infer_instance

/-- **The start law**: the deployment's start sets an unset address (`addrUnset a`, spent) to serve etcd's peer
API (`addr_set_proto`). -/
theorem http_addr_set (E : CoPset) (γ : SrvRaft) (id : w64) (a : GoString) :
    ⊢ regCtx (Gg := Gg) -∗ addrUnset (Gg := Gg) a ={E}=∗ httpAddrAt (Gg := Gg) γ id a := by
  iintro #Hreg Hu
  unfold httpAddrAt
  iapply addr_set_proto E a _ _ $$ Hreg Hu

end addr

/-! ## No HTTP proxy -/

section env
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

/-- The variables net/http's `ProxyFromEnvironment` reads a proxy from (`golang.org/x/net/http/httpproxy`'s
`FromEnvironment`: `HTTP_PROXY` or `http_proxy` for `http` URLs, `HTTPS_PROXY` or `https_proxy` for `https` ones;
`NO_PROXY` and `REQUEST_METHOD` only turn a proxy off). -/
def proxyEnvKeys : List GoString :=
  [go!"HTTP_PROXY", go!"http_proxy", go!"HTTPS_PROXY", go!"https_proxy"]

/-- **This process uses no HTTP proxy** (persistent): each proxy variable is unset or empty for the run
(`osEnvIs k ""`, from the program's own check through `os.Getenv.specEnv`). Go evidence:
`examples/etcd/dist/server`'s `TestProxyEnvSet` (with the four empty, `httpproxy.FromEnvironment` proxies no peer
URL; with each one set, it proxies the peer URL of its scheme). -/
def noProxyEnv : IProp GF := iprop([∗list] k ∈ proxyEnvKeys, osEnvIs (hG := hG) k go!"")

instance noProxyEnv_persistent : Persistent (noProxyEnv (hG := hG)) := by
  unfold noProxyEnv; infer_instance

end env

/-! ## `bootstrap`'s round tripper -/

section bootrt
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [π : NetProtoGS]

/-- **What `bootstrap`'s round tripper needs of the other members' peer URLs** (persistent; the round-tripper
contract of the interim `bootstrap.wp_proof_dist`): every other peer `pid` of the cluster `γ` (not `id`) whose
directory entry is `http://a` has its address `a` set to etcd's peer protocols of `γ` and `pid` (`httpAddrAt`), and
this process uses no HTTP proxy (`noProxyEnv`). `bootstrap` (`bootstrap.go:72`, `rafthttp.NewRoundTripper`)
makes the round tripper with which `isMemberBootstrapped` (`cluster_util.go:41`) sends `GET <url>/members` to each
other member's peer URL. Exactly `NewServer.specG_dist`'s `#Hpeers ∗ #Hnoproxy`, so the S5 interim axioms'
callers discharge it; S5's proof of net/http across machines is to replace it by the client contract it proves. -/
def bootRTOk (γ : SrvRaft) (id : w64) (dir : w64 → List GoString) : IProp GF :=
  iprop((□ ∀ (pid : w64) (a : GoString), ⌜pid ∈ γ.vs ∧ pid ≠ id ∧ go!"http://" ++ a ∈ dir pid⌝ -∗
      httpAddrAt (Gg := hG.goose_globalGS) γ pid a) ∗ noProxyEnv (hG := hG))

instance bootRTOk_persistent (γ : SrvRaft) (id : w64) (dir : w64 → List GoString) :
    Persistent (bootRTOk (hG := hG) γ id dir) := by
  unfold bootRTOk; infer_instance

end bootrt

/-! ## The peer handler -/

section handler
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]

/-- The trusted text of `peerHandlerOf` (opaque, no law). -/
opaque peerHandlerRaw (hh : HeapGS HasLC.hasLC GF) (h : GoInterface) (s : Loc) : IProp GF := iprop(True)

/-- **`h` is etcd's peer handler of the server `s`** (persistent, of one process): what
`etcdhttp.NewPeerHandler(lg, s)` returned (`NewPeerHandler_dist`), what `PeerServe_dist` serves. -/
def peerHandlerOf (h : GoInterface) (s : Loc) : IProp GF := iprop(□ peerHandlerRaw hG h s)

instance peerHandlerOf_persistent (h : GoInterface) (s : Loc) :
    Persistent (peerHandlerOf (hG := hG) h s) := by
  unfold peerHandlerOf; infer_instance

end handler

end etcd_dist
end EtcdGrove
end Perennial

end
