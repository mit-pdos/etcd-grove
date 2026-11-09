/-
# `server/lease/leasehttp`: vocabulary (batch 2e)

The lease HTTP endpoints a follower forwards to the leader (`RenewHTTP`; `TimeToLiveHTTP` is
reached only through 2c's names-only `leaseTimeToLive` and has no spec here). Trusted (names only).

* `rtOk rt` (persistent): `rt` is an `http.RoundTripper` that may be used from any goroutine
  (`rafthttp.NewRoundTripper`'s, the server's `peerRt`). Integration (I5): no longer provisional:
  it is the `net/http` boundary's `Http.roundTripperOk rt` (`Spec/net/http/Api.lean`), which
  `rafthttp.NewRoundTripper.spec` gives (the name kept as an abbreviation).
-/
module

public import Spec.context.Api
public import Spec.net.http.Api
public import GeneratedProof.go_etcd_io.etcd.server.v3.lease.leasehttp
public import Spec.PkgInit.go_etcd_io.etcd.server.v3.lease.leasehttp

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Leasehttp

open Iris Iris.BI

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- `rt` is a usable `http.RoundTripper` (persistent): `net/http`'s `Http.roundTripperOk`. -/
abbrev rtOk (rt : GoInterface) : IProp GF := Http.roundTripperOk rt

def rtOk_persistent.spec : Prop := ∀ rt, Persistent (rtOk (GF := GF) rt)

end res

end Leasehttp
end EtcdGrove
end Perennial
