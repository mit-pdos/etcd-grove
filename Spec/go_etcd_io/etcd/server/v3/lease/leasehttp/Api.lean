/-
# `server/lease/leasehttp`: vocabulary (batch 2e)

The lease HTTP endpoints a follower forwards to the leader (`RenewHTTP`; `TimeToLiveHTTP` is
reached only through 2c's names-only `leaseTimeToLive` and has no spec here). Trusted (names only).

* `rtOk rt` (persistent): **provisional (the `net/http` boundary, 2a's/2f's)**: `rt` is an
  `http.RoundTripper` that may be used from any goroutine (`rafthttp.NewRoundTripper`'s, the
  server's `peerRt`).
-/
module

public import Spec.context.Api
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
variable [go_gctx : GoGlobalContext]

/-- **Provisional (`net/http`):** `rt` is a usable `http.RoundTripper` (persistent). -/
opaque rtOk (rt : GoInterface) : IProp GF := iprop(True)

def rtOk_persistent.spec : Prop := ∀ rt, Persistent (rtOk (GF := GF) rt)

end res

end Leasehttp
end EtcdGrove
end Perennial
