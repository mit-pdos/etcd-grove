/-
## `NewRoundTripper(tlsInfo, dialTimeout)`

**Users.** `Transport.Start`, etcd's `bootstrap` (`server/etcdserver/bootstrap.go:72`, a round tripper for fetching the cluster).

**Proof sketch.** Assumed: Go's `*http.Transport` meets the HTTP boundary's `RoundTrip` contract (`Http.roundTripperOk`); the TLS configuration may fail.

**Changes.** New (no old spec; was a names-only call inside the `Start` axiom).

**Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Rafthttp

open Iris Iris.BI Raft
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- (trust boundary: untranslated; `transport.NewTimeoutTransport`) **A round tripper** (an `*http.Transport`, or a TLS error). -/
def NewRoundTripper.spec : Prop :=
  ∀ (tls : go_etcd_io.etcd.client.pkg.v3.transport.TLSInfo) (d : _root_.Perennial.time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ True }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.NewRoundTripper)) (Val #tls)) (Val #d))
  {{ (rt : GoInterface) (err : GoInterface), RET (PairV #rt #err); (⌜err ≠ interface.nil⌝ ∗ Http.errOk err) ∨ (⌜err = interface.nil⌝ ∗ Http.roundTripperOk rt) }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
