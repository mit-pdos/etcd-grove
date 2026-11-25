/-
`newStreamRoundTripper(tlsInfo, dialTimeout)` (`util.go`; rafthttp stage 6c, `Transport.Start`'s
round trippers): translated and proved over `transport.NewTimeoutTransport`'s spec since rafthttpfix
(2026-11-20; until then the trust boundary, the HTTP boundary's, D39). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply
public import Proof.net.http.Boundary
public import GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp
public import Proof.go_etcd_io.etcd.client.pkg.v3.transport.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`newStreamRoundTripper(tlsInfo, dialTimeout)`** (the streams' round tripper): an error, or a round tripper of
any network `H` (`http.roundTripperOk`), for a `TLSInfo` with no certificate (`transport.tlsEmpty`,
`NewTimeoutTransport`'s premise, 2026-11-25). -/
abbrev rafthttp.newStreamRoundTripper.spec : Prop :=
  ∀ (H : http.HttpNet GF) (tls : go_etcd_io.etcd.client.pkg.v3.transport.TLSInfo) (dt : w64),
  transport.tlsEmpty tls →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp }}
    (App (App (Val (@! rafthttp.newStreamRoundTripper)) (Val #tls)) (Val #dt))
  {{ (rt err : GoInterface), RET (PairV #rt #err);
      ⌜err ≠ GoInterface.nil⌝ ∨ ⌜err = GoInterface.nil⌝ ∗ http.roundTripperOk H rt }}

end spec

end EtcdGrove
end Perennial
