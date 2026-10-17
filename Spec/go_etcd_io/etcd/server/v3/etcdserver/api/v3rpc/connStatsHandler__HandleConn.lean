/-
`(*connStatsHandler).HandleConn` (`connstats.go`, pr-verify etcd#21621): grpc's stats handler,
called by grpc for each connection event. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvConnStats

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI google_golang_org.grpc

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`h.HandleConn(ctx, s)`**, on the handler `hs` (read-only), a context carrying the peer
`o` (`peer.inCtx`), with the TLS state `oti` if it is a TLS peer, and the connection event `s`: it observes one value in the cert-expiry
histogram (`Q f` for some `f`, the leaf certificate's remaining lifetime in seconds: time and
floats are outside the model, so any `f`) exactly when `connRecords s hs o oti` (a `ConnBegin`, a
TLS peer, a server that asks for client certificates, at least one sent), and nothing otherwise
(`P` back). It does not panic (the leaf is read only when there is one). -/
abbrev v3rpc.connStatsHandler.HandleConn.spec : Prop :=
  ∀ (h : Loc) (hs : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.connStatsHandler)
    (ctx s : GoInterface) (o : Option (Loc × peer.Peer)) (oti : Option credentials.TLSInfo)
    (P : IProp GF) (Q : w64 → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      ⌜v3rpc.connEventOk s⌝ ∗ h ↦□ hs ∗ □ EtcdGrove.peer.inCtx ctx o ∗ EtcdGrove.peer.ctxOwn o ∗ v3rpc.connTLSOk o oti ∗
      v3rpc.certExpHist P Q ∗ P }}
    (App (App (Val (h @!! go.GoType.PointerType
        go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.connStatsHandler.ty @!! go!"HandleConn"))
      (Val #ctx)) (Val #s))
  {{ RET #(); (⌜v3rpc.connRecords s hs o oti⌝ ∗ ∃ f : w64, Q f) ∨
      (⌜¬ v3rpc.connRecords s hs o oti⌝ ∗ P) }}

end spec

end EtcdGrove
end Perennial
