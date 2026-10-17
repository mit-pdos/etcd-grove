/-
`peer.FromContext(ctx)` (grpc's `peer` package, with its body since PR etcd#22259: the server's
log interceptor reads the run's peer). Lean-first (no Rocq counterpart).
-/
module

public import Proof.google_golang_org.grpc.InvGrpc

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [peer_sem : google_golang_org.grpc.peer.Assumptions]

/-- `peer.FromContext(ctx)` of a context with the run's peer at `o` (`grpcRunPeerIs`): `(p, ok)`,
with `ok` false if there is none, else `ok` and `p` the non-nil peer grpc wrote, at the address
(`grpcPeerIs`). -/
abbrev peer.FromContext.spec : Prop :=
  ∀ (ci : GoInterfaceOk) (o : Option GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.peer ∗ grpcRunPeerIs ci o }}
    (App (Val (@! google_golang_org.grpc.peer.FromContext)) (Val #(GoInterface.ok ci)))
  {{ (p : Loc) (ok : Bool), RET (PairV #p #ok);
      match o with
      | none => ⌜ok = false⌝
      | some s => ⌜ok = true ∧ p ≠ null⌝ ∗ grpcPeerIs p s }}

end spec

end EtcdGrove
end Perennial
