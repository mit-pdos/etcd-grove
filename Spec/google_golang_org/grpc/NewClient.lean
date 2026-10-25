/-
`grpc.NewClient(target, opts...)` (grpc's `clientconn.go`, names only; item 5, client construction): a
client connection, the producer of `grpcConn` (`Proof/google_golang_org/grpc/InvDial.lean`).
Lean-first (no Rocq counterpart).
-/
module

public import Proof.google_golang_org.grpc.InvDial

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

/-- **`grpc.NewClient(target, opts...)`** with dial options doing `ds` (`dialOptsAt`), whose stream
interceptors are etcd's and whose one resolver is `rb` (`dialOk`), which resolves the target's
scheme to the addresses `addrs` (`grpcResolverAt`, taken: the resolver's state is the connection's
from then on), returns a connection that reaches the servers at `addrs` (each attempt one of them) with the unary interceptor chain the
options set (`unaryIcsOf ds`: the last `WithUnaryInterceptor`'s) and no default call options
(`grpcConn`), or an error (an unparsable target, no transport credentials, ...). -/
abbrev grpc.NewClient.spec : Prop :=
  ∀ (target : GoString) (sl : GoSlice) (ds : List GrpcDialOpt) (rb : GoInterface)
    (scheme : GoString) (addrs : List GoString),
  dialOk ds rb →
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ dialOptsAt sl ds ∗
      grpcResolverAt rb scheme addrs ∗ ⌜(scheme ++ go!"://") <+: target⌝ }}
    (App (App (Val (@! google_golang_org.grpc.NewClient)) (Val #target)) (Val #sl))
  {{ (conn : Loc) (err : GoInterface), RET (PairV #conn #err);
      (⌜err = GoInterface.nil ∧ conn ≠ null⌝ ∗ grpcConn conn addrs (unaryIcsOf ds) []) ∨
        ⌜err ≠ GoInterface.nil⌝ }}

end spec

end EtcdGrove
end Perennial
