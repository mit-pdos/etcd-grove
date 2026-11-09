/-
`(*credentials.perRPCCredential).GetRequestMetadata` (`client/v3/credentials/credentials.go`).

Users: grpc (each attempt's metadata, 2a: the token the server authenticates).

Proof sketch: `authTokenMu.RLock` (a reader slot of the credentials' own lock; see the margin),
the token read, `RUnlock`; `""`: `nil`; else a fresh map `{"token": tok}`.

Changes: from `specs-ref`.

Margin: the read lock's reader slots are the credentials' own (its invariant), not counted at the
caller (PRINCIPLES, "a bound is reasoned about where it is owned").
-/
module

public import Spec.go_etcd_io.etcd.client.v3.credentials.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Credentials

open Iris Iris.BI EtcdModel ClientV3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.credentials.Assumptions]

/-- `rc.GetRequestMetadata(ctx, uri...)`: no metadata, or `{"token": tok}` of a token `who` may
send. -/
def perRPCCredential.GetRequestMetadata.spec : Prop :=
  ∀ (rc : Loc) (γ : Cluster) (who : Principal) (ctx : GoInterface) (s : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.credentials ∗ rpcCredsAt (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.credentials.perRPCCredential.ty) #rc) γ who }}
    (App (App (Val (rc @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.credentials.perRPCCredential.ty @!! go!"GetRequestMetadata")) (Val #ctx)) (Val #s))
  {{ (m : Loc) (err : GoInterface), RET (PairV #m #err); ⌜err = GoInterface.nil⌝ ∗
      (⌜m = null⌝ ∨ ∃ tok, ⌜tok ≠ []⌝ ∗ tokenMd m tok ∗ tokFor γ who tok) }}

end spec

end Credentials
end EtcdGrove
end Perennial
