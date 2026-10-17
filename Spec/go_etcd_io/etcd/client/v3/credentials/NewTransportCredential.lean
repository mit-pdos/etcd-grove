/-
`credentials.NewTransportCredential(cfg)` (`client/v3/credentials`, names only; pr-verify etcd#21714: what `clientv3.newClient` calls. Lean-first (no Rocq counterpart)).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI


section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `credentials.NewTransportCredential(cfg)` returns some transport credentials (an interface value).
It reads the caller's `*tls.Config` (grpc's `NewTLS` clones it), which the model leaves opaque
(`crypto/tls` names only): the caller does not write it. -/
abbrev credentials.NewTransportCredential.spec : Prop :=
  ∀ (t : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.credentials }}
    (App (Val (@! go_etcd_io.etcd.client.v3.credentials.NewTransportCredential)) (Val #t))
  {{ (tc : google_golang_org.grpc.credentials.TransportCredentials), RET #tc; True }}

end spec

end EtcdGrove
end Perennial
