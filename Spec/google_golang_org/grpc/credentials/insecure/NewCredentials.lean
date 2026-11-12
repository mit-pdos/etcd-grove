/-
`insecure.NewCredentials()` (grpc's `credentials/insecure`, names only; item 5). Lean-first.
-/
module

public import Proof.google_golang_org.grpc.InvDial
public import Proof.go_etcd_io.etcd.cache.v3.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `insecure.NewCredentials()`: some transport credentials (grpc's `insecureTC{}`). -/
abbrev insecure.NewCredentials.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.credentials.insecure }}
    (App (Val (@! google_golang_org.grpc.credentials.insecure.NewCredentials)) (Val #()))
  {{ (c : GoInterface), RET #c; True }}

end spec

end EtcdGrove
end Perennial
