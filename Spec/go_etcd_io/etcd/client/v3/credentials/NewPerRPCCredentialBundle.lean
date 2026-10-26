/-
`credentials.NewPerRPCCredentialBundle()` (`client/v3/credentials/credentials.go`; the auth plan's
E2d). Lean-first (no Rocq counterpart); see `Proof/go_etcd_io/etcd/client/v3/credentials/Defs.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.credentials.Defs

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
variable [package_sem : go_etcd_io.etcd.client.v3.credentials.Assumptions]

/-- `NewPerRPCCredentialBundle()`: a token bundle (`tokenBundleAt`). -/
abbrev credentials.NewPerRPCCredentialBundle.spec : Prop :=
  {{ True }}
    (App (Val (@! go_etcd_io.etcd.client.v3.credentials.NewPerRPCCredentialBundle)) (Val #()))
  {{ (atb : GoInterface), RET #atb; tokenBundleAt (GF := GF) atb }}

end spec

end EtcdGrove
end Perennial
