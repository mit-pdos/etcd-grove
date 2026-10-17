/-
`c.UpdateAuthToken(token)` (`client/v3/client.go`; new in PR etcd#21909). Lean-first (no Rocq
counterpart); see `Proof/go_etcd_io/etcd/client/v3/InvAuthToken.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvAuthToken

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `c.UpdateAuthToken(token)`, with the client's `Token` field owned and its `authTokenBundle`
a bundle (not nil: the client was built with a token or a user name and password), sets `Token`
to `token` (and hands the token to the bundle). The two premises are what the code needs: with a
`nil` bundle the call panics, and the write of `Token` needs the field exclusively, which the
retry interceptor's read-only share of it rules out (`retryClientOk_excl_token`). -/
abbrev Client.UpdateAuthToken.spec : Prop :=
  ∀ (c : Loc) (old token : GoString) (atb : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      structFieldRef go_etcd_io.etcd.client.v3.Client go!"Token" c ↦ old ∗
      structFieldRef go_etcd_io.etcd.client.v3.Client go!"authTokenBundle" c ↦□ atb ∗
      tokenBundleOk atb }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!! go!"UpdateAuthToken"))
      (Val #token))
  {{ RET #(); structFieldRef go_etcd_io.etcd.client.v3.Client go!"Token" c ↦ token }}

end spec

end EtcdGrove
end Perennial
