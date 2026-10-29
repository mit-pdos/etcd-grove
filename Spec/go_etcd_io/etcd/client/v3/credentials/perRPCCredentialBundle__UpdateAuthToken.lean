/-
`(*perRPCCredentialBundle).UpdateAuthToken(token)` (`client/v3/credentials/credentials.go`; the
auth plan's C1, 2026-10-28). Lean-first (no Rocq counterpart); see
`Proof/go_etcd_io/etcd/client/v3/credentials/Defs.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.credentials.Defs

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
variable [package_sem : go_etcd_io.etcd.client.v3.credentials.Assumptions]

/-- `b.UpdateAuthToken(t)` on a token bundle whose tokens are `""` or meet `P`
(`tokenBundleInv`), with `t` `""` or meeting `P`: it returns. -/
abbrev credentials.perRPCCredentialBundle.UpdateAuthToken.spec : Prop :=
  ∀ (b : Loc) (P : GoString → IProp GF) (t : GoString),
  {{ tokenBundleInv (GF := GF) (interface.mkOk (go.GoType.PointerType
        go_etcd_io.etcd.client.v3.credentials.perRPCCredentialBundle.ty) #b) P ∗
      (⌜t = go!""⌝ ∨ □ P t) }}
    (App (Val (b @!! go.GoType.PointerType
      go_etcd_io.etcd.client.v3.credentials.perRPCCredentialBundle.ty @!! go!"UpdateAuthToken"))
      (Val #t))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
