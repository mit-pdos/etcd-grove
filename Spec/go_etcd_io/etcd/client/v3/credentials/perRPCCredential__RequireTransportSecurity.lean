/-
`(*perRPCCredential).RequireTransportSecurity()` (`client/v3/credentials/credentials.go`, names
only; the auth plan's C1, 2026-10-28; C1's review, F4). Lean-first (no Rocq counterpart); see
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

/-- `rc.RequireTransportSecurity()`: `false` (the credentials go over insecure connections too). -/
abbrev credentials.perRPCCredential.RequireTransportSecurity.spec : Prop :=
  ∀ (rc : Loc),
  {{ (True : IProp GF) }}
    (App (Val (rc @!! go.GoType.PointerType
      go_etcd_io.etcd.client.v3.credentials.perRPCCredential.ty @!! go!"RequireTransportSecurity"))
      (Val #()))
  {{ (b : Bool), RET #b; ⌜b = false⌝ }}

end spec

end EtcdGrove
end Perennial
