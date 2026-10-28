/-
`(*perRPCCredential).GetRequestMetadata(ctx, s...)` (`client/v3/credentials/credentials.go`, names
only; the auth plan's C1, 2026-10-28). Lean-first (no Rocq counterpart); see
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

/-- `rc.GetRequestMetadata(ctx, s...)` on credentials whose token is `""` or meets `P`
(`credTokInv`): no error, and a map whose metadata meets `tokMdOk P` (`nil` for `""`, else
`{"token": t}`). -/
abbrev credentials.perRPCCredential.GetRequestMetadata.spec : Prop :=
  ∀ (rc : Loc) (P : GoString → IProp GF) (ctx : GoInterface) (sl : GoSlice),
  {{ credTokInv (GF := GF) rc P }}
    (App (App (Val (rc @!! go.GoType.PointerType
      go_etcd_io.etcd.client.v3.credentials.perRPCCredential.ty @!! go!"GetRequestMetadata"))
      (Val #ctx)) (Val #sl))
  {{ (mp : Loc) (err : GoInterface), RET (PairV #mp #err);
      ⌜err = GoInterface.nil⌝ ∗ ∃ cm, credsMapIs mp cm ∗ tokMdOk P cm }}

end spec

end EtcdGrove
end Perennial
