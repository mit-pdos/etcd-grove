/-
`(*perRPCCredential).GetRequestMetadata(ctx, s...)` (`client/v3/credentials/credentials.go`; the
auth plan's C1, 2026-10-28; with its body since 2026-11-24). Lean-first (no Rocq counterpart); see
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
`{"token": t}`). It does not read `ctx` (`credentials.go:69-77`: it reads the token under the
credential's lock and builds the map; premise-fixes-7 corrected premise-fixes-5's list, which
counted it among the axioms reading `ctx.Value`), so it takes any context. The caller lends it a
level-0 thread token (`levelTok 0`, given back; prove-ps2-clientrdlock, 2026-11-24, decision 1b),
with which it borrows a reader slot of the credentials' lock (`credTokInv`'s pool): grpc lends it
its caller's (`perRPCCredsOk pc clientRes`). -/
abbrev credentials.perRPCCredential.GetRequestMetadata.spec : Prop :=
  ∀ (rc : Loc) (P : GoString → IProp GF) (ctx : GoInterface) (sl : GoSlice),
  {{ credTokInv (GF := GF) rc P ∗ levelTok 0 }}
    (App (App (Val (rc @!! go.GoType.PointerType
      go_etcd_io.etcd.client.v3.credentials.perRPCCredential.ty @!! go!"GetRequestMetadata"))
      (Val #ctx)) (Val #sl))
  {{ (mp : Loc) (err : GoInterface), RET (PairV #mp #err);
      levelTok 0 ∗ ⌜err = GoInterface.nil⌝ ∗ ∃ cm, credsMapIs mp cm ∗ tokMdOk P cm }}

end spec

end EtcdGrove
end Perennial
