/-
`reqCtx(who)` (`examples/etcd/auth/etcd_auth.go`; the auth plan's E2f). Lean-first (no Rocq
counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth.ClientAuth
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_auth

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.auth.Assumptions]

/-- `reqCtx(who)` returns a request context and its `cancel`: a context a client call takes
(`ctxOk`, whose `Err()` returns client errors, `ctxErrClient`), derived from a timeout context
`c0` (`context.WithTimeout(context.Background(), RequestTimeout)`): `c0` itself, or for the bad
principal `c0` with `token: badtoken` appended to its outgoing metadata (contract C3,
`metadata.AppendToOutgoingContext`). `c0` has no outgoing metadata
(`context.WithTimeoutBackgroundMd.spec`; round 1 of `notes/authkv-main-plan.md`, F-W4: so `anon`'s calls
carry no token, and `bad`'s only `badtoken`). `cancel` is callable from anywhere. (errdesc stage 1,
2026-11-20) Its outgoing metadata is stated as the per-run relation `metadata.outMD` (until then the
pure `metadata.outgoingOf`). -/
abbrev reqCtx.spec : Prop :=
  ∀ [_root_.Perennial.errors.Assumptions] [_root_.Perennial.fmt.Assumptions]
    [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]
    (who : GoString),
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.auth }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.auth.reqCtx)) (Val #who))
  {{ (c : GoInterface) (cancel : GoFunc), RET (PairV #c #cancel);
      □ (∀ Φ : val → IProp GF, True -∗ ▷ (True -∗ Φ #()) -∗
        WP (App (Val #cancel) (Val #())) {{ Φ }}) ∗
      ∃ (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
        ⌜c = GoInterface.ok ci⌝ ∗ ctxOk ci cd ∗ ctxErrClient ci cd ∗
        metadata.outMD ci
          (if who = go!"bad" then metadata.mdAdd none go!"token" badToken else none) }}

end spec

end etcd_auth
end EtcdGrove
end Perennial
