/-
`reqCtx(who)` (`examples/authkv/authkv.go`; the auth plan's E2f). Lean-first (no Rocq
counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.authkv.ClientAuth
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authkv

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.authkv.Assumptions]

/-- `reqCtx(who)` returns a request context and its `cancel`: a context a client call takes
(`ctxOk`, whose `Err()` returns client errors, `ctxErrClient`), derived from a timeout context
`c0` (`context.WithTimeout(context.Background(), RequestTimeout)`): `c0` itself, or for the bad
principal `c0` with `token: badtoken` appended to its outgoing metadata (contract C3,
`metadata.AppendToOutgoingContext`). `cancel` is callable from anywhere. -/
abbrev reqCtx.spec : Prop :=
  ∀ [_root_.Perennial.errors.Assumptions] [_root_.Perennial.fmt.Assumptions]
    [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]
    [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)] [ContextErrsClient (GF := GF) (hG := hG)]
    (who : GoString),
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.authkv }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.authkv.reqCtx)) (Val #who))
  {{ (c : GoInterface) (cancel : GoFunc), RET (PairV #c #cancel);
      □ (∀ Φ : val → IProp GF, True -∗ ▷ (True -∗ Φ #()) -∗
        WP (App (Val #cancel) (Val #())) {{ Φ }}) ∗
      ∃ (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (c0 : GoInterface),
        ⌜c = GoInterface.ok ci⌝ ∗ ctxOk ci cd ∗ ctxErrClient ci cd ∗
        ⌜if who = go!"bad" then
            metadata.outgoingOf c = metadata.mdAdd (metadata.outgoingOf c0) go!"token" badToken
          else c = c0⌝ }}

end spec

end authkv
end EtcdGrove
end Perennial
