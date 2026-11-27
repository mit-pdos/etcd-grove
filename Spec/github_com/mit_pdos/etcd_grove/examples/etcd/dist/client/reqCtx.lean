/-
`reqCtx(who)` (`examples/etcd/dist/client/authlease.go`; authlease's, copied): a request's context with the
request timeout, the bad principal's carrying its token. The single-process `etcd_authlease.reqCtx.spec`, its
metadata named `reqMd who` (`AuthLeaseDefs.lean`, with `outTokOk_reqMd`: the auth-on contracts' `outTokOk`).
Lean-first (no Rocq counterpart); F7 stage S4.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.AuthLeaseDefs
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Net client
open github_com.mit_pdos.etcd_grove.examples.etcd.dist

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]

/-- `reqCtx(who)` returns a request context and its `cancel`: a context a client call takes (`ctxOk`,
whose `Err()` returns client errors, `ctxErrClient`), whose outgoing metadata is `reqMd who` (none, or the
bad principal's `token: badtoken`). `cancel` is callable from anywhere. -/
abbrev reqCtx.spec : Prop :=
  ∀ [_root_.Perennial.errors.Assumptions] [_root_.Perennial.fmt.Assumptions]
    [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]
    (who : GoString),
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client }}
    (App (Val (@! client.reqCtx)) (Val #who))
  {{ (c : GoInterface) (cancel : GoFunc), RET (PairV #c #cancel);
      □ (∀ Φ : val → IProp GF, True -∗ ▷ (True -∗ Φ #()) -∗
        WP (App (Val #cancel) (Val #())) {{ Φ }}) ∗
      ∃ (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
        ⌜c = GoInterface.ok ci⌝ ∗ ctxOk ci cd ∗ ctxErrClient ci cd ∗ metadata.outMD ci (reqMd who) }}

end spec

end etcd_dist_client
end EtcdGrove
end Perennial
