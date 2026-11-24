/-
`Client(ep)` (`examples/etcd/dist/putget/putget.go`): the client machine's program of `putget_safe` -- a
client of the member's client address `ep` (`etcdstart.NewClient`), a `Put` of `k` with `v`, a `Get`
of `k`, a panic unless the `Get` returned `v`; an error from a step returns `false`. Lean-first (no Rocq
counterpart); `notes/putget-dist-plan.md` §12.

**The triple:** from the package's `isPkgInit` and the client's share of the distributed start over the
interim cross-machine vocabulary (`clientShare`: the member's client address set to serve etcd's KV
calls for the publication name `γE` and the member id `mid`, and the publication invariant at
`putgetPub`, what the member publishes with its view: the putget invariant at read names whose KV state
variable is the view's), `Client` does not panic. Its first call (`Put`) learns the member's view
(`etcd_dist.Client_Put_dist`), its second (`Get`) is at that view (`etcd_dist.Client_Get_dist`).

**The pure premises:** the endpoint plain (`clientv3.New`'s), the logic's thread bound
(`NewClient`'s), `errors.As`'s target `rpctypes.EtcdError` (the request contexts' errors,
`client.wp_WithTimeout_bg`), as the in-process putget's `Main` (`Spec/.../examples/etcd/putget/Main.lean`).
No thread token: the client forks nothing.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.Defs
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx
public import Proof.go_etcd_io.etcd.client.v3.InvClientNew

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_putget_dist

open Iris Iris.BI Net

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.Assumptions]

/-- See the file header. -/
abbrev Client.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)]
    [ContextErrsClient (GF := GF) (hG := hG)] [π : NetProtoGS]
    (client : GoString) (γE : GName) (mid : w64),
  plainEndpoint client → threadBound GF ≤ 2 ^ 31 →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget ∗
      clientShare (G := hG.goose_globalGS) client γE mid (putgetPub (G := hG.goose_globalGS)) }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.Client)) (Val #client))
  {{ (b : bool), RET #b; True }}

end spec

end etcd_putget_dist
end EtcdGrove
end Perennial
