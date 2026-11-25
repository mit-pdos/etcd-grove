/-
`Client(ep)` (`examples/etcd/dist/putgetk/putgetk.go`): unless `ep` is a valid address (`AddrOK`), it returns
`false` at once; else putget's client (`putget.Client(ep)`: a `Put` of `k` with `v`, a `Get` of `k`, a panic
unless the `Get` returned `v`). Lean-first (no Rocq counterpart).

**The triple:** from, if `ep` is not empty, putget's client share at `ep` (`clientShare`: the address fact
of the member serving `ep`, `mid`, and its publication invariant at `putgetPub`) and `ep` a plain endpoint,
it returns (putget's `Client.spec` otherwise).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.Client
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_putgetk_dist

open Iris Iris.BI Net etcd_putget_dist

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.Assumptions]

/-- See the file header. -/
abbrev Client.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)]
    [ContextErrsClient (GF := GF) (hG := hG)] [ThreadBoundLe GF (2 ^ 31)] [π : NetProtoGS]
    (ep : GoString) (γE : GName) (mid : w64),
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk ∗
      (⌜ep ≠ []⌝ -∗ ⌜plainEndpoint ep⌝ ∗
        clientShare (G := hG.goose_globalGS) ep γE mid (putgetPub (G := hG.goose_globalGS))) }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.Client)) (Val #ep))
  {{ (b : Bool), RET #b; True }}

end spec

end etcd_putgetk_dist
end EtcdGrove
end Perennial

end
