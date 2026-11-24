/-
`(*Client).Get` to a member at another machine, at its published view: a trust-boundary axiom until
#24's S2 (`notes/putget-dist-plan.md` §12). Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.ClientGetDist

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI Net

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **`(*Client).Get` to a member at another machine, at its published view** (trust boundary until
#24's S2; `notes/putget-dist-plan.md` §12). What it asserts of clientv3 v3.6 and grpc-go v1.84 (the
model) over the net extension, for a client that dials with **no proxy dial path** (`clientNoProxy`,
from `etcdstart.NewClient`'s post: `grpc.WithNoProxy()` in the client's configuration, so no
attempt goes through an HTTP `CONNECT` proxy named by `HTTPS_PROXY`; review F1, evidence
`TestProxyRogue` and `TestWithNoProxyFix`): as `Client_Put_dist.wp_proof`, each attempt's `Range`
reaches `ep`'s only acceptor, the member that published `ν` at `γE` (see `Client_Put_dist.wp_proof` on
review 4 and `bridge.New`'s fix). A `nil` result is that
member's linearizable read of `key` (no `serializable`, revision `0`) at a state after the put fired
(the flag at `1`), which the invariant says holds `val`.

Why it is true: it is `client.client_Get_own` (proved) at the member's `⟨ep, E, ρ.rd, cid, mid⟩`,
with `putGetInv_st` (`γr.kv.st = ν.st = ρ.rd.kv.st`), the free `committedAtLeast ρ.rd 0`
(`monoNatLbOwn_0`) and `kvLogLb E.γs []` (`kvLogLb_nil`). `kvRegsAt` is replaced by the address
fact and the published view.

Retired by #24's switch: `etcdAddrAt` gives `kvRegsPub ep γE mid` (`grpcSvcAt_of_addr`), and with
`envAt γE ν` that gives `kvRegsAt` at the client's own heap (#24's `kvRegsPub_at`, then a theorem),
then `client_Get_own`. The statement does not change. -/
axiom Client_Get_dist.wp_proof : Client_Get_dist.spec (GF := GF) (hG := hG)

end proof

end etcd_dist
end EtcdGrove
end Perennial
