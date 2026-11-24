/-
`etcdstart.Serve(s, a)` (`examples/lib/etcdstart`) on a member machine of a distributed deployment,
against the interim address fact (`notes/putget-dist-plan.md` §12; a trust-boundary axiom until
#24's S2: `Proof/.../etcd/dist/ServeDist.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.S2Interim
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Defs
public import Proof.google_golang_org.grpc.InvGrpc

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI Net go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **`Serve(s, a)` of a started member whose view is published, at an address set for it**
(see the axiom's docstring): from today's `Serve.spec` premises for a one-member start (the
logger, the method sets, the quota, the thread and receipt bounds, `grpcRepliesFit`, `srvLevels`),
the started member (`memberUp`, its member id `mid`), the address `a` set to serve etcd's KV calls
for `(γE, mid)` (`etcdAddrAt`) and the member's view published at `γE` (`envAt γE ν`, `ν` the
member's own, `memberView ρ`), `Serve` returns. -/
abbrev Serve_dist.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [ThreadBoundLe GF (2 ^ 28)] [ReceiptBoundLe GF (2 ^ 48)]
    [π : NetProtoGS] (s : Loc) (a : GoString) (ρ : ReqNames) (E₀ : apply.AEnv GF) (lg : Loc) (γn : NetNames GF)
    (mid : w64) (γE : GName) (ν : EnvView),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart ∗
      zapLoggerOk lg ∗
      ⌜v3rpc.ServerMethodSets ∧ apply.backendUnderQuota ∧ grpcRepliesFit ∧ srvLevels (GF := GF) ∧
        ν = memberView ρ⌝ ∗
      etcdstart.memberUp s ρ E₀ lg γn mid ∗
      etcdAddrAt (Gg := hG.goose_globalGS) a γE mid ∗ envAt (Gg := hG.goose_globalGS) γE ν }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Serve)) (Val #s))
      (Val #a))
  {{ (err : GoInterface), RET #err; True }}

end spec

end etcd_dist
end EtcdGrove
end Perennial
