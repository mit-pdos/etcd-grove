/-
`etcdstart.Serve(s, a)` (`examples/lib/etcdstart`) on a member machine of a distributed deployment,
against the interim address fact (`notes/putget-dist-plan.md` §12; a trust-boundary axiom until
#24's S2: `Proof/.../etcd/dist/ServeDist.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.S2Interim
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Defs
public import Proof.google_golang_org.grpc.InvGrpc
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.MemberLessor

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

/-- **`Serve(s, a)` of a started member of the view `Γ`, at an address set for it** (see the axiom's
docstring): from today's `Serve.spec` premises for a one-member start (the logger, the method sets, the
quota, the thread and receipt bounds, `grpcRepliesFit`, `srvLevels`), the started member (`memberUp`, its
member id `mid`) whose KV names agree with the view's (`kvCongr ρ.rd.kv Γ.kv`: what every incarnation of
every member of the cluster has, `notes/etcd-dist-plan.md` §18.3) at an auth-off view (the member's auth is
off, `memberUp`; review F2, 2026-11-25), and the address `a` set to serve etcd's
table for `(Γ, mid)` (`etcdAddrAt`), `Serve` returns. -/
abbrev Serve_dist.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [ThreadBoundLe GF (2 ^ 28)] [ReceiptBoundLe GF (2 ^ 48)]
    [π : NetProtoGS] (s : Loc) (a : GoString) (ρ : ReqNames) (E₀ : apply.AEnv GF) (lg : Loc) (γn : NetNames GF)
    (mid : w64) (Γ : DistView),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart ∗
      zapLoggerOk lg ∗
      ⌜v3rpc.ServerMethodSets ∧ apply.backendUnderQuota ∧ grpcRepliesFit ∧ srvLevels (GF := GF) ∧
        kvCongr ρ.rd.kv Γ.kv ∧ Γ.auth = false⌝ ∗
      etcdstart.memberUp s ρ E₀ lg γn mid ∗
      etcdAddrAt (Gg := hG.goose_globalGS) a Γ mid }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Serve)) (Val #s))
      (Val #a))
  {{ (err : GoInterface), RET #err; True }}

/-- **PROPOSED (F2's P-L1, 2026-11-26; the auth-lease review's F2, `/shared/tmp/coord-03/rev-f7c-report.md`; for
review with F7's P-A1 change to the same axiom; not used by any proof):** `Serve_dist.spec` with the serving
member's lessor tied to the view: `memberUp` replaced by `etcdstart.memberUpL … Γ.kv.lm (Γ.ls mid)` (its lessor
made at `Γ.ls mid`, `NewServer.specG_dist_proposed`'s `mvccLeases E.γ = γl`, and its lease subsystem at the view's
mode `Γ.kv.lm`). Without it a start could serve a `Γ` whose lessor names it allocated and owns itself
(`etcdAddr_set` takes any `Γ`) and refute the lease axioms' posts; with it, `Γ.ls mid` is the real member's lessor
through `Serve_dist`'s exclusive resources (the member's start), and the lease axioms' distinct-names premise is
redundant (kept). Nothing else changes. -/
abbrev Serve_dist.spec_proposed : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [ThreadBoundLe GF (2 ^ 28)] [ReceiptBoundLe GF (2 ^ 48)]
    [π : NetProtoGS] (s : Loc) (a : GoString) (ρ : ReqNames) (E₀ : apply.AEnv GF) (lg : Loc) (γn : NetNames GF)
    (mid : w64) (Γ : DistView),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart ∗
      zapLoggerOk lg ∗
      ⌜v3rpc.ServerMethodSets ∧ apply.backendUnderQuota ∧ grpcRepliesFit ∧ srvLevels (GF := GF) ∧
        kvCongr ρ.rd.kv Γ.kv ∧ Γ.auth = false⌝ ∗
      -- (PROPOSED, F2's P-L1, 2026-11-26) the started member with its lessor at the view's name `Γ.ls mid`
      -- and the lease subsystem at the view's lease mode `Γ.kv.lm` (in place of `memberUp`'s default `.none`)
      etcdstart.memberUpL s ρ E₀ lg γn mid Γ.kv.lm (Γ.ls mid) ∗
      etcdAddrAt (Gg := hG.goose_globalGS) a Γ mid }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Serve)) (Val #s))
      (Val #a))
  {{ (err : GoInterface), RET #err; True }}

end spec

end etcd_dist
end EtcdGrove
end Perennial
