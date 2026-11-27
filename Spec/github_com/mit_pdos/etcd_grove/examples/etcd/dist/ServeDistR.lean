/- Lean-first (no Rocq counterpart).

**DRAFT (etcd_safe S0, 2026-11-26; unreached, not reviewed).** `etcdstart.Serve(s, a)` of a member incarnation
after the first (restarted on its files after a crash or a graceful stop), against the interim address fact. The
axiom is `Proof/.../etcd/dist/ServeDistR.lean`. `plans/etcd-safe-restart-design.md` §3, §4.3 (P2).

**What changes from `Serve_dist.spec`** (`ServeDist.lean`; `etc/dist-axiom-diff.py` checks the list):
* the premises `Γ.auth = false` and `Γ.kv.lm = .none` in place of the guarded distinct-auth-names premise: the
  auth-off, lease-none class (design D4), where `Serve_dist`'s "Restarts are outside it" applies;
* the binder `γl` (the incarnation's own lessor name) and the member `memberUpL … .none γl` in place of the
  view's `if Γ.auth then memberUpOnL … else memberUpL … Γ.kv.lm (Γ.ls mid)`.
Everything else (the KV names' agreement with the view, `kvCongr`, the address fact `etcdAddrAt a Γ mid`, the
post `True`) is `Serve_dist.spec`'s.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.ServeDist

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

/-- **`Serve(s, a)` of a restarted incarnation of member `mid` of an auth-off, lease-none view `Γ`** (DRAFT; see
the file header and the axiom's docstring): `Serve_dist.spec` with the member's lessor its own (`γl`). -/
abbrev Serve_distR.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [ThreadBoundLe GF (2 ^ 28)] [ReceiptBoundLe GF (2 ^ 48)]
    [π : NetProtoGS] (s : Loc) (a : GoString) (ρ : ReqNames) (E₀ : apply.AEnv GF) (lg : Loc) (γn : NetNames GF)
    (mid : w64) (Γ : DistView) (γl : GName),
  -- the auth-off, lease-none class: no client axiom reads `Γ.ls` or `Γ.au` there
  Γ.auth = false → Γ.kv.lm = .none →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart ∗
      zapLoggerOk lg ∗
      ⌜v3rpc.ServerMethodSets ∧ apply.backendUnderQuota ∧ grpcRepliesFit ∧ srvLevels (GF := GF) ∧
        kvCongr ρ.rd.kv Γ.kv ∧ (Γ.auth = false ∨ ρ.rd.kv.hist = Γ.kv.hist)⌝ ∗
      -- the incarnation's lessor `γl` (its own: `NewLessor` recovered it), at the lease mode `.none`
      etcdstart.memberUpL s ρ E₀ lg γn mid .none γl ∗
      etcdAddrAt (Gg := hG.goose_globalGS) a Γ mid }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Serve)) (Val #s))
      (Val #a))
  {{ (err : GoInterface), RET #err; True }}

end spec

end etcd_dist
end EtcdGrove
end Perennial
