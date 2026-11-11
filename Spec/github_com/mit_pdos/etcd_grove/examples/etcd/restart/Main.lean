/-
`Main()` (`examples/etcd/restart/restart3.go`; the restart plan's R2a, 2026-11-02; DRAFT): `Run` with
no logging (`zap.NewNop()`). Lean-first (no Rocq counterpart).

**The triple:** `Run.spec`'s, at the logger `zap.NewNop` returns.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.restart.Run

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_restart

open Iris Iris.BI go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.restart.Assumptions]

/-- See the file header. -/
abbrev Main.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions]
    [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)]
    [ContextErrsClient (GF := GF) (hG := hG)]
    (N : Nat) (id₁ id₂ id₃ : w64) (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    [ThreadBoundLe GF (2 ^ 28)] [ReceiptBoundLe GF (2 ^ 48)] [ReceiptBoundLe GF (N + 1)],
  -- (per-type stage B3) the levels of a thread token the server's gRPC runs use
  srvLevels (GF := GF) →
  -- (2026-11-03, the whole-`bootOk` review, A) the write budget `bootstrap`'s own write-backs leave
  N + 7 + bootWB ≤ backend.wbInit →
  runPure id₁ id₂ id₃ ps ctxs boot →
  v3rpc.ServerMethodSets →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.restart ∗
      runRes N id₁ id₂ id₃ ps ctxs boot }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.restart.Main)) (Val #()))
  {{ RET #(); True }}

end spec

end etcd_restart
end EtcdGrove
end Perennial
