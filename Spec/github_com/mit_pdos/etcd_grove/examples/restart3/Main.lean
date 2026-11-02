/-
`Main()` (`examples/restart3/restart3.go`; the restart plan's R2a, 2026-11-02; DRAFT): `Run` with
no logging (`zap.NewNop()`). Lean-first (no Rocq counterpart).

**The triple:** `Run.spec`'s, at the logger `zap.NewNop` returns.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.restart3.Run

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace restart3

open Iris Iris.BI go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.restart3.Assumptions]

/-- See the file header. -/
abbrev Main.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions]
    [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)]
    [ContextErrsClient (GF := GF) (hG := hG)]
    (N : Nat) (id₁ id₂ id₃ : w64) (ctxs : List (List w8)) (boot : List LogEntry)
    [ThreadBoundLe GF (2 ^ 28)] [ReceiptBoundLe GF (2 ^ 48)] [ReceiptBoundLe GF (N + 1)],
  runPure id₁ id₂ id₃ ctxs boot →
  v3rpc.ServerMethodSets →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.restart3 ∗
      runRes N id₁ id₂ id₃ ctxs boot }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.restart3.Main)) (Val #()))
  {{ RET #(); True }}

end spec

end restart3
end EtcdGrove
end Perennial
