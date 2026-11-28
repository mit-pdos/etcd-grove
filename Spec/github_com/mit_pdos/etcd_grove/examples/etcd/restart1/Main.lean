/-
`Main()` (`examples/etcd/restart1/restart1.go`; restart S7.5, step g, 2026-11-14): `Run(zap.NewNop())`.
Lean-first (no Rocq counterpart).

**The triple:** with the member's start bundle (`etcdstart.memberStartRes`: its data directory fresh,
`ETCD_VERIFY` off; program start gives it, D19d), the main thread's token and `Run`'s named premises
(`premises`), at the bounds the server's specs take: no panic.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.restart1.Run

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_restart1

open Iris Iris.BI go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.restart1.Assumptions]

/-- See the file header. -/
abbrev Main.spec : Prop :=
  ∀ (N : Nat) (id : w64) (ctxs : List (List w8))
    (boot : List LogEntry)
    [ThreadBoundLe GF (2 ^ 28)] [ReceiptBoundLe GF (2 ^ 48)] [ReceiptBoundLe GF (N + 1)],
  BootFacts id ctxs boot →
  srvLevels (GF := GF) →
  N + 7 + bootWB ≤ backend.wbInit →
  authRecordsFit → apply.backendUnderQuota → storage.diskOk →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.restart1 ∗
      etcdstart.memberStartRes (GF := GF) name {} ∗ threadTok ∗ premises N id ctxs boot }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.restart1.Main)) (Val #()))
  {{ RET #(); True }}

end spec

end etcd_restart1
end EtcdGrove
end Perennial
