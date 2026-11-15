/-
`Main()` (`examples/etcd/restart/restart3.go`; restart3 C2, 2026-11-15): `Run(zap.NewNop())`.
Lean-first (no Rocq counterpart).

**The triple:** `Run.spec`'s, at the logger `zap.NewNop` returns: from the members' start bundles (program
start gives them, D19d), the main thread's token and `Run`'s named premises, no panic.
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
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] (N : Nat) (id₁ id₂ id₃ : w64) (ps : List w64)
    (ctxs : List (List w8)) (boot : List LogEntry)
    [ThreadBoundLe GF (2 ^ 28)] [ReceiptBoundLe GF (2 ^ 48)] [ReceiptBoundLe GF (N + 1)],
  BootFacts id₁ id₂ id₃ ps ctxs boot →
  srvLevels (GF := GF) →
  N + 7 + bootWB ≤ backend.wbInit →
  authRecordsFit → apply.backendUnderQuota → storage.diskOk →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.restart ∗
      etcdstart.memberStartRes (GF := GF) name₁ ⟨some peerAddr₁, none⟩ ∗
      etcdstart.memberStartRes (GF := GF) name₂ ⟨some peerAddr₂, none⟩ ∗
      etcdstart.memberStartRes (GF := GF) name₃ ⟨some peerAddr₃, none⟩ ∗
      threadTok ∗ premises N id₁ id₂ id₃ ps ctxs boot }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.restart.Main)) (Val #()))
  {{ RET #(); True }}

end spec

end etcd_restart
end EtcdGrove
end Perennial
