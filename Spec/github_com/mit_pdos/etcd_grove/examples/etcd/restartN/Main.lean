/-
`Main(k)` (`examples/etcd/restartN/restartN.go`; `notes/restartN-plan.md`): `Run(k, zap.NewNop())`.
Lean-first (no Rocq counterpart).

**The triple:** `Run.spec`'s, at the logger `zap.NewNop` returns: from the members' start bundles (program
start gives them, D19d), the main thread's token and `Run`'s named premises, no panic.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.restartN.Run

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_restartN

open Iris Iris.BI go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver
open etcd_restart

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.restartN.Assumptions]

/-- See the file header. -/
abbrev Main.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] (k : Nat) (N : Nat) (ids : List w64) (ps : List w64)
    (ctxs : List (List w8)) (boot : List LogEntry)
    [ThreadBoundLe GF (2 ^ 28)] [ReceiptBoundLe GF (2 ^ 48)] [ReceiptBoundLe GF (N + 1)],
  k ≤ 1000 → ids.length = k → BootFacts ids ps ctxs boot →
  srvLevels (GF := GF) →
  N + 7 + bootWB ≤ backend.wbInit →
  authRecordsFit → apply.backendUnderQuota → storage.diskOk →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.restartN ∗
      ([∗list] m ∈ members k, etcdstart.memberStartRes (GF := GF) m.Name' ⟨some m.Peer', none⟩) ∗
      threadTok ∗ premises k N ids ps ctxs boot }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.restartN.Main)) (Val #(W64 k)))
  {{ RET #(); True }}

end spec

end etcd_restartN
end EtcdGrove
end Perennial
