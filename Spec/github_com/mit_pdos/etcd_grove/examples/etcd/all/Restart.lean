/- Lean-first (no Rocq counterpart).

`Restart(k5)` (`examples/etcd/all/all.go`; `notes/etcd-unified-scope.md` §3.1): restartN's `Main(k5)` on
a goroutine of its own (`spawn`) and restart1's `Main()` on the calling thread, at once; `Restart`
returns once both have (a `sync.WaitGroup`).

**The triple:** the two drivers' triples side by side (`etcd_restartN.Main.spec`,
`etcd_restart1.Main.spec`): from the package's `isPkgInit`, restartN's members' start bundles and
restart1's member's, the calling thread's token and each cluster's named premises at one bound `N`,
`Restart` does not panic and returns; the pure premises are the union of the two triples', once each
where they coincide.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.restartN.Main
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.restart1.Main
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.all.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_all

open Iris Iris.BI go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.all.Assumptions]

/-- See the file header. -/
abbrev Restart.spec : Prop :=
  ∀ (N : Nat)
    (k₅ : Nat) (ids₅ ps₅ : List w64) (ctxs₅ : List (List w8)) (boot₅ : List LogEntry)
    (rId : w64) (ctxsR : List (List w8)) (bootR : List LogEntry)
    [ThreadBoundLe GF (2 ^ 28)] [ReceiptBoundLe GF (2 ^ 48)] [ReceiptBoundLe GF (N + 1)],
  srvLevels (GF := GF) →
  k₅ ≤ 1000 → ids₅.length = k₅ → etcd_restartN.BootFacts ids₅ ps₅ ctxs₅ boot₅ →
  etcd_restart1.BootFacts rId ctxsR bootR →
  N + 7 + bootWB ≤ backend.wbInit →
  authRecordsFit → apply.backendUnderQuota → storage.diskOk →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.all ∗
      ([∗list] m ∈ etcd_restartN.members k₅,
        etcdstart.memberStartRes (GF := GF) m.Name' ⟨some m.Peer', none⟩) ∗
      etcdstart.memberStartRes (GF := GF) etcd_restart1.name {} ∗
      threadTok ∗
      etcd_restartN.premises k₅ N ids₅ ps₅ ctxs₅ boot₅ ∗
      etcd_restart1.premises N rId ctxsR bootR }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.all.Restart)) (Val #(W64 k₅)))
  {{ RET #(); True }}

end spec

end etcd_all
end EtcdGrove
end Perennial
