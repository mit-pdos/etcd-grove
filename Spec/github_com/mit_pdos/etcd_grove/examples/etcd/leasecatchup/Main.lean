/-
`Main()` (`examples/etcd/leasecatchup/leasecatchup.go`; lease-mono3 step 1, 2026-11-06,
`notes/lease-mono3-plan.md`): `run(zap.NewNop())`. Lean-first (no Rocq counterpart).

**The triple:** `run`'s (`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/leasecatchup/run.lean`),
at `zap.NewNop()`'s logger: from the package's `isPkgInit`, the cluster's start bundle, the main
thread's token and the cluster's named premises, `Main()` returns: it does not panic (member 3, once
caught up, still lists the lease granted through it).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.leasecatchup.run

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_leasecatchup

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.leasecatchup.Assumptions]

/-- See the file header. -/
abbrev Main.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions]
    [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)]
    [ContextErrsClient (GF := GF) (hG := hG)]
    (N : Nat) (id₁ id₂ id₃ : w64) (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry),
  cluster3.BootFacts id₁ id₂ id₃ ps ctxs boot →
  threadBound GF ≤ 2 ^ 28 → receiptBound GF ≤ 2 ^ 48 → receiptBound GF ≤ N + 1 →
  N + 7 + bootWB ≤ backend.wbInit →
  ckptEffectsOk → authRecordsFit → apply.backendUnderQuota → grpcRepliesFit → storage.diskOk →
  leasePeersOk → lease.leasesNoExpiry →
  v3rpc.ServerMethodSets →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.leasecatchup ∗
      cluster3.startRes (GF := GF) clusterCfg ∗
      threadTok ∗ cluster3.premises clusterCfg N id₁ id₂ id₃ ps ctxs boot }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.leasecatchup.Main)) (Val #()))
  {{ RET #(); True }}

end spec

end etcd_leasecatchup
end EtcdGrove
end Perennial
