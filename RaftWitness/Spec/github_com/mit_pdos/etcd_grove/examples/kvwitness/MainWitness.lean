/- Lean-first (no Rocq counterpart). (2026-10-20, W4)

## `MainWitness()` (check.go), the top-level driver of the cluster with a witness

`StartClusterWitness([]uint64{1, 2}, 3)` (two regular voters and the witness `3`, raft's static
mode, no conf change), then `Check(kvs, lintest.CounterClock(), 4, 25)`, the randomized
linearizability test, then a panic unless porcupine answers `Ok`: as `Main.spec`, it returns, so
porcupine's check of the recorded trace always passes.
-/
module

public import RaftWitness.Proof.github_com.mit_pdos.etcd_grove.examples.kvwitness.Defs
public import Proof.github_com.anishathalye.porcupine.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvwitness

open Iris Iris.BI go_etcd_io.raft.v3
open github_com.anishathalye.porcupine

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvwitness.Assumptions]

/-- See the file header. -/
abbrev MainWitness.spec : Prop :=
  receiptBound GF ≤ 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvwitness ∗ context.isClosedchanInit }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.kvwitness.MainWitness)) (Val #()))
  {{ RET #(); True }}

end spec

end kvwitness
end EtcdGrove
end Perennial
