/- Lean-first (no Rocq counterpart).

`r.request(snapIndex, snap, bound)` (kv.go): the applier, at the committed prefix `ap` (`repOwn`,
read only), asks the snapshot goroutine, without waiting, for a snapshot at `len ap` if `snap` and
that is past `snapIndex` (the latest one asked for), and for a compaction up to the least of `len
ap` and `bound` unless `bound` is `0` (raft's applied index, `nodeAppliedLb` at the storage's key:
`Advance`'s), and returns the latest snapshot index asked for. What the request carries
(`snapReqOk`) comes from the applier's frozen delivered log `D` above the known compaction point
`c`, the node's committed index on the storage (`nodeCommitLb` at `len D`, from the loop's driver:
the snapshotter holds none) and the snapshot's certificate (the store's registry).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KdStor GF]

attribute [local instance] kdStorageModel

/-- See the file header. -/
abbrev Replica.request.spec : Prop :=
  ∀ (γ : KdNames) (vs : List w64) (dir : GoString) (id : w64) (r n st sts sq : Loc)
    (ρ : KdRepNames) (ap : List LogEntry) (csp : Loc) (m : Membership) (mA : Loc)
    (A : GMap (List w8) (List w8)) (D : List LogEntry) (c : Nat) (snapIndex bound : w64)
    (snap : Bool),
  ap <+: D → c ≤ uint.nat snapIndex →
  {{ isReplicaR γ vs dir id r n st sts sq ρ ∗ repOwn γ r ap (W64 ap.length) csp m mA A ∗
      memCompacted ρ.γs c ∗ memLog ρ.γs (c + 1) DFrac.discard ((LogEntry.toEntries D 0).drop c) ∗
      deliveredLogLb n γ.r.cluster kdRaftN D ∗ nodeCommitLb γ.r.cluster ρ.key D.length ∗
      (⌜bound = W64 0⌝ ∨ nodeAppliedLb γ.r.cluster ρ.key (uint.nat bound)) }}
    (App (App (App (Val (r @!! go.GoType.PointerType kReplicaTy @!! go!"request")) (Val #snapIndex)) (Val #snap)) (Val #bound))
  {{ (ret : w64), RET #ret; repOwn γ r ap (W64 ap.length) csp m mA A ∗
      ⌜ret = snapIndex ∨ (ret = W64 ap.length ∧ uint.nat snapIndex < ap.length)⌝ }}

end spec

end kvdurable
end EtcdGrove
end Perennial
