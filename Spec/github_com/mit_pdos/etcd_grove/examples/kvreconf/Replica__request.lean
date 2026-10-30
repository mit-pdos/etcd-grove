/- Lean-first (no Rocq counterpart).
`r.request(snapIndex, snap, compact)` (kv.go; kvreconf-snapshot-thread, 2026-10-30, in place of
`maybeSnapshot` and `maybeCompact`): the applier, at the committed prefix `ap` (`repOwn`, read only),
asks the snapshot goroutine, without waiting, for a snapshot at `len ap` if `snap` and that is past
`snapIndex` (the latest one asked for), and for a compaction up to `len ap` if `compact`, and
returns the latest snapshot index asked for. What the request carries (`snapReqOk`) comes from the
applier's storage ranges: the delivered log `D` it applied a prefix of, frozen above the known
compaction point `c ≤ snapIndex` (`frozenTo`, so the entry at `len ap` is frozen, its term `ap`'s
last), the node's delivered log (`deliveredLogLb`), and, for a compaction, the node's applied index
`len ap` (`Advance`'s, `nodeAppliedLb`); the snapshot's validity (`snapshotValid`) is certified in
the store's registry (`kvrSnapInv`) with `ap`'s state.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.DefsCluster

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KvrStor GF]

attribute [local instance] kvrStorageModel

/-- See the file header. -/
abbrev Replica.request.spec : Prop :=
  ∀ (γr : RNames) (vs : List w64) (id : w64) (r n st sts : Loc) (ρ : RepNames)
    (ap : List LogEntry) (csp : Loc) (m : Membership) (mA : Loc) (A : GMap (List w8) (List w8))
    (D : List LogEntry) (c : Nat) (snapIndex : w64) (snap compact : Bool),
  ap <+: D → c ≤ uint.nat snapIndex →
  {{ isReplicaR γr vs id r n st sts ρ ∗ repOwn γr r ap (W64 ap.length) csp m mA A ∗
      memCompacted ρ.γs c ∗ frozenTo ρ.γs c D ∗ deliveredLogLb n γr.cluster kvrRaftN D ∗
      (⌜compact = false⌝ ∨ nodeAppliedLb γr.cluster id ap.length) }}
    (App (App (App (Val (r @!! go.GoType.PointerType rReplicaTy @!! go!"request")) (Val #snapIndex))
      (Val #snap)) (Val #compact))
  {{ (ret : w64), RET #ret; repOwn γr r ap (W64 ap.length) csp m mA A ∗
      ⌜ret = snapIndex ∨ (ret = W64 ap.length ∧ uint.nat snapIndex < ap.length)⌝ }}

end spec

end kvreconf
end EtcdGrove
end Perennial
