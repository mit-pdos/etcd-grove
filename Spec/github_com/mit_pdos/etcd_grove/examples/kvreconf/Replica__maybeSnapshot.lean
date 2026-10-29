/- Lean-first (no Rocq counterpart).

`r.maybeSnapshot(snapIndex)` (kv.go): the applier, at the committed prefix `ap` (`repOwn`, read
only), takes a snapshot of its replicated state at `len ap` if that is past the stored snapshot's
index `snapIndex` (`memSnapExact`: the applier is the stored snapshot's only writer), and returns the
stored snapshot's index after it. What `CreateSnapshot` needs comes from the applier's storage
ranges: the delivered log `D` it applied a prefix of, frozen above the known compaction point `c`
(`frozenTo`, with `c ≤ snapIndex`, so the entry at `len ap` is frozen, its term `ap`'s last), and the
node's delivered log (`deliveredLogLb`, the storage's `J.DL`). The snapshot's validity
(`snapshotValid`) is certified in the store's registry (`kvrSnapInv`) with `ap`'s state.
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
abbrev Replica.maybeSnapshot.spec : Prop :=
  ∀ (γr : RNames) (vs : List w64) (id : w64) (r n st sts : Loc) (ρ : RepNames)
    (ap : List LogEntry) (csp : Loc) (m : Membership) (mA : Loc) (A : GMap (List w8) (List w8))
    (D : List LogEntry) (c : Nat) (sv0 : SnapshotM) (snapIndex : w64),
  ap <+: D → c ≤ uint.nat snapIndex → sv0.Metadata'.Index' = snapIndex →
  {{ isReplicaR γr vs id r n st sts ρ ∗ repOwn γr r ap (W64 ap.length) csp m mA A ∗
      memSnapExact ρ.γs sv0 ∗ frozenTo ρ.γs c D ∗ deliveredLogLb n γr.cluster kvrRaftN D }}
    (App (Val (r @!! go.GoType.PointerType rReplicaTy @!! go!"maybeSnapshot")) (Val #snapIndex))
  {{ (ret : w64), RET #ret; ∃ sv1 : SnapshotM,
      repOwn γr r ap (W64 ap.length) csp m mA A ∗ memSnapExact ρ.γs sv1 ∗
      ⌜sv1.Metadata'.Index' = ret ∧
        (ret = snapIndex ∨ (ret = W64 ap.length ∧ uint.nat snapIndex < ap.length))⌝ }}

end spec

end kvreconf
end EtcdGrove
end Perennial
