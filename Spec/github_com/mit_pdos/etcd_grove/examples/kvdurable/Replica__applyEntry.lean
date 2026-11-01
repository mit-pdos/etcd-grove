/- Lean-first (no Rocq counterpart).

`r.applyEntry(e)` (kv.go): kvreconf's, but an entry at or below the applied index (`r.index`, the
restarted incarnation's snapshot covers it: raft hands entries back from `Config.Applied`, which may
be below the snapshot's index) is skipped: the replicated state stays at `ap` while the node's
delivered log `l` passes it (`appNode`'s view moves with the skipped entries: the conf entries raft
hands back up to the view's index are the client's to skip, `skippedIn`). The applier's index field
is the replicated state's (`idx = len ap`) and the entry is not past it (`k ≤ len ap`): the code
decides `covered` on the field, and an entry past `len ap` would leave a gap (stage I fix,
2026-11-01).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.Defs
public import Proof.go_etcd_io.raft.v3.InvPbLog

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
abbrev Replica.applyEntry.spec : Prop :=
  ∀ (γ : KdNames) (vs : List w64) (dir : GoString) (id : w64) (r n st sts sq ms : Loc)
    (γs : MemStorNames) (ph : KdDmuNames) (q : Qp) (ap : List LogEntry) (idx : w64) (csp : Loc) (m : Membership)
    (mA : Loc) (A : GMap (List w8) (List w8)) (l : List LogEntry) (k : Nat) (e : LogEntry) (ep : Loc),
  l.take k ++ [e] <+: l → ap <+: l → ((ap.length : Int) + 1 < 2 ^ 61) → ((k : Int) + 1 < 2 ^ 61) →
  uint.Z idx = (ap.length : Int) → k ≤ ap.length →
  {{ isReplica γ vs dir id r n st sts sq ms γs ph ∗ repOwn γ r ap idx csp m mA A ∗
      appNode γ n l (max k ap.length) m ∗ entRO ep (e.toEntryM (W64 (k + 1))) ∗
      isCommittedLogLb γ.r.cluster l ∗ nodeRunning n γ.r.cluster kdRaftN q }}
    (App (Val (r @!! go.GoType.PointerType kReplicaTy @!! go!"applyEntry")) (Val #ep))
  {{ RET #(); ∃ (ap' : List LogEntry) (csp' : Loc) (m' : Membership) (A' : GMap (List w8) (List w8)),
      ⌜ap' = (if k < ap.length then ap else ap ++ [e])⌝ ∗
      repOwn γ r ap' (W64 ap'.length) csp' m' mA A' ∗
      appNode γ n l (max (k + 1) ap'.length) m' ∗ nodeRunning n γ.r.cluster kdRaftN q }}

end spec

end kvdurable
end EtcdGrove
end Perennial
