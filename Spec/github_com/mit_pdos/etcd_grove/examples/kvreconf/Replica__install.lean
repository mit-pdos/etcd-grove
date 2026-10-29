/- Lean-first (no Rocq counterpart).

`r.install(md, kv, applied)` (kv.go): the applier's replicated state replaced by a snapshot's: the
maps decoded from its data (`kv`, `applied`: the state of a committed log `L` as long as its index),
its configuration (the metadata's, denoting `mL`, raft's configuration after `L`), its index. The
waiting operations the snapshot covers are answered with its recorded answers (`waitP`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.Defs

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
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [StorageModel GF] [AllG GF]

/-- See the file header. -/
abbrev Replica.install.spec : Prop :=
  ∀ (γr : RNames) (vs : List w64) (id : w64) (r n st sts : Loc)
    (ap : List LogEntry) (idx : w64) (csp : Loc) (m : Membership) (mA : Loc)
    (A : GMap (List w8) (List w8)) (mdp : Loc) (dq : DFrac) (md : SnapshotMetadataM)
    (mK' mA' : Loc) (K' A' : GMap (List w8) (List w8)) (L : List LogEntry) (mL : Membership),
  L.length = uint.nat md.Index' → ((L.length : Int) < 2 ^ 61) →
  (∀ k, (K' !! k).getD [] = kvFold (logHist L) k) → AppliedOk A' (logHist L) →
  confStateIs md.ConfState' mL →
  {{ isReplica γr vs id r n st sts ∗ repOwn γr r ap idx csp m mA A ∗ smOpt mdp dq md ∗
      mK' ↦$ K' ∗ mA' ↦$ A' ∗ isCommittedLogLb γr.cluster L ∗ confAt γr.cluster L.length mL }}
    (App (App (App (Val (r @!! go.GoType.PointerType rReplicaTy @!! go!"install")) (Val #mdp))
      (Val #mK')) (Val #mA'))
  {{ RET #(); smOpt mdp dq md ∗ ∃ csp' : Loc, repOwn γr r L md.Index' csp' mL mA' A' }}

end spec

end kvreconf
end EtcdGrove
end Perennial
