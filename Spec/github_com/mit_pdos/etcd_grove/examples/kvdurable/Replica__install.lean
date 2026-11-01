/- Lean-first (no Rocq counterpart). kvreconf's (the same Go text), ported.

`r.install(md, kv, applied)` (kv.go): the applier's replicated state replaced by a snapshot's: the
maps decoded from its data (`kv`, `applied`: the state of a committed log `L` as long as its index),
its configuration (the metadata's, denoting `mL`, raft's configuration after `L`), its index. The
waiting operations the snapshot covers are answered with its recorded answers (`waitP`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open kvreconf (kvFold logHist AppliedOk ccTransOk)
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
abbrev Replica.install.spec : Prop :=
  ∀ (γ : KdNames) (vs : List w64) (dir : GoString) (id : w64) (r n st sts sq ms : Loc)
    (γs : MemStorNames) (ph : KdDmuNames)
    (ap : List LogEntry) (idx : w64) (csp : Loc) (m : Membership) (mA : Loc)
    (A : GMap (List w8) (List w8)) (mdp : Loc) (dq : DFrac) (md : SnapshotMetadataM)
    (mK' mA' : Loc) (K' A' : GMap (List w8) (List w8)) (L : List LogEntry) (mL : Membership),
  L.length = uint.nat md.Index' → ((L.length : Int) < 2 ^ 61) →
  (∀ k, (K' !! k).getD [] = kvFold (logHist L) k) → AppliedOk A' (logHist L) →
  confStateIs md.ConfState' mL → GMap.size mL.ids < 2 ^ 61 →
  {{ isReplica γ vs dir id r n st sts sq ms γs ph ∗ repOwn γ r ap idx csp m mA A ∗ smOpt mdp dq md ∗
      mK' ↦$ K' ∗ mA' ↦$ A' ∗ isCommittedLogLb γ.r.cluster L ∗ confAt γ.r.cluster L.length mL }}
    (App (App (App (Val (r @!! go.GoType.PointerType kReplicaTy @!! go!"install")) (Val #mdp))
      (Val #mK')) (Val #mA'))
  {{ RET #(); smOpt mdp dq md ∗ ∃ csp' : Loc, repOwn γ r L md.Index' csp' mL mA' A' }}

end spec

end kvdurable
end EtcdGrove
end Perennial
