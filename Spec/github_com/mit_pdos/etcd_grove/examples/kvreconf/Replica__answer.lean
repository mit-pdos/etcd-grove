/- Lean-first (no Rocq counterpart).

`r.answer(pending)` (kv.go): the applier's answer, under the lock, to the pending read states (each
`rsOk`), after it applied the committed prefix `ap` (its index field `len ap`): a read of this
replica waiting at the sequence number its context decodes to, whose read index is applied, gets
the value after `ap` (`readAns`); the read states of a larger index come back, in a new slice.
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
abbrev Replica.answer.spec : Prop :=
  ∀ (γr : RNames) (vs : List w64) (id : w64) (r n st sts : Loc)
    (ap : List LogEntry) (idx : w64) (csp : Loc) (m : Membership) (mA : Loc)
    (A : GMap (List w8) (List w8)) (psl : GoSlice) (ps : List ReadState) (dq : DFrac),
  uint.Z idx = (ap.length : Int) →
  {{ isReplica γr vs id r n st sts ∗ repOwn γr r ap idx csp m mA A ∗
      psl ↦*{dq} ps ∗ [∗list] v ∈ ps, rsOk γr.cluster v }}
    (App (Val (r @!! go.GoType.PointerType rReplicaTy @!! go!"answer")) (Val #psl))
  {{ (rest : GoSlice), RET #rest; repOwn γr r ap idx csp m mA A ∗
      ∃ ps' : List ReadState, rest ↦* ps' ∗ ownSliceCap ReadState rest (DFrac.own 1) ∗
        [∗list] v ∈ ps', rsOk γr.cluster v }}

end spec

end kvreconf
end EtcdGrove
end Perennial
