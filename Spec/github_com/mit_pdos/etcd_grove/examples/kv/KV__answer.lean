/- Lean-first (no Rocq counterpart).

`(*KV).answer(pending, applied)` (kv.go:148, 2026-10-13): the applier's answer to
the pending read states (each `rsOk`: a `ReadState` value whose context holds the bytes of a
read state `Ready` handed out, `readStateOk`; raft v3.7, stage R6b, D6: a read context is its
bytes), after it applied the committed prefix `ap` (`runOwn`), at least `applied` long: a
waiting read of this replica whose read index is at most `applied` gets the value after `ap`
(`readAns`); the read states with a larger index come back, in a new slice.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kv

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]
variable [KVStor GF]

/-- See the file header. -/
abbrev KV.answer.spec : Prop :=
  ∀ (γr : RKVNames) (γp : RepNames) (r : Loc) (id : w64) (n st : Loc)
    (ap : List Draft.LogEntry) (psl : GoSlice) (ps : List ReadState) (dq : DFrac) (applied : w64),
  uint.Z applied ≤ (ap.length : Int) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kv ∗
      isReplica γr γp r id n st ∗ runOwn γr r ap ∗
      psl ↦*{dq} ps ∗ [∗list] v ∈ ps, rsOk γr.cluster v }}
    (App (App (Val (r @!! go.GoType.PointerType rKVTy @!! go!"answer")) (Val #psl))
      (Val #applied))
  {{ (rest : GoSlice), RET #rest; runOwn γr r ap ∗
      ∃ ps' : List ReadState, rest ↦* ps' ∗ ownSliceCap ReadState rest (DFrac.own 1) ∗
        [∗list] v ∈ ps', rsOk γr.cluster v }}

end spec

end kv
end EtcdGrove
end Perennial
