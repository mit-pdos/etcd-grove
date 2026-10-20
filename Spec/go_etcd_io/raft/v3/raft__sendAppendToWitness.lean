/-
`(*raft).sendAppendToWitness` (raft#168, `raft.go`; 2026-10-20, witness support).
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

/-- The request `sendAppendToWitness` queues: a `MsgApp` from `id` to the witness `w` at the
term `tm`, of the entry `i` of the term `tm` and subterm `st`, with the replication set's
non-witness voters `vs0`, `vs1` of each half. -/
def wappMsg [FfiSyntax] (id w tm st i : w64) (vs0 vs1 : List w64) : WMsg :=
  ⟨MsgApp, id, w, tm, tm, st, i, vs0, vs1, ∅, []⟩

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `r.sendAppendToWitness(w, i, st)` at a configuration with a witness: the request `wappMsg`
(the epoch's halves' non-witness voters, in some order, `GetNonWitnessVoterSlice`) queued on
`r.witnessMsgs`, its protocol reading on the outbox, and an `Infof`. -/
abbrev raft.sendAppendToWitness.spec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (w i st : w64),
  c.wit ≠ W64 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhysCV c c.voters r id s }}
    (App (App (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"sendAppendToWitness"))
      (Val #w)) (Val #i)) (Val #st))
  {{ (vs0 vs1 : List w64), RET #();
      ⌜vs0 ≡ₚ GMap.elements s.ep.rs0.nwv ∧ vs1 ≡ₚ GMap.elements s.ep.rs1.nwv⌝ ∗
      ownRaftPhysCV c c.voters r id (sendMsgs s [wAbs (wappMsg id w s.term st i vs0 vs1)]) }}

end spec

end EtcdGrove
end Perennial
