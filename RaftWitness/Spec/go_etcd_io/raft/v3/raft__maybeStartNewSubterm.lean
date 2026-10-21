/-
`(*raft).maybeStartNewSubterm` (raft#168, `raft.go`; 2026-10-19, witness support).
-/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.InvRaftPhys

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The empty entry `maybeStartNewSubterm` appends (`appendEntry`): stamped with the term, the next
index and the node's subterm, then self-acknowledged. -/
def subtermStart (id : w64) (s : NState) : NState :=
  sendMsgs
    { s with logst :=
        logAppend s.logst ([zero_val EntryM].mapIdx (stampS s.term s.ep.sub (logLast s.logst))) }
    [selfAck id
      { s with logst :=
          logAppend s.logst ([zero_val EntryM].mapIdx (stampS s.term s.ep.sub (logLast s.logst))) }]

/-- `r.maybeStartNewSubterm(newTerm, false)` at a tracker of the configuration `c`
(`ownRaftPhysCV`'s, `ownTrackerC`; 2026-10-20 at any configuration, until then witness-free).
With `newTerm` (`becomeLeader`) the tracker's replication set is reset (`ResetReplicationSet(true)`:
the reset epoch at subterm 0, the witness excluded, bare without a witness) and the empty entry is
appended as `appendEntry` does (`subtermStart`), and it returns `true`. Without (`stepLeader`'s
check-quorum) `ChangeReplicationSet` either finds no voter to swap (always without a witness) and
returns `false` with nothing changed, or installs the next subterm's epoch (`ChangeEpochOk`) and
the empty entry is appended at it, returning `true`. Only `confChange = false` is specified:
`switchToConfig` passes `true` only when a witness is involved. The term is nonzero when an entry
may be appended, as for `appendEntry`. -/
abbrev raft.maybeStartNewSubterm.spec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (nt : Bool) (k : Nat),
  (nt = true ∨ s.ep.hasWit = true → s.term ≠ W64 0) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhysCV c c.voters r id s ∗
      -- (2026-10-20) a time receipt, raised by one with the empty entry (`appendEntry`'s)
      ⧖ k }}
    (App (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"maybeStartNewSubterm"))
      (Val #nt)) (Val #false))
  {{ (ch : Bool), RET #ch;
      if nt then
        ⌜ch = true⌝ ∗ ⧖ (k + 1) ∗ ownRaftPhysCV c c.voters r id
          (subtermStart id { s with ep := resetEpoch c.incoming c.outgoing c.wit (W64 0) (W64 0) })
      else if ch then
        ∃ em', ⌜s.ep.hasWit = true ∧ ChangeEpochOk c.incoming c.outgoing c.wit (W64 0) s.ep em'⌝ ∗
          ⧖ (k + 1) ∗ ownRaftPhysCV c c.voters r id (subtermStart id { s with ep := em' })
      else
        ownRaftPhysCV c c.voters r id s }}

end spec

end EtcdGrove
end Perennial
