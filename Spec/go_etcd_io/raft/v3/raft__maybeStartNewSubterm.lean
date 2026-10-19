/-
`(*raft).maybeStartNewSubterm` (raft#168, `raft.go`; 2026-10-19, witness support).
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys

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

/-- `r.maybeStartNewSubterm(newTerm, false)` on a witness-free configuration (`ownRaftPhysC`'s
tracker, `ownTrackerC`). With `newTerm` (`becomeLeader`) the tracker's replication set is reset
(`ResetReplicationSet(true)`: a fresh witness-free epoch, which `ownRaftPhysCV` does not see) and
the empty entry is appended as `appendEntry` does (stamped with the term, the next index and
subterm 0, then the self-acknowledgement), and it returns `true`. Without (`stepLeader`'s
check-quorum) `ChangeReplicationSet` finds no excluded voter to swap in, so nothing happens and
it returns `false`. Only `confChange = false` is specified: `switchToConfig` passes `true` only
when a witness is involved. The term is nonzero when an entry is appended, as for
`appendEntry`. -/
abbrev raft.maybeStartNewSubterm.spec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (nt : Bool),
  (nt = true → s.term ≠ W64 0) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhysCV c c.voters r id s }}
    (App (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"maybeStartNewSubterm"))
      (Val #nt)) (Val #false))
  {{ RET #nt;
      if nt then
        ownRaftPhysCV c c.voters r id
          (sendMsgs
            { s with logst :=
                logAppend s.logst ([zero_val EntryM].mapIdx (stamp s.term (logLast s.logst))) }
            [selfAck id
              { s with logst :=
                  logAppend s.logst ([zero_val EntryM].mapIdx (stamp s.term (logLast s.logst))) }])
      else
        ownRaftPhysCV c c.voters r id s }}

end spec

end EtcdGrove
end Perennial
