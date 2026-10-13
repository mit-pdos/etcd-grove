/-
Port of `election_proof/spec_releasePendingReadIndexMessages.v` (feb5c73d4).
-/
module

public import Spec.go_etcd_io.raft.v3.sendMsgReadIndexResponse

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section results
variable [FfiSyntax]

/-- The pending requests released at the commit index (before the heartbeats). -/
def releasedState (id : w64) (s : NState) : NState :=
  { s with rd := { s.rd with pend := [], ro := readonlyRelease s.rd.ro id s.logst.committed s.rd.pend } }

end results

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `releasePendingReadIndexMessages(r)` (`releasePendingReadIndexMessages.impl`,
`Code/go_etcd_io/raft/v3.lean`; Rocq new/code/go_etcd_io/raft/v3.v:5423;
`raft.go:2115`):

    if len(r.pendingReadIndexMessages) == 0 { return }
    if !r.committedEntryInCurrentTerm() { r.logger.Error(...); return }
    msgs := r.pendingReadIndexMessages
    r.pendingReadIndexMessages = nil
    for _, m := range msgs { sendMsgReadIndexResponse(r, m) }

Each pending request arrives as `sendMsgReadIndexResponse` makes it, read at the commit
index (2026-10-12; until then none was ever pending, the phase-1 scope): the queue holds
them in order (`readonlyRelease`), and each arrival broadcasts heartbeats with the position
after it. The `Error` arm is dead: `stepLeader` calls this only after a successful
`maybeCommit`, which commits an entry of the leader's term (the premise). -/
abbrev releasePendingReadIndexMessages.spec : Prop :=
  ∀ (cfg : GSet w64) (r : Loc) (id : w64) (s : NState),
  s.role = .leader →
  s.term ≠ W64 0 →
  (s.rd.pend ≠ [] →
     plogTermAt s.logst.prev (s.logst.sents ++ s.logst.uents) s.logst.committed
       = some s.term) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhys cfg r id s }}
    (App (Val #(functions releasePendingReadIndexMessages [])) (Val #r))
  {{ (ms : List Msg) (pvs : GMap w64 Progress), RET #();
      ownRaftPhys cfg r id
        { sendMsgs (releasedState id s) ms with prvals := pvs } ∗
      ⌜∀ m' ∈ ms, HeartbeatOk id (toPState s) m' ∧
         ∃ k, 0 < k ∧ k ≤ s.rd.pend.length ∧
           m'.ctx = hbCtx (readonlyRelease s.rd.ro id s.logst.committed (s.rd.pend.take k))⌝ ∗
      ⌜prvalsMatch pvs = prvalsMatch s.prvals⌝ }}

end spec

end EtcdGrove
end Perennial
