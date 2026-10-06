/-
Port of `election_proof/spec_releasePendingReadIndexMessages.v` (feb5c73d4).
-/
import EtcdGrove.Raft.ElectionProof.InvRaftPhys

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `releasePendingReadIndexMessages(r)` (`releasePendingReadIndexMessages.impl`,
`Perennial/Code/go_etcd_io/raft/v3.lean`; Rocq new/code/go_etcd_io/raft/v3.v:5423;
`raft.go:2115`):

    if len(r.pendingReadIndexMessages) == 0 { return }
    if !r.committedEntryInCurrentTerm() { r.logger.Error(...); return }
    msgs := r.pendingReadIndexMessages
    r.pendingReadIndexMessages = nil
    for _, m := range msgs { sendMsgReadIndexResponse(r, m) }

Under the phase-1 scope no `MsgReadIndex` is ever pending (`ownRaftMisc`'s
`pendingReadIndexMessages ↦* []`, `InvMisc.lean`), so the first test returns at once
and the struct is unchanged. `stepLeader` calls it after a successful `maybeCommit`. -/
abbrev releasePendingReadIndexMessages.spec : Prop :=
  ∀ (cfg : GSet w64) (r : Loc) (id : w64) (s : NState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhys cfg r id s }}
    (App (Val #(functions releasePendingReadIndexMessages [])) (Val #r))
  {{ RET #(); ownRaftPhys cfg r id s }}

end spec

end EtcdGrove
end Perennial
