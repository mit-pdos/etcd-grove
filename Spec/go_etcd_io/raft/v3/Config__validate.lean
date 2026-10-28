/- Port of election_proof/spec_Config__validate.v (857d09190). -/
module

public import Proof.go_etcd_io.raft.v3.ApiVocab
public import Proof.go_etcd_io.raft.v3.InvRaftPhys

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section defs
variable [GooseExts]

-- (2026-10-26, raft's signature, stage 1) `ConfigValid` moved to `Proof.go_etcd_io.raft.v3.ApiVocab`.

/-- `validate` writes defaults into up to four fields (`MaxUncommittedEntriesSize`,
`MaxCommittedSizePerReady`, `MaxInflightBytes`, and `Logger` when nil). The
postcondition says only which fields it preserves -- the ones `newRaft` reads and a
proof needs to know -- and not what the defaults are. -/
def ConfigPreserved (cv cv' : Config) : Prop :=
  cv'.ID' = cv.ID' ∧
  cv'.ElectionTick' = cv.ElectionTick' ∧
  cv'.HeartbeatTick' = cv.HeartbeatTick' ∧
  cv'.Storage' = cv.Storage' ∧
  cv'.Applied' = cv.Applied' ∧
  cv'.MaxInflightMsgs' = cv.MaxInflightMsgs' ∧
  cv'.CheckQuorum' = cv.CheckQuorum' ∧
  cv'.PreVote' = cv.PreVote' ∧
  cv'.DisableProposalForwarding' = cv.DisableProposalForwarding' ∧
  cv'.Logger' = cv.Logger' ∧
  -- the `MaxCommittedSizePerReady` default (2026-10-05, for the log's applying limit):
  -- `MaxSizePerMsg` when unset
  cv'.MaxCommittedSizePerReady' =
    (if cv.MaxCommittedSizePerReady' = W64 0 then cv.MaxSizePerMsg'
     else cv.MaxCommittedSizePerReady') ∧
  -- read by `NewRawNode` after `newRaft` (2026-10-09)
  cv'.AsyncStorageWrites' = cv.AsyncStorageWrites' ∧
  -- read by `newRaft` (2026-10-12, read-index)
  cv'.ReadOnlyOption' = cv.ReadOnlyOption' ∧
  -- read by `newRaft` (2026-10-13, reconfiguration stage D)
  cv'.DisableConfChangeValidation' = cv.DisableConfChangeValidation' ∧
  -- read by `newRaft` (2026-10-14, reconfiguration stage B7 part 2: a dynamic `RawNode` needs
  -- it on)
  cv'.StepDownOnRemoval' = cv.StepDownOnRemoval'

end defs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

abbrev Config.validate.spec : Prop :=
  ∀ (c : Loc) (cv : Config),
  ConfigValid cv →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ c ↦ cv }}
    (App (Val (c @!! go.GoType.PointerType Config.ty @!! go!"validate")) (Val #()))
  {{ (cv' : Config), RET #interface.nil;
      c ↦ cv' ∗ ⌜ConfigPreserved cv cv'⌝ }}

end spec

end EtcdGrove
end Perennial
