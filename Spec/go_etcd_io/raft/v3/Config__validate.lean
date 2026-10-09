/- Port of election_proof/spec_Config__validate.v (857d09190). -/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section defs
variable [FfiSyntax]

/-- What `Config.validate` checks, as a proposition over the `Config`. Each conjunct is
exactly the condition Go tests before one of its `return errors.New(...)`s, except
`Logger ≠ nil`: Go substitutes the package default logger (`getLogger`) for a nil one,
and taking the logger as given keeps the default logger out of the trust base. -/
def ConfigValid (cv : Config) : Prop :=
  cv.ID' ≠ W64 0 ∧
  cv.ID' ≠ W64 18446744073709551615 ∧
  cv.ID' ≠ W64 18446744073709551614 ∧
  (0 < sint.Z cv.HeartbeatTick' ∧ sint.Z cv.HeartbeatTick' < sint.Z cv.ElectionTick') ∧
  cv.Storage' ≠ interface.nil ∧
  0 < sint.Z cv.MaxInflightMsgs' ∧
  (cv.MaxInflightBytes' = W64 0 ∨ uint.Z cv.MaxSizePerMsg' ≤ uint.Z cv.MaxInflightBytes') ∧
  cv.Logger' ≠ interface.nil ∧
  (cv.ReadOnlyOption' = W64 0 ∨ cv.CheckQuorum' = true)

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
     else cv.MaxCommittedSizePerReady')

end defs

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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
