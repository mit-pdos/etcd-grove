/-
Port of `election_proof/spec_raft__Step.v`.

Lean notes:
* The spec mentions ghost state (`ownRaftGhost`, `isMessage`), so the section has the
  extra variable `[AllG GF]` (porting guide, "Section variables").
* Rocq's `Require Export New.proof.bytes` (for `wp_Equal`, used by the `MsgVote`
  branch's `Context` comparison) is `import Perennial.Proof.bytes`.
* The context's existential is typed `ctx : List w8` (Rocq infers it from `↦*□` and
  the comparison with the `go_string` `campaignTransfer`).
-/
import EtcdGrove.Raft.ElectionProof.InvRaftPhys
import EtcdGrove.Raft.ElectionProof.StepLemmas
-- `bytes.wp_Equal`, for the `MsgVote` branch's `Context` comparison.
import Perennial.Proof.bytes

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
variable [AllG GF]

/-- The top-level dispatch, and **one spec like every other function**. The
per-message-type branches are proof structure, not specification: since 2026-09-17
they live in `proof_raft__Step_MsgHup.v`, `_MsgVote.v` and `_MsgVoteResp.v` (and below
those, `_MsgVote_gt.v`, `_MsgVote_le.v`, `_MsgVote_lt.v`, `_MsgVote_eq_novote.v`,
`_MsgVote_eq_voted.v`), each a functor over `STEP_POSTULATES` with no `Module Type` and
no `Parameter`, so that `make -j` checks them in parallel. Only `proof_raft__Step.v`
and the combining files may `Require` one. (An earlier version of this note said
`Step` "is the one function with more than one spec"; that was written before the
first cut's three per-message-type `Module Type`s were removed on 2026-09-14, and it is
no longer true of anything here.)

This is **the only spec in this development that mentions ghost state**. Every
function below it is specified against `ownRaftPhys` alone, saying which state the
struct ends up refining and how the outbox grew; `Step` assembles those pure facts into
one `Step` witness and takes one `ownRaftGhost_step`. A caller that needs to know a
pending outgoing message is protocol-legal gets that from `ownRaftGhost_outbox`, not
from `ownRaftPhys`. -/
abbrev raft.Step.spec : Prop :=
  ∀ (cfg : GSet w64)
    (γ : RaftElectionNames) (r : Loc) (id : w64) (s : NState) (ps : PState)
    (m : raftpb.Message),
  -- The ghost state is about one configuration, and it is this one. Without this the
  -- caller could hand `ownRaftGhost_step` a `cfg` of its own choosing -- a singleton
  -- one, say, in which the node is its own quorum -- and election safety would not
  -- hold. See `RaftElectionNames`.
  γ.reCfg = cfg →
  ElectionMsg m →
  -- The node is a voter. `stepCandidate` needs this outright (its `poll` and
  -- `becomeLeader` both do) and `spec_stepCandidate_MsgVoteResp.v` says to thread it
  -- in "from the caller" -- but `Step` *is* the outermost caller, so it has to enter
  -- the development here. Under the no-learner, no-reconfiguration scope this is a
  -- property of the node, not of a particular call. Added 2026-09-16 for the
  -- `MsgVoteResp` branch.
  id ∈ cfg →
  -- A `MsgHup` is local (`Term = 0`) and may start an election, which increments the
  -- term; `send` panics if that wraps to zero.
  (m.Type' = MsgHup →
     m.Term' = W64 0 ∧
     uint.Z s.term + 1 < 2 ^ 64) →
  (m.Type' = MsgVote →
     m.To' = id ∧ m.Term' ≠ W64 0 ∧
     m.From' ≠ W64 0) →
  (m.Type' = MsgVoteResp →
     m.To' = id ∧ m.Term' ≠ W64 0) →
  -- The one place the two layers meet. `s` is the physical abstract state
  -- `ownRaftPhys` is indexed by, `ps` the protocol state the ghost state is about,
  -- and `NStateRel` (`Defs.lean`) connects them: `ps` is `s`'s protocol fields,
  -- `r.step` agrees with the role, nothing is on loan.
  NStateRel s ps →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhys cfg r id s ∗
      "Hghost" ∷ ownRaftGhost γ id ps ∗
      "#Hm" ∷ (∀ ty, ⌜mtypeOf m.Type' = some ty⌝ -∗
                     isMessage γ (absMsg ty m)) ∗
      "#Hctx" ∷ (∃ (ctx : List w8), m.Context' ↦*□ ctx ∗
                        ⌜ctx ≠ campaignTransfer⌝) }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #m))
  {{ (err : GoInterface) (s' : NState) (ps' : PState), RET #err;
      "Hphys" ∷ ownRaftPhys cfg r id s' ∗
      "Hghost" ∷ ownRaftGhost γ id ps' ∗
      "%Hrel" ∷ ⌜NStateRel s' ps'⌝ ∗
      "%Hrefines" ∷ ⌜∃ recv, Step cfg id ps recv ps'⌝ ∗
      "%Herr" ∷ ⌜err = interface.nil⌝ }}

end spec

end EtcdGrove
end Perennial
