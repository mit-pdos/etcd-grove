/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_MsgVote_eq_novote.v.

One case of `Step`'s `MsgVote` branch with `m.Term ≤ r.Term`, in its own file so that
it checks in parallel with the others -- see `proof_raft__Step_MsgVote_le.v`
(`MsgVote_le.lean`), which combines them, and `notes/decisions.md` (2026-09-17;
2026-09-18 for why this directory exists). Proof structure, not specification: no
`Module Type`, no `Parameter`; only `MsgVote_le.lean` may import this module.

Lean notes:
* The branch lemma takes the callee specs (Rocq's functor argument `P : STEP_POSTULATES`)
  as its first argument `_P : raft.Step.Postulates`, and Rocq's section variable `c`
  as its second.
* Rocq's `Local Ltac recv_elem` (`∀ m' ∈ recv, m' = a` for the concrete `recv` lists
  `[]`, `[a]`, `[a] ++ [a]`, by rewriting the membership away rather than `set_solver`,
  which took 150s and more there) is not ported.
* Rocq's `Local Ltac vote_grant_tail` and `vote_reject_tail` are the macros
  `vote_grant_tail` and `vote_reject_tail` of `ElectionLemmas.lean` (taking no arguments: they refer to the
  proof's hypothesis names `Hty`, `Hto`, `Hterm`, `Hfnz`, `Heq0`, `Hwf`, and the grant
  tail to `Hcan`/`Hutd`). The `send` premise of both is the helper `sendOk_voteResp`;
  `send`'s precondition is framed with `$$ [Hphys]` then `iframe Hphys`, since `[$Hphys]`
  would be an antiquotation inside the macro. The `MsgPreVote` type test is the
  macro `ty_ne`. `Step`'s
  `MsgVote` decision has exactly two tails -- grant the vote or decline it -- and the
  code reaches each of them by several routes through the `canVote` computation
  (already voted for this candidate; not voted and no leader; voted for somebody else; a
  leader is known). The program point they start at is in the middle of `Step`'s body,
  so there is no closed expression to state a lemma about; in Rocq they are tactics.
  Grant (in the *current* term): log, `send` the response, and record
  `r.Vote := m.From` (`StepC.grantVote`; `can` is the protocol-level `PCanVote` of
  `toPState s`). Decline: log, then `send` a rejection carrying `r.Term`
  (`StepC.rejectVote`); always legal. Both start with the log closed (`"Hphys"` whole).

raft v3.7 (2026-10-15, stage R4 phase 3): the message is a pointer `ml` with `msgIn ml □ ⟨m, ents,
sn, ctx, rs⟩`, read by the getters (`wp_get`/`wp_gets`, `ElectionLemmas.lean`, by `PB`); a response
is a fresh `*pb.Message` sharing the request's `From` (granted: and `Term`) cell
(`msgPtsC_From_acc`/`_Term_acc`, `msgOwn_of_resp`), handed to `send`.
-/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.raft__Step.ElectionLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section branches
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

namespace StepProof

/-! `MsgVote`: step down if the term is higher, then grant or decline.

The thing to know before editing this proof is that **`canVote`'s Go-level shape
decides how many `decide`s each arm owes**. The Go expression is

    (Vote == m.From) || (Vote == None && lead == None)
                     || (m.Type == MsgPreVote && m.Term > r.Term)

and Goose compiles `||`/`&&` to short-circuiting `If`s, so the number of comparisons
`wp_auto` actually evaluates differs per arm:

- `Vote = m.From`: one (`true`, done).
- `Vote = None`, `lead = None`: three (the second disjunct is `true`).
- `Vote = None`, `lead ≠ None`: **four** -- the second disjunct is `false`, so the
  third is evaluated and its `MsgPreVote` test is live.
- `Vote ≠ None`, `Vote ≠ m.From`: **three** -- `A` and `B` are `false`, then the
  `MsgPreVote` test again.

The two four/three-comparison arms are the two that decline, and an earlier version of
the Rocq script left their `MsgPreVote` `bool_decide` undischarged: `wp_auto` then
stopped in front of it, and the failure surfaced fifteen lines later as `iApply: cannot
apply` at the `lastEntryID` call. So each arm does its own `decide` bookkeeping and
only then calls the shared tail; the tails themselves (grant / decline, see the Lean
notes) assume the program is sitting right after `lastEntryID` with `canVote` already
decided. -/

set_option maxHeartbeats 2000000 in
/-- `MsgVote` with `m.Term = r.Term` and `r.Vote = None`: grant if no leader is known and
the candidate's log is up to date, else decline. -/
theorem wp_Step_MsgVote_eq_novote (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (PB : raft.Step.PbPostulates (GF := GF) (hG := hG))
    (c : CfgM) (r : Loc) (id : w64) (s : NState) (ml : Loc) (m : MessageM)
    (ents : List EntryM) (sn : Option SnapshotM) (ctx : List w8) (rs : List Loc) :
    m.Type' = MsgVote →
    m.To' = id →
    m.Term' ≠ W64 0 →
    -- `send` stamps the sender's id into `From`, and node ids are nonzero
    m.From' ≠ W64 0 →
    -- this file: same term, and this node has not voted in it
    m.Term' = s.term →
    s.vote = W64 0 →
    -- `r.step` matches the role
    NStateWf s →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
        -- (stage R4) the message, as `Step` received it
        "Hm" ∷ msgIn ml DFrac.discard ⟨m, ents, sn, ctx, rs⟩ }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #ml))
    {{ (err : GoInterface) (s' : NState), RET #err;
        "Hphys" ∷ ownRaftPhysCV c c.voters r id s' ∗
        "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
        -- `recv` is whatever this branch consumed -- nothing, or the incoming message
        -- once or twice. Naming its elements rather than the list lets
        -- `raft.Step.wp_proof` discharge the `isMessage` side of `ownRaftGhost_step`
        -- from the single fact it holds about `m`.
        "%Hrefines" ∷ ⌜∃ recv, (∀ m' ∈ recv, m' = absMsg .vote m ents) ∧
            StepCD c id B m s recv s'⌝ ∗
        "%Herr" ∷ ⌜err = interface.nil⌝ ∗
        "%Hframe" ∷ ⌜NetFrame s s'⌝ ∗
        "%Hterm" ∷ ⌜TermStep m s s'⌝ }} := by
  intro Hty Hto Hterm Hfnz Heq0 Hv00 Hwf
  -- `MessageType.Enum()`'s receiver: `int32` is not an interface (as in `toConfChangeSingle`)
  haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
  wp_start as ⟨Hphys, Hm⟩
  icases msgPtsC_nn _ _ _ _ _ $$ Hm with ⟨%Hnn, Hm⟩
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  have Hle : ¬ (uint.Z s.term < uint.Z m.Term') := by rw [Heq0]; omega
  have Hnlt : ¬ (uint.Z m.Term' < uint.Z s.term) := by rw [Heq0]; omega
  wp_apply _P.traceReceiveMessage
  try wp_auto
  wp_apply PB.GetTerm.1 $$ [$Hm] as Hm
  -- `m.Term ≠ 0`, so the first arm of the term preamble is skipped
  rw [decide_eq_false Hterm]
  wp_auto
  wp_gets
  wp_apply raft.wp_load_TermC $$ Hphys as Hphys
  wp_gets
  rw [decide_eq_false Hle]
  wp_auto
  wp_gets
  wp_apply raft.wp_load_TermC $$ Hphys as Hphys
  wp_gets
  rw [decide_eq_false Hnlt]
  wp_auto
  -- the type switch: not MsgHup / MsgStorageAppendResp / MsgStorageApplyResp, not
  -- MsgPreVote, but MsgVote
  wp_gets
  rw [Hty]
  try wp_auto
  -- `canVote` is the model's `PCanVote`: the Go expression's third disjunct needs
  -- `MsgPreVote` and is dead here
  wp_gets
  wp_apply raft.wp_load_VoteC $$ Hphys as Hphys
  wp_gets
  rw [Hv00, decide_eq_false (fun h : W64 0 = m.From' => Hfnz h.symm)]
  try wp_auto
  wp_gets
  wp_apply raft.wp_load_VoteC $$ Hphys as Hphys
  wp_gets
  rw [Hv00]
  try wp_auto
  wp_gets
  wp_apply raft.wp_load_leadC $$ Hphys as Hphys
  by_cases Hl0 : s.lead = W64 0
  · -- and recognises no leader: `canVote`
    wp_gets
    rw [Hl0]
    try wp_auto
    have Hcan : PCanVote (toPState s) m.From' := Or.inr ⟨Hv00, toPState_lead_0 s Hl0⟩
    -- each `raftLog` call: load the field, open the log, call, close it again -- the
    -- next field load needs `Hphys`
    wp_gets
    wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
    icases ownRaftPhysC_log_same $$ Hphys with ⟨Hlog, Hlogback⟩
    wp_gets
    wp_apply _P.lastEntryID $$ [$Hlog] as %lastID2 ⟨Hlog, -⟩
    ihave Hphys := Hlogback $$ Hlog
    try wp_auto
    wp_gets
    wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
    icases ownRaftPhysC_log_same $$ Hphys with ⟨Hlog, Hlogback⟩
    wp_gets
    wp_apply _P.isUpToDate $$ [$Hlog] as %ok2 ⟨Hlog, %Hutd⟩
    ihave Hphys := Hlogback $$ Hlog
    cases ok2
    · vote_reject_tail
    · vote_grant_tail
  · -- but a leader is known, so the vote is declined. `canVote`'s second disjunct is
    -- now false, so the program goes on to evaluate the third -- which needs
    -- `MsgPreVote`. This arm therefore discharges one more `decide` than the
    -- `lead = None` one above, which short-circuited to `true`.
    wp_gets
    rw [decide_eq_false Hl0]
    try wp_auto
    ty_ne 17
    try wp_auto
    wp_gets
    wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
    icases ownRaftPhysC_log_same $$ Hphys with ⟨Hlog, Hlogback⟩
    wp_gets
    wp_apply _P.lastEntryID $$ [$Hlog] as %lastID2 ⟨Hlog, -⟩
    ihave Hphys := Hlogback $$ Hlog
    vote_reject_tail

end StepProof

end branches

end EtcdGrove
end Perennial
