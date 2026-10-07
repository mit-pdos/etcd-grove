/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_MsgVote_eq_voted.v.

One case of `Step`'s `MsgVote` branch with `m.Term ≤ r.Term`, in its own file so that
it checks in parallel with the others -- see `proof_raft__Step_MsgVote_le.v`
(`MsgVote_le.lean`), which combines them, and `notes/decisions.md` (2026-09-17;
2026-09-18 for why this directory exists). Proof structure, not specification: no
`Module Type`, no `Parameter`; only `MsgVote_le.lean` may import this module.

Lean notes:
* The branch lemma takes the callee specs (Rocq's functor argument `P : STEP_POSTULATES`)
  as its first argument `_P : raft.Step.Postulates`, and Rocq's section variable `cfg`
  as its second.
* Rocq's `Local Ltac recv_elem` (`∀ m' ∈ recv, m' = a` for the concrete `recv` lists
  `[]`, `[a]`, `[a] ++ [a]`, by rewriting the membership away rather than `set_solver`,
  which took 150s and more there) is not ported.
* Rocq's `Local Ltac vote_grant_tail` and `vote_reject_tail` are not ported. `Step`'s
  `MsgVote` decision has exactly two tails -- grant the vote or decline it -- and the
  code reaches each of them by several routes through the `canVote` computation
  (already voted for this candidate; not voted and no leader; voted for somebody else; a
  leader is known). The program point they start at is in the middle of `Step`'s body,
  so there is no closed expression to state a lemma about; in Rocq they are tactics.
  Grant (in the *current* term): log, `send` the response, and record
  `r.Vote := m.From` (`Step.grantVote`; `can` is the protocol-level `PCanVote` of
  `toPState s`). Decline: log, then `send` a rejection carrying `r.Term`
  (`Step.rejectVote`); always legal. Both start with the log closed (`"Hphys"` whole).
-/
import EtcdGrove.Raft.ElectionProof.Proof.raft__Step.Base

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section branches
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
variable [AllG GF]

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

/-- `MsgVote` with `m.Term = r.Term` and `r.Vote ≠ None`: grant again if the vote was
for this candidate (and its log is up to date), else decline. -/
theorem wp_Step_MsgVote_eq_voted (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (m : raftpb.Message)
    (ents : List raftpb.Entry) :
    m.Type' = MsgVote →
    m.To' = id →
    m.Term' ≠ W64 0 →
    -- `send` stamps the sender's id into `From`, and node ids are nonzero
    m.From' ≠ W64 0 →
    -- this file: same term, and this node has already voted in it
    m.Term' = s.term →
    s.vote ≠ W64 0 →
    -- `r.step` matches the role
    NStateWf s →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        "Hphys" ∷ ownRaftPhys cfg r id s ∗
        -- the message's `Context` is readable and is not the leader-transfer marker:
        -- leader transfer is out of scope
        "#Hctx" ∷ (∃ (ctx : List w8), m.Context' ↦*□ ctx ∗ ⌜ctx ≠ campaignTransfer⌝) }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #m))
    {{ (err : GoInterface) (s' : NState), RET #err;
        "Hphys" ∷ ownRaftPhys cfg r id s' ∗
        "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
        -- `recv` is whatever this branch consumed -- nothing, or the incoming message
        -- once or twice. Naming its elements rather than the list lets
        -- `raft.Step.wp_proof` discharge the `isMessage` side of `ownRaftGhost_step`
        -- from the single fact it holds about `m`.
        "%Hrefines" ∷ ⌜∃ recv, (∀ m' ∈ recv, m' = absMsg .vote m ents) ∧
            Step cfg id (toPState s) recv (toPState s')⌝ ∗
        "%Herr" ∷ ⌜err = interface.nil⌝ }} := by
  -- PORT: proof
  sorry

end StepProof

end branches

end EtcdGrove
end Perennial
