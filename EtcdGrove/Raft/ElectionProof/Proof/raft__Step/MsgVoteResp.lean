/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_MsgVoteResp.v.

One branch of `Step`'s proof, in its own file so that the branches check in parallel
-- each is a few minutes of `wp_auto` over the same 100k-node body, and in one file they
ran back to back.

This is **proof structure, not specification**: `Step` has exactly one spec, in
`Spec/raft__Step.lean`, and this module has no `Module Type` and no `Parameter`.
Only `Proof/raft__Step.lean`, or another module of `Proof/raft__Step/`, may import
this module; see `notes/decisions.md` (2026-09-17, and 2026-09-18 for why the helpers
moved out of the top-level directory).

Lean notes:
* The branch lemma takes the callee specs (Rocq's functor argument `P : STEP_POSTULATES`)
  as its first argument `_P : raft.Step.Postulates`, and Rocq's section variable `cfg`
  as its second.
* Rocq's `Local Ltac recv_elem` (`∀ m' ∈ recv, m' = a` for the concrete `recv` lists
  `[]`, `[a]`, `[a] ++ [a]`, by rewriting the membership away rather than `set_solver`,
  which took 150s and more there) is not ported.
* Rocq's `Local Ltac wp_load_step` (the load of `r.step` in `r.step(r, m)`, bound by
  hand with `wp_bind` because `wp_apply` did not find it in the function position of an
  application, 2026-09-24) is not ported; `MsgBeat.lean` uses
  `wp_apply raft.wp_load_step $$ Hphys as Hphys` there.
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

/-- `MsgVoteResp`: the term preamble, then `r.step(m)`.

The one branch where all three `stepX` can run, so it is also the one that needs the
`r.step` field pinned to the role: `raft.wp_load_step` loads `s.stepfn`, and `NStateWf`
says it is `stepFuncOf s.role` -- without that there is nothing to apply at
`r.step(m)`. Three term cases, and the third splits three ways:

- `m.Term > r.Term`: a `VoteResp` is not `fromLeader`, so the preamble runs
  `becomeFollower(m.Term, None)` rather than adopting a leader. The role is `follower`
  afterwards, so `r.step` is `stepFollower`, which has no `MsgVoteResp` arm. One
  `Step.higherTerm`.
- `m.Term < r.Term`: with `checkQuorum` and `preVote` both off, and a `MsgVoteResp`
  being neither `MsgPreVote` nor `MsgStorageAppendResp`, every arm of the chain is
  skipped but the last, which only logs. Then `return nil`. `Step.refl`, with
  `recv = []` -- the message is dropped, which the model always permits.
- `m.Term = r.Term`: straight to the type switch's default arm. `stepFollower` and
  `stepLeader` only read, so again `Step.refl`; `stepCandidate` records the vote and
  may win or lose in the same call, which is `Step.recordVote` followed by `Step.win` /
  `Step.lose`, on its `won`/`lost` flags. -/
theorem wp_Step_MsgVoteResp (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (m : raftpb.Message)
    (ents : List raftpb.Entry) :
    m.Type' = MsgVoteResp →
    m.To' = id →
    m.Term' ≠ W64 0 →
    -- `stepCandidate` needs it; `Step` is the outermost caller
    id ∈ cfg →
    NStateWf s →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        "Hphys" ∷ ownRaftPhys cfg r id s }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #m))
    {{ (err : GoInterface) (s' : NState), RET #err;
        "Hphys" ∷ ownRaftPhys cfg r id s' ∗
        "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
        "%Hrefines" ∷ ⌜∃ recv, (∀ m' ∈ recv, m' = absMsg .voteResp m ents) ∧
            Step cfg id (toPState s) recv (toPState s')⌝ ∗
        "%Herr" ∷ ⌜err = interface.nil⌝ }} := by
  -- PORT: proof
  sorry

end StepProof

end branches

end EtcdGrove
end Perennial
