/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_MsgHup.v.

One branch of `Step`'s proof, in its own file so that the branches check in parallel
-- each is a few minutes of `wp_auto` over the same 100k-node body, and in one file they
ran back to back.

This is **proof structure, not specification**: `Step` has exactly one spec, in
`Spec/raft__Step.lean`, and this module has no `Module Type` and no `Parameter`.
Only `Proof/raft__Step.lean`, or another module of `Proof/raft__Step/`, may import
this module; see `notes/decisions.md` (2026-09-17, and 2026-09-18 for why the helpers
moved out of the top-level directory).

Lean notes: the branch lemma takes the callee specs (Rocq's functor argument
`P : STEP_POSTULATES`) as its first argument `_P : raft.Step.Postulates`, and Rocq's
section variable `c` as its second.
-/
module

public import Proof.go_etcd_io.raft.v3.raft__Step.ElectionLemmas

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

/-- `MsgHup` is a local message (`m.Term = 0`), so `Step`'s term preamble is skipped
entirely and it goes straight to `hup`.

Like the other branch lemmas this is ghost-free: it establishes the `Step` witness as a
pure fact, and `raft.Step.wp_proof` turns them into the single `ownRaftGhost_step` of
the whole development. -/
theorem wp_Step_MsgHup (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (PB : raft.Step.PbPostulates (GF := GF) (hG := hG))
    (c : CfgM) (r : Loc) (id : w64) (s : NState) (ml : Loc) (m : MessageM)
    (ents : List EntryM) (sn : Option SnapshotM) (ctx : List w8) (rs : List Loc) :
    m.Type' = MsgHup →
    m.Term' = W64 0 →
    -- an election increments the term; `send` panics if that wraps to zero
    uint.Z s.term + 1 < 2 ^ 64 →
    -- `r.step` matches the role
    NStateWf s →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
        "Hm" ∷ msgIn ml DFrac.discard ⟨m, ents, sn, ctx, rs⟩ }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #ml))
    {{ (err : GoInterface) (s' : NState), RET #err;
        "Hphys" ∷ ownRaftPhysCV c c.voters r id s' ∗
        "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
        "%Hrefines" ∷ ⌜StepCD c id m s [] s'⌝ ∗
        "%Herr" ∷ ⌜err = interface.nil⌝ ∗
        "%Hframe" ∷ ⌜NetFrame s s'⌝ ∗
        "%Hterm" ∷ ⌜TermStep m s s'⌝ }} := by
  intro Hty Hterm Hnowrap Hwf
  wp_start as ⟨Hphys, Hm⟩
  icases msgPtsC_nn _ _ _ _ _ $$ Hm with ⟨%Hnn, Hm⟩
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_apply _P.traceReceiveMessage
  try wp_auto
  wp_apply PB.GetTerm.1 $$ [$Hm] as Hm
  -- `m.Term = 0` (a local message), so the term preamble is skipped
  rw [decide_eq_true Hterm]
  wp_auto
  -- the type switch selects the `MsgHup` case
  wp_apply PB.GetType.1 $$ [$Hm] as Hm
  rw [Hty]
  wp_auto
  -- `hup(campaignPreElection)` with pre-vote on, `hup(campaignElection)` otherwise;
  -- `hup`'s spec covers both
  wp_apply raft.wp_load_preVoteC $$ Hphys as Hphys
  -- (2026-10-14, stage B7) the log facts the campaign guard reads on the full log
  icases ownRaftPhysC_log_same c r id s $$ Hphys with ⟨Hlog, Hback⟩
  icases ownRaftLog_committed _ _ $$ Hlog with ⟨%Hcm, Hlog⟩
  icases ownRaftLog_nowrap _ _ $$ Hlog with ⟨%Hlnw, Hlog⟩
  ihave Hphys := Hback $$ Hlog
  have Hlogf : (s.logst.snap = none → uint.Z s.logst.prev.index' ≤ uint.Z s.logst.applied) ∧
      uint.Z s.logst.applied ≤ uint.Z s.logst.committed ∧ uint.Z s.logst.committed + 1 < 2 ^ 64 :=
    ⟨Hcm.2, Hcm.1.2.1, by have := Hcm.1.2.2; omega⟩
  -- `hup(campaignPreElection)` exactly when `r.preVote`
  cases Hpv : s.prevote
  all_goals
    wp_auto
    wp_apply _P.hup c r id s _ Hnowrap ?Hpvt Hwf $$ [$Hphys]
      as %s' ⟨Hphys, %Hok⟩
    case Hpvt =>
      first
        | exact fun _ => Hpv
        | exact fun h => by
            have := congrArg List.length h
            simp [campaignPreElection] at this
    have HCD := stepCD_hup (m := m) Hok Hnowrap Hlogf
    obtain ⟨Hwf', Hstep, ⟨Hl, Ht1, Ht2, Hpv', Hg'⟩, -⟩ := Hok
    iapply HΦ $$ %interface.nil %s'
    iframe Hphys
    ipureintro
    exact ⟨Hwf', HCD, rfl, NetFrame.of_logst Hl Hpv' Hg', Ht1, fun _ => Ht2,
      fun h _ _ => absurd Hty h, fun _ => by rw [Hl]; exact Int.le_refl _,
      fun h => absurd (Hty.symm.trans h) (by w32_ne)⟩

end StepProof

end branches

end EtcdGrove
end Perennial
