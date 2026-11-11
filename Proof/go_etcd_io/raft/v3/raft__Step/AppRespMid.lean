/-
Lean-first (no Rocq counterpart). **`Step`'s `MsgAppResp` arm past `maybeCommit`** (2026-11-11,
trace-check Q8 stage 1 slice 28c, `notes/decisions.md`, "Q8 stage 1 (slice 28c)"): a traced caller's
family moves raft's ghost state past the accepted response and the commit inside `"Hgcommit"` (the
`Commit` line's facts read the new commit), and gives it back there (`CloseMid`'s third case: the state
after `maybeCommit`, `commitAt { s with prvals := pvs } b N`); `Step` then steps the rest alone from
there (the release and the appends: `appResp_rest`, the tail of `leader_appresp_step`), with the whole
step's model witness, the mode unchanged. The `MsgAppResp` versions of `VoteWin.lean`'s
`stepOut_vote_md`, `stepOut_of_stepCD_vote`, `gmodePre_vote`.

Proof structure, not specification: only `Proof/raft__Step.lean` imports it.
-/
module

public import Proof.go_etcd_io.raft.v3.raft__Step.VoteWin
public import Proof.go_etcd_io.raft.v3.raft__Step.resp_lemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section pure
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext] [GoSemanticsFunctions]

namespace StepProof

/-- An append response's step keeps the mode (`GMove`: no ghost part moves). -/
theorem stepOut_appResp_md {md md' : GMode} {c : CfgM} {id : w64} {m : MessageM} {s s' : NState}
    (hty : m.Type' = MsgAppResp) (h : md.StepOut c id m s s' md') : md' = md := by
  cases md with
  | static => exact h.1
  | dyn dec c0 h0 g =>
    obtain ⟨g', hmv, rfl, -⟩ := h
    rcases hmv with ⟨h1, -⟩ | rfl | ⟨h1, -⟩ | ⟨h1, -⟩
    · exact absurd (hty.symm.trans h1) (by w32_ne)
    · rfl
    · exact absurd (hty.symm.trans h1) (by w32_ne)
    · exact absurd (hty.symm.trans h1) (by w32_ne)

/-- **An append response's whole step, the model's witness at the mode unchanged** (`StepCD`, the
dynamic premises at `s`). -/
theorem stepOut_of_stepCD_appResp {md : GMode} {c : CfgM} {id : w64} {m : MessageM} {s s' : NState}
    {B : Int} {recv : List Msg} (Hstep : StepCD c id B m s recv s') (hty : m.Type' = MsgAppResp)
    (Hdyn : ∀ dec c0 h0 g, md = .dyn dec c0 h0 g → g.cfg.cfg = c ∧ DynHyp (effDec dec g.decs) m s s' g) :
    md.StepOut c id m s s' md := by
  cases md with
  | static => exact ⟨rfl, B, recv, Hstep.1⟩
  | dyn dec c0 h0 g =>
    obtain ⟨hc, hd⟩ := Hdyn dec c0 h0 g rfl
    obtain ⟨cidx', Hcm, HR⟩ := Hstep.2 (AdmFold (effDec dec g.decs) c0) (effDec dec g.decs) g hc hd
    have hci : cidx' = g.cidx := by
      rcases Hcm with h | ⟨h, -⟩
      · exact h
      · exact absurd (hty.symm.trans h) (by w32_ne)
    subst hci
    exact ⟨g, .inr (.inl rfl), rfl, B, recv, HR⟩

/-- The dynamic premises of an append response at a state that is no pre-candidate. -/
theorem gmodePre_appResp {md : GMode} {m : MessageM} {ents : List EntryM} {s1 : NState}
    (hty : m.Type' = MsgAppResp) (hrole : s1.role ≠ .preCandidate) : md.Pre m ents s1 := by
  cases md with
  | static => trivial
  | dyn dec c0 h0 g =>
    exact ⟨fun _ hp => absurd hp hrole,
      fun h => absurd (hty.symm.trans h) (by w32_ne), fun h => absurd (hty.symm.trans h) (by w32_ne)⟩

/-- The state after `maybeCommit`'s outcome has `s`'s outbox. -/
theorem commitAt_outbox (s : NState) (pvs : GMap w64 Progress) (b : Bool) (N : w64) :
    (commitAt { s with prvals := pvs } b N).outbox = s.outbox := by
  cases b <;> rfl

theorem commitAt_gh' (s : NState) (pvs : GMap w64 Progress) (b : Bool) (N : w64) :
    (commitAt { s with prvals := pvs } b N).gh = s.gh := by
  cases b <;> rfl

theorem commitAt_storage (s : NState) (pvs : GMap w64 Progress) (b : Bool) (N : w64) :
    (commitAt { s with prvals := pvs } b N).logst.storage = s.logst.storage := by
  cases b <;> rfl

theorem commitAt_role (s : NState) (pvs : GMap w64 Progress) (b : Bool) (N : w64) :
    (commitAt { s with prvals := pvs } b N).role = s.role := by
  cases b <;> rfl

/-- The new messages' numbers from the state after `maybeCommit` (whose outbox is `s`'s). -/
theorem outTrStep_commitAt (s : NState) (pvs : GMap w64 Progress) (b : Bool) (N : w64) (s' : NState)
    (h : OutTrStep s s') : OutTrStep (commitAt { s with prvals := pvs } b N) s' := by
  intro htr x hx
  rcases h (by rw [commitAt_gh'] at htr; exact htr) x hx with h1 | h1
  · left; rw [commitAt_outbox]; exact h1
  · right; exact h1

/-- **The rest of an accepted append response's step, from the state after `maybeCommit`** (the tail of
`leader_appresp_step`): the end state's log the committed state's (`hlog`), so the step's commit index
is `s1`'s; from there the release (`StepC.readRelease` and the heartbeats, or a single voter's
`StepC.readReleaseSingle`) when it committed, then the appends (`StepC.sendApps`), receiving nothing. -/
theorem appResp_rest {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM} {ctx : List w8}
    {s s' : NState} (B : Int) (pvs1 : GMap w64 Progress) (b : Bool) (N : w64)
    (hty : m.Type' = MsgAppResp) (hrole : s.role = .leader) (hterm : m.Term' = s.term)
    (hrej : m.Reject' = false) (hdom : m.From' ∈ domSet s.progress)
    (hpm1 : prvalsMatch pvs1 = appRespMatch s m.From' m.Index')
    (Hend : StepEnd c id m ents ctx s s')
    (hlog : (commitAt { s with prvals := pvs1 } b N).logst = s'.logst)
    (Hpc : domSet s.progress ⊆ c.voters ∪ c.learners) :
    StepCD c id B m (commitAt { s with prvals := pvs1 } b N) [] s' := by
  have hety : StepEndTy m.Type' := by rw [hty]; unfold StepEndTy; simp
  have hns : ¬ StaleMsg s m := fun h => absurd h.2 (by rw [hterm]; omega)
  have hnh : m.Type' ≠ MsgHup := by rw [hty]; w32_ne
  have hnv : m.Type' ≠ MsgVote := by rw [hty]; w32_ne
  have hnbf : ¬ PreBF m s := fun h => absurd h.1 (by rw [hterm]; omega)
  obtain ⟨pvs0, h⟩ := (Hend hety).2.2.2 hns hnh hnv
  rw [show preState s m pvs0 = s by simp [preState, hnbf]] at h
  obtain ⟨d, H⟩ := h.2.2 hrole
  unfold LeaderStepResultC at H
  rw [ite_eq_right (by rw [hty]; w32_ne)] at H
  obtain ⟨-, Hres⟩ := H
  unfold LeaderNonpropResultC at Hres
  rcases Hres with ⟨Hc, -⟩ | ⟨Hc, -⟩ | ⟨Hc, -⟩ | ⟨Hc, -⟩ | ⟨-, Hres⟩ | ⟨Hc6, -⟩ | ⟨Hc7, -⟩
  rotate_right
  · exfalso; rw [hty] at Hc7; exact absurd Hc7 (by w32_ne)
  rotate_right
  · exfalso
    rcases Hc6 with h6 | h6 | h6 | h6 | h6 <;> rw [hty] at h6 <;> exact absurd h6 (by w32_ne)
  · exfalso; rw [hty] at Hc
    rcases Hc with Hc | Hc | Hc | Hc | Hc <;> exact absurd Hc (by w32_ne)
  · exfalso; rw [hty] at Hc; exact absurd Hc (by w32_ne)
  · exfalso; rw [hty] at Hc; exact absurd Hc (by w32_ne)
  · exfalso; rw [hty] at Hc; exact absurd Hc (by w32_ne)
  rcases Hres with ⟨hnd, -⟩ | ⟨-, hr, -⟩ | ⟨-, -, Hacc⟩
  · exact absurd hdom hnd
  · rw [hrej] at hr; cases hr
  obtain ⟨x, pvs, n0, hb, ms, Hx, Hpvs, Hc, -, -, Hms, Hrel⟩ := Hacc
  have Hpr : (toPState s).role = .leader := by rw [toPState_role, hrole]; rfl
  have Hpr1 : (toPState { s with prvals := pvs }).role = .leader := Hpr
  have hpm : prvalsMatch pvs1 = prvalsMatch pvs := by
    rw [hpm1, Hpvs, appRespMatch_of_some s _ _ x Hx]
  -- the state after `maybeCommit` is `s` at `pvs1` committed at the end state's commit index
  have hs1 : s'.logst = { s.logst with committed := n0 } →
      commitAt { s with prvals := pvs1 } b N =
        { s with prvals := pvs1, logst := { s.logst with committed := n0 } } := by
    intro hX
    rw [hX] at hlog
    cases b
    · simp only [commitAt_false] at hlog ⊢
      rw [← hlog]
    · simp only [commitAt_true] at hlog ⊢
      rw [hlog]
  have hT : toPState ({ s with prvals := pvs1, logst := { s.logst with committed := n0 } } : NState) =
      { toPState { s with prvals := pvs } with commit := n0 } := by
    simp [toPState, hrole, hpm]
  by_cases Hcc : n0 = s.logst.committed
  · rw [if_pos Hcc] at Hrel
    obtain ⟨-, rfl⟩ := Hrel
    rw [hs1 rfl]
    refine StepCD.frame ?_ ⟨rfl, rfl, fun _ => ⟨hrole, rfl⟩⟩
    have H3 : StepCF c id { toPState { s with prvals := pvs } with commit := n0 } []
        (psendMsgs { toPState { s with prvals := pvs } with commit := n0 } ms) :=
      .sendApps _ ms Hpr1 (fun m' Hm' =>
        replOk_proper _ _ _ _ rfl rfl rfl rfl (Hms m' Hm').1)
        (fun m' Hm' h => (Hms m' Hm').2.1 h) (Hms.snapTo Hpc)
    have He : toPState { sendMsgs { s with logst := { s.logst with committed := n0 } } ms with
          prvals := pvs } =
        psendMsgs { toPState { s with prvals := pvs } with commit := n0 } ms := by
      simp [toPState, sendMsgs, psendMsgs, hrole]
    rw [hT, He]
    exact H3
  rw [if_neg Hcc] at Hrel
  rcases Hc with Hc | ⟨Hlt, Hle, Hterm, Hq⟩
  · exact absurd Hc Hcc
  let ps2 : PState := { toPState { s with prvals := pvs } with commit := n0 }
  rcases Hrel with ⟨-, Hhb, rfl⟩ | ⟨Hsg, -, rfl⟩
  · rw [hs1 rfl]
    refine StepCD.frame ?_ ⟨rfl, rfl, fun _ => ⟨hrole, rfl⟩⟩
    have H3 : StepCF c id ps2 []
        { ps2 with rd := { ps2.rd with
            pend := []
            ro := readonlyRelease ps2.rd.ro id ps2.commit ps2.rd.pend } } :=
      .readRelease _ Hpr1 Hterm
    let ps3 : PState := { ps2 with rd := { ps2.rd with
            pend := []
            ro := readonlyRelease ps2.rd.ro id ps2.commit ps2.rd.pend } }
    have H4 : StepCF c id ps3 [] (psendMsgs ps3 hb) :=
      .beat _ hb Hpr1
        (fun m' h => by
          have := (Hhb m' h).1
          unfold HeartbeatOk matchOf at this ⊢
          simpa [ps3, ps2, toPState, hrole] using this)
        (fun m' h => by
          obtain ⟨k, -, -, Hk⟩ := (Hhb m' h).2
          rw [Hk]
          have : ps3.rd.ro = readonlyRelease s.rd.ro id n0 s.rd.pend := by
            simp [ps3, ps2, toPState, hrole]
          rw [this]
          exact HbCtxOk_release _ _ _ _ k)
    have H5 : StepCF c id (psendMsgs ps3 hb) [] (psendMsgs (psendMsgs ps3 hb) ms) :=
      .sendApps _ ms Hpr1 (fun m' Hm' =>
        replOk_proper _ _ _ _ rfl rfl rfl rfl (Hms m' Hm').1)
        (fun m' Hm' h => (Hms m' Hm').2.1 h) (Hms.snapTo Hpc)
    have He : toPState { sendMsgs (sendMsgs (releasedState id
          { s with logst := { s.logst with committed := n0 } }) hb) ms with prvals := pvs } =
        psendMsgs (psendMsgs ps3 hb) ms := by
      simp [ps3, ps2, toPState, sendMsgs, psendMsgs, releasedState, hrole]
    rw [hT, He]
    exact .trans _ _ _ _ _ H3 (.trans _ _ _ _ _ H4 H5)
  · obtain ⟨o4, rd4, H4e⟩ := readRespondAll_eq id
      ({ s with logst := { s.logst with committed := n0 }, rd := { s.rd with pend := [] } } : NState)
      (pendReqs { s with logst := { s.logst with committed := n0 } })
    rw [hs1 (by rw [H4e]; rfl)]
    refine StepCD.frame ?_ (by rw [H4e]; exact ⟨rfl, rfl, fun _ => ⟨hrole, rfl⟩⟩)
    have H3 : StepCF c id ps2 []
        (preadRespondAll id { ps2 with rd := { ps2.rd with pend := [] } }
          (ps2.rd.pend.map (fun p => ⟨ps2.commit, p.1.From', p.2⟩))) :=
      .readReleaseSingle _ Hpr1 Hterm Hsg
    obtain ⟨o3, rd3, H3e⟩ := preadRespondAll_eq id ({ ps2 with rd := { ps2.rd with pend := [] } })
      (ps2.rd.pend.map (fun p => ⟨ps2.commit, p.1.From', p.2⟩))
    rw [H3e] at H3
    have H5 : StepCF c id { ({ ps2 with rd := { ps2.rd with pend := [] } }) with
          outbox := o3, rd := rd3 } []
        (psendMsgs { ({ ps2 with rd := { ps2.rd with pend := [] } }) with
          outbox := o3, rd := rd3 } ms) :=
      .sendApps _ ms Hpr1 (fun m' Hm' =>
        replOk_proper _ _ _ _ rfl rfl rfl rfl (Hms m' Hm').1)
        (fun m' Hm' h => (Hms m' Hm').2.1 h) (Hms.snapTo Hpc)
    have He : toPState { sendMsgs (readRespondAll id
          { s with logst := { s.logst with committed := n0 }, rd := { s.rd with pend := [] } }
          (pendReqs { s with logst := { s.logst with committed := n0 } })) ms with
          prvals := pvs } =
        psendMsgs { ({ ps2 with rd := { ps2.rd with pend := [] } }) with
          outbox := o3, rd := rd3 } ms := by
      rw [← H3e]
      have Hpv := readRespondAll_prvals id
        ({ s with logst := { s.logst with committed := n0 }, rd := { s.rd with pend := [] } } : NState)
        pvs (pendReqs { s with logst := { s.logst with committed := n0 } })
      have e1 : ({ sendMsgs (readRespondAll id
          ({ s with logst := { s.logst with committed := n0 }, rd := { s.rd with pend := [] } } : NState)
          (pendReqs { s with logst := { s.logst with committed := n0 } })) ms with
          prvals := pvs } : NState) =
          sendMsgs ({ readRespondAll id
          ({ s with logst := { s.logst with committed := n0 }, rd := { s.rd with pend := [] } } : NState)
          (pendReqs { s with logst := { s.logst with committed := n0 } }) with prvals := pvs }) ms :=
        rfl
      rw [e1, ← Hpv, toPState_sendMsgs, toPState_readRespondAll id _ (by exact hrole)]
      simp [ps2, pendReqs, toPState, hrole]
    rw [hT, He]
    exact .trans _ _ _ _ _ H3 H5

end StepProof

end pure

end EtcdGrove
end Perennial
