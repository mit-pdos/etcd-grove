/-
Lean-first (no Rocq counterpart).

# Parity B2: the quiet steps of a sync, unbatched node (`antSim_noReadyD_in`, `antSim_silentD_in`)

`QuietIn.noReady` (`HasReady` false at the loop head) and `QuietIn.silentReady` (a `Ready` the harness
does not report, not a `-parallel` leader's: those are `antSim_quietP_in`) over `AntSimD`, as
`antSim_quietP_in`: with no queued write and no split write in progress the node's disk is raft's
state, so B1's `nodeOk_quiet` applies to the run with the driver modes off, and its result is the B2
node part again (#33 parity B2, Sim round 22; the statements are `DrainB2Sync.lean`'s laws).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.QuietP

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntSim

open GMap go_etcd_io.raft.v3 AntCheck

section quietD
variable [GooseExts]

/-- `nodeOk_syncOffD` for every sync, unbatched run: the B2 `SyncDisk` is the driver-modes-off run's. -/
theorem nodeOk_syncOffD' {R : RunCfg} {dec : CCDec} {S0 : State} {net : List Msg} {n : Fin R.N}
    {v w : NodeView} (ha : R.md.async = false) (hb : R.drv.batch = false)
    (hm : v.mems = []) (hdu : v.dur = w.dur) (hun : v.undo = w.undo)
    (hp0 : v.parts = []) (hj : v.jobs = []) (haj : v.ajobs = []) (huf : UndoFacts R w) (hbo : BindingOkM R dec S0)
    (hcl : CandLt v.ps) (hlt : LogTermsLe v.ps) (hsm : SelfMatchLe (nodeId n) v.ps v.qs)
    (h : NodeOk R.syncOff dec (stripU n S0) net n v) : NodeOkD R dec (stripU n S0) net n v := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, hf, hl, hc, hp, hx, hqs, ht, hca, hxc, hlo, hvs⟩ := h
  have hd : v.dur = durOf v.r := (d3 ha rfl rfl rfl).2.1
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15⟩ := hf
  refine ⟨d1, d2, fun _ _ _ _ => d3 ha rfl rfl rfl, d4, d5, d6, d7,
    ⟨fun _ => f1, f2, f3, f4, f5, fun _ => by rw [hm, hp0]; exact f6, f7, f8, f9, f10, f11, f12, f13, f14,
      f15, hcl, hlt, hsm⟩, fun hrl => ?_, fun hrc => ?_, fun _ => hp,
    fun hb' => (by rw [hb] at hb'; cases hb'), hx, fun q hq => .inl (hqs q hq), ht, hca, hxc, hlo, hvs, ?_, ?_, ?_, ?_,
    fun _ _ => (d3 ha rfl rfl rfl).2.2, (memCommitOk_of_disk (S := S0) hbo d1 hd :),
    parWriteOk_nil hm⟩
  · obtain ⟨l1, l2, l3, l4, l5, l6⟩ := hl hrl
    refine ⟨l1, l2, fun j k hk ht => ackX_stripX (stripU_ackX (l3 j k hk ht)),
      fun j hj => (l4 j hj).imp_right fun h => ackX_stripX (stripU_ackX h), fun _ => ⟨l5, ?_⟩⟩
    have hlog : v.dur.log = v.r.full := by rw [hd]; rfl
    rw [hlog]; exact l6
  · obtain ⟨c1, c2⟩ := hc hrc
    exact ⟨c1, fun _ => c2⟩
  · intro d hd'
    rw [hun] at hd'
    obtain ⟨u1, u2, u3⟩ := huf d hd'
    exact ⟨u1, u2, by rw [hdu]; exact u3⟩
  · intro _; rw [hm]; exact hd
  · refine ⟨fun _ => ⟨hj, haj⟩, (by rw [hj]; simp), (by rw [haj]; simp), fun ha' => (by rw [ha] at ha'; cases ha'),
      fun j hj' => (by rw [hj] at hj'; cases hj'), fun ha' => (by rw [ha] at ha'; cases ha')⟩
  · intro ha'; rw [ha] at ha'; cases ha'

/-- **No `Ready` over the B2 relation** (`QuietIn.noReady` over `AntSimD`; `antSim_noReadyD_in.law`). -/
theorem antSim_noReadyD_in :
    ∀ (msk : SimMask), msk ≤ mskB2 →
    ∀ (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → NodeView)
      (net : List Msg) (xnet : List XMsg) (G : RaftFacts) (n : Fin R.N) (r₁ : RState)
      (Adm : List EntryM → CCState → Prop),
      InMask msk R net xnet → AntSimD R dec S V net xnet → RaftLaws G →
      GlobalOk R S net G → R.md.async = false → R.drv.batch = false →
      (V n).mems = [] → (V n).parts = [] →
      ReachIn msk R dec Adm net xnet n (V n) r₁ → r₁.p.outbox = [] → r₁.p.rd.states = [] →
      r₁.p.term = (V n).ps.term → r₁.p.vote = (V n).ps.vote → r₁.p.commit = (V n).ps.commit →
      r₁.p.role = (V n).ps.role → r₁.full = (V n).r.full →
      AntSimD R dec S (setV V n { V n with r := r₁, qs := [] }) net xnet := by
  intro msk hmsk R dec S V net xnet G n r₁ Adm hin hs _ _ ha hb hm hparts hr hob hst hT hV hC hR hF
  obtain ⟨hsh, hbd, hn, hxn, hno⟩ := hs
  have hv := hno n
  have hu : (V n).undo ≠ none → (V n).made = false :=
    hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ha hb
  have hqn : S.queue[n.val]! = [] := by
    have hqi : QueueIs S n (V n) := hv.2.2.2.2.1
    unfold QueueIs at hqi; rw [hqi, hm]; rfl
  have hd : (V n).dur = durOf (V n).r := by
    have := hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hparts
    rw [hm] at this; exact this
  have hjo := hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hfD : NodeFactsD R n (V n) := hv.2.2.2.2.2.2.2.1
  have hcl0 : CandLt (V n).ps := hfD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hlt0 : LogTermsLe (V n).ps := hfD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hsm0 : SelfMatchLe (nodeId n) (V n).ps (V n).qs := hfD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨hmd, -⟩ := hin.syncOff.b1 (SimMask.b1Of_le hmsk)
  have hfp0 : (V n).r.fp = [] :=
    (hfD.2.1 (by rw [show R.md = R.syncOff.md from rfl, hmd])).2.1
  have huf := hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hqn' : (stripU n S).queue[n.val]! = [] := hqn
  have hv' := nodeOk_liftC (R := R.syncOff) hqn' (nodeOkD_syncOff ha hb hm hparts hd hu (nodeOkD_stripU hb hv))
  have hnB1 : NetOk R.syncOff (liftC (stripU n S)) net := netOkD_toB1L ha hsh.2.2.2.2.2.1 (netOkD_stripU n hn)
  have hrP := ReachIn.toP (SimMask.b1Of_le hmsk) hin.syncOff hnB1 hv' hr.syncOff
  have hfp1 : r₁.fp = [] := (reach_fp (SimMask.b1Of_le hmsk) hin.syncOff hv' hr.syncOff).trans hfp0
  have hlog : r₁.p.log = (V n).ps.log := by
    have h1 : r₁.full = r₁.p.log := by unfold RState.full; rw [hfp1]; rfl
    have h2 : (V n).r.full = (V n).ps.log := by unfold RState.full; rw [hfp0]; rfl
    rw [← h1, hF, h2]
  have hM : MatchLe (nodeId n) r₁.p :=
    matchLe_reachP (fun hl => (hsm0 hl).1) (fun m hm => (hnB1.2.2.1 m hm).2.1)
      (fun q hq hne => (hv'.qs q hq).self hne)
      (fun q hq ht => (hsm0 ((hv'.qs q hq).lead_of_app ht)).2 q hq ht) hrP
  have hq : QuietIn msk.b1Of R.syncOff dec Adm net xnet n (V n) { V n with r := r₁, qs := [] } :=
    .noReady _ r₁ hr.syncOff hob hst hT hV hC hR hF
  have h1 := nodeOk_unliftC (R := R.syncOff) hqn'
    (nodeOk_quiet (SimMask.b1Of_le hmsk) hin.syncOff hsh.1
      (netOkD_toB1L ha hsh.2.2.2.2.2.1 (netOkD_stripU n hn)) hv' hq)
  have h2 : NodeOkD R dec S net n { V n with r := r₁, qs := [] } := nodeOkD_unstripU hb
    (nodeOk_syncOffD' ha hb hm rfl rfl hparts ((hjo.1 ha).1) ((hjo.1 ha).2) huf hbd.1
      ((fun hc e he => by
        rw [hlog] at he; rw [hT]; exact hcl0 (hR.symm.trans hc) e he) : CandLt r₁.p)
      ((fun e he => by rw [hlog] at he; rw [hT]; exact hlt0 e he) : LogTermsLe r₁.p)
      ((fun hl => ⟨hM hl, fun q hq _ => by cases hq⟩) : SelfMatchLe (nodeId n) r₁.p [])
      h1)
  refine ⟨hsh, hbd, hn, hxn, fun j => ?_⟩
  unfold setV
  by_cases hj : j = n
  · subst hj; simp only [↓reduceIte]; exact h2
  · simp only [hj, ↓reduceIte]; exact hno j

/-- **A synchronous `Ready` the harness does not report over the B2 relation** (`QuietIn.silentReady`
over `AntSimD`, not a `-parallel` leader's; `antSim_silentD_in.law`). -/
theorem antSim_silentD_in :
    ∀ (msk : SimMask), msk ≤ mskB2 →
    ∀ (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → NodeView)
      (net : List Msg) (xnet : List XMsg) (G : RaftFacts) (n : Fin R.N) (r₁ : RState)
      (rd : ReadyD) (Adm : List EntryM → CCState → Prop),
      InMask msk R net xnet → AntSimD R dec S V net xnet → RaftLaws G →
      GlobalOk R S net G → R.md.async = false → R.drv.batch = false →
      (V n).mems = [] → (V n).parts = [] →
      ReachIn msk R dec Adm net xnet n (V n) r₁ → ReadyOutP R n (V n) r₁ rd →
      ¬ (R.drv.parallel = true ∧ rd.role = .leader) → rd.snap = none → ¬ Reported (V n) rd →
      ReadyFacts G (nodeId n) r₁ →
      AntSimD R dec S (setV V n ((V n).drainOf r₁ rd)) net xnet := by
  intro msk hmsk R dec S V net xnet G n r₁ rd Adm hin hs _ _ ha hb hm hparts hr hrop _ hsnr hrep _
  obtain ⟨hsh, hbd, hn, hxn, hno⟩ := hs
  have hv := hno n
  have hu : (V n).undo ≠ none → (V n).made = false :=
    hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ha hb
  have hqn : S.queue[n.val]! = [] := by
    have hqi : QueueIs S n (V n) := hv.2.2.2.2.1
    unfold QueueIs at hqi; rw [hqi, hm]; rfl
  have hd : (V n).dur = durOf (V n).r := by
    have := hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hparts
    rw [hm] at this; exact this
  have hjo := hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hfD : NodeFactsD R n (V n) := hv.2.2.2.2.2.2.2.1
  have hcl0 : CandLt (V n).ps := hfD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hlt0 : LogTermsLe (V n).ps := hfD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨hmd, -⟩ := hin.syncOff.b1 (SimMask.b1Of_le hmsk)
  have hfp0 : (V n).r.fp = [] :=
    (hfD.2.1 (by rw [show R.md = R.syncOff.md from rfl, hmd])).2.1
  have huf := hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hqn' : (stripU n S).queue[n.val]! = [] := hqn
  have hv' := nodeOk_liftC (R := R.syncOff) hqn' (nodeOkD_syncOff ha hb hm hparts hd hu (nodeOkD_stripU hb hv))
  have hnB1 : NetOk R.syncOff (liftC (stripU n S)) net := netOkD_toB1L ha hsh.2.2.2.2.2.1 (netOkD_stripU n hn)
  have hrP := ReachIn.toP (SimMask.b1Of_le hmsk) hin.syncOff hnB1 hv' hr.syncOff
  have hsm : SelfMatchLe (nodeId n) (accepted r₁).p rd.qs :=
    selfMatchLe_ready hfD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      (fun q hq ht => (hv'.qs q hq).lead_of_app ht) hrP hrop hv'.facts.outbox hv'.leadOk.1
      (fun m hm h4 => ⟨h4, hnB1.2.2.1 m hm⟩) (fun m hm => (hnB1.2.2.1 m hm).2.1)
      (fun q hq hne => (hv'.qs q hq).self hne)
  have hfp1 : r₁.fp = [] := (reach_fp (SimMask.b1Of_le hmsk) hin.syncOff hv' hr.syncOff).trans hfp0
  -- the log and term are the view's (nothing reported)
  have hlog : r₁.p.log = (V n).ps.log ∧ r₁.p.term = (V n).ps.term := by
    have ht : rd.term = (V n).dur.term := Classical.byContradiction fun h => hrep (.inl h)
    have he : rd.ents = [] :=
      Classical.byContradiction fun h => hrep (.inr (.inr (.inr (.inl h))))
    obtain ⟨-, -, hT, -, -, hne, -⟩ := hrop
    have hfull := hne hsnr he
    have h1 : r₁.full = r₁.p.log := by unfold RState.full; rw [hfp1]; rfl
    have h2 : (V n).dur.log = (V n).ps.log := by
      rw [hd]; show (V n).r.fp ++ (V n).r.p.log = _; rw [hfp0]; rfl
    exact ⟨by rw [← h1, hfull, h2], by rw [← hT, ht, hd]; rfl⟩
  have hcand : CandLt r₁.p := by
    intro hc e he
    have hrr : rd.role = .candidate := hrop.1.trans hc
    have hpre0 : rd.pre = false := by
      cases h : rd.pre
      · rfl
      · have := (hrop.2.1 h).1; rw [hrr] at this; cases this
    have hrs : roleStr rd.pre rd.role = roleS (V n) :=
      Classical.byContradiction fun h => hrep (.inr (.inr (.inr (.inr (.inr h)))))
    rw [hpre0, hrr] at hrs
    have hvc : (V n).ps.role = .candidate := by
      revert hrs; unfold roleS roleStr roleOf
      cases hp : (V n).pre <;> cases hr' : (V n).ps.role <;> decide
    rw [hlog.1] at he; rw [hlog.2]; exact hcl0 hvc e he
  have hq : QuietIn msk.b1Of R.syncOff dec Adm net xnet n (V n) ((V n).drainOf r₁ rd) :=
    .silentReady _ r₁ rd hr.syncOff hrop hrep
  have h1 := nodeOk_unliftC (R := R.syncOff) hqn'
    (nodeOk_quiet (SimMask.b1Of_le hmsk) hin.syncOff hsh.1
      (netOkD_toB1L ha hsh.2.2.2.2.2.1 (netOkD_stripU n hn)) hv' hq)
  have h2 : NodeOkD R dec S net n ((V n).drainOf r₁ rd) := nodeOkD_unstripU hb
    (nodeOk_syncOffD' ha hb hm rfl rfl hparts ((hjo.1 ha).1) ((hjo.1 ha).2) huf hbd.1 (hcand :)
      (logTermsLe_quiet (r₁ := r₁) hlt0 hd hfp0 hfp1 hrop hsnr hrep :) hsm h1)
  refine ⟨hsh, hbd, hn, hxn, fun j => ?_⟩
  unfold setV
  by_cases hj : j = n
  · subst hj; simp only [↓reduceIte]; exact h2
  · simp only [hj, ↓reduceIte]; exact hno j

end quietD

end AntSim
end EtcdGrove
end Perennial
