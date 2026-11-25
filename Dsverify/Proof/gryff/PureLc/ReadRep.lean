/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureLc/ReadRep.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit L-c: **L3 for a read's reply** (per step): a read reply output by a step carries a produced
pair's value, and the pair's tag is the step's `readTag` for the reply's key.
-/
module

public import Dsverify.Proof.gryff.PureLc.VInv

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure

open model kahn proto

/-- Read replies among a step's outputs are produced pairs, with the step's `readTag`. -/
def RRep (Q : w64 → model.Tag → Prop) (s : RState) (e : Ev) (o : List Out) : Prop :=
  ∀ cid rid v z, Out.ext (.readReply cid rid v z) ∈ o →
    ∃ vt, QV Q vt ∧ vt.v = v ∧ readTag s (shiftInts rid cid) e = some vt.t

/-- No read reply among the outputs. -/
def NoRR (o : List Out) : Prop := ∀ cid rid v z, Out.ext (.readReply cid rid v z) ∉ o

theorem NoRR.rrep {Q : w64 → model.Tag → Prop} {s : RState} {e : Ev} {o : List Out}
    (h : NoRR o) : RRep Q s e o := fun cid rid v z hm => absurd hm (h cid rid v z)

theorem noRR_of_noR {o : List Out} (h : NoR o) : NoRR o := fun cid rid v z hm => by
  have := h _ hm; simp [isROut] at this

theorem noRR_nil : NoRR [] := fun _ _ _ _ h => by cases h

theorem noRR_sends {o : List Out} (h : ∀ x ∈ o, ∃ d m, x = Out.send d m) : NoRR o :=
  fun cid rid v z hm => by obtain ⟨d, m, e⟩ := h _ hm; cases e

theorem sends_sendTo {q : w32} {m : Msg} {x : Out} (h : sendTo q m = some x) :
    ∀ y ∈ [x], ∃ d m, y = Out.send d m := by
  obtain ⟨d, rfl⟩ := sendTo_some h
  intro y hy; rw [List.mem_singleton.1 hy]; exact ⟨d, m, rfl⟩

theorem sends_sendPeer {s : RState} {q : w32} {m : Msg} {x : Out} (h : sendPeer s q m = some x) :
    ∀ y ∈ [x], ∃ d m, y = Out.send d m := by
  unfold sendPeer at h; split at h
  · cases h
  · exact sends_sendTo h

theorem sends_mapTo {l : List w32} {m : Msg} {r : List Out}
    (h : l.mapM (fun q => sendTo q m) = some r) : ∀ y ∈ r, ∃ d m, y = Out.send d m := by
  intro y hy
  obtain ⟨q, -, hq⟩ := mapM_some_mem h y hy
  obtain ⟨d, rfl⟩ := sendTo_some hq; exact ⟨d, m, rfl⟩

theorem sends_mapPeer {s : RState} {l : List w32} {m : Msg} {r : List Out}
    (h : l.mapM (fun q => sendPeer s q m) = some r) : ∀ y ∈ r, ∃ d m, y = Out.send d m := by
  intro y hy
  obtain ⟨q, -, hq⟩ := mapM_some_mem h y hy
  exact sends_sendPeer hq y (List.mem_singleton_self _)

theorem sends_bcast {s : RState} {m : Msg} {r : List Out} (h : bcast s m = some r) :
    ∀ y ∈ r, ∃ d m, y = Out.send d m := sends_mapPeer h

macro "rr_sends" : tactic => `(tactic| (first
  | exact noRR_nil
  | exact noRR_sends (sends_sendTo ‹sendTo _ _ = some _›)
  | exact noRR_sends (sends_sendPeer ‹sendPeer _ _ _ = some _›)
  | exact noRR_sends (sends_mapTo ‹List.mapM _ _ = some _›)
  | exact noRR_sends (sends_mapPeer ‹List.mapM _ _ = some _›)
  | exact noRR_sends (sends_bcast ‹bcastPreAccept _ _ _ _ _ _ _ _ = some _›)))

/-- A short circuit replies to reads with its value. -/
theorem shortCircuit_rr {s s' : RState} {n : w32} {val : ValTag} {f : Bool} {o : List Out}
    (h : shortCircuit s n val f = some (s', o)) :
    ∀ cid rid v z, Out.ext (.readReply cid rid v z) ∈ o → v = val.v := by
  rcases Perennial.gryff.model.shortCircuit_cases h with h | ⟨rfl, rfl⟩
  rotate_left
  · intro _ _ _ _ h; cases h
  unfold Perennial.gryff.model.shortCircuitReads at h
  opeel h
  all_goals
    cases h
    refine forIn_opt_inv _ _ _ (fun p : RState × List Out => ∀ cid rid v z,
      Out.ext (.readReply cid rid v z) ∈ p.2 → v = val.v) ?_ ?_ _ ‹_›
    · intro _ _ _ _ h; cases h
    intro a b st hb hf
    opeel hf
    all_goals (cases hf; first
      | exact hb
      | (intro cid rid v z hm
         rcases List.mem_append.1 hm with hm | hm
         · exact hb _ _ _ _ hm
         · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
           cases hm; rfl))

theorem shortCircuit_ite_rr {s s' : RState} {c : Prop} [Decidable c] {n : w32} {val : ValTag}
    {f : Bool} {o : List Out}
    (h : (if c then shortCircuit s n val f else some (s, [])) = some (s', o)) :
    ∀ cid rid v z, Out.ext (.readReply cid rid v z) ∈ o → v = val.v := by
  split at h
  · exact shortCircuit_rr h
  · cases h; intro _ _ _ _ h; cases h

section
variable {Q : w64 → model.Tag → Prop}

theorem stepRead2Reply_rr {s s' : RState} {m : Read2ReplyM} {o : List Out}
    (h : stepRead2Reply s m = .ok (s', o)) (hs : VS Q s)
    (hkey : ∀ K rd, s.rops.get? K = some rd → K = shiftInts rd.requestId rd.clientId) :
    RRep Q s (.msg (.read2Reply m)) o := by
  unfold stepRead2Reply at h
  peel h
  all_goals (cases h)
  all_goals first
  | exact noRR_nil.rrep
  | intro cid rid v z hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    cases hm
    have hg := ‹s.rops.get? _ = some _›
    have hv := ‹ReadOp.readValTag _ = some _›
    refine ⟨_, (hs.rops _ _ hg).2 _ hv, rfl, ?_⟩
    unfold readTag
    rw [← hkey _ _ hg, hg]
    simp [hv]

set_option maxHeartbeats 4000000 in
theorem stepRead1Reply_rr {s s' : RState} {m : Read1ReplyM} {o : List Out}
    (h : stepRead1Reply s m = .ok (s', o)) (hs : VS Q s) (hm0 : QV Q m.vt)
    (hkey : ∀ K rd, s.rops.get? K = some rd → K = shiftInts rd.requestId rd.clientId) :
    RRep Q s (.msg (.read1Reply m)) o := by
  unfold stepRead1Reply at h
  peel h
  all_goals (cases h)
  all_goals first
  | exact noRR_nil.rrep
  | (apply NoRR.rrep; rr_sends)
  | (intro cid rid v z hm
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
     cases hm
     have hg := ‹s.rops.get? _ = some _›
     have hrd := hs.rops _ _ hg
     unfold readTag
     rw [← hkey _ _ hg, hg]
     simp only [Option.bind_some]
     refine ⟨_, ?_, rfl, ?_⟩
     all_goals (simp only [VRd, QV] at *)
     all_goals (try split at *)
     all_goals (simp_all; done))

theorem stepWrite2Reply_rr {s s' : RState} {m : Write2ReplyM} {o : List Out}
    (h : stepWrite2Reply s m = .ok (s', o)) (hs : VS Q s) :
    RRep Q s (.msg (.write2Reply m)) o := by
  unfold stepWrite2Reply at h
  peel h
  all_goals (cases h)
  all_goals first
  | exact noRR_nil.rrep
  | (intro cid rid v z hm
     have hg := ‹s.wops.get? _ = some _›
     have hwt := ‹WriteOp.writeTag _ = some _›
     have hsc := ‹(if _ then shortCircuit _ _ _ _ else some _) = some _›
     rcases List.mem_append.1 hm with hm | hm
     · have := shortCircuit_ite_rr hsc _ _ _ _ hm
       subst this
       refine ⟨⟨_, _⟩, (hs.wops _ _ hg).2.2.2 _ hwt, rfl, ?_⟩
       simp only [readTag]; rw [hg]; simpa using hwt
     · simp at hm)

theorem stepWrite1Reply_rr {s s' : RState} {m : Write1ReplyM} {o : List Out}
    (h : stepWrite1Reply s m = .ok (s', o)) (hs : VS Q s) (hm : m.vt.v = -1) :
    RRep Q s (.msg (.write1Reply m)) o := by
  unfold stepWrite1Reply at h
  peel h
  all_goals (cases h)
  all_goals (try (refine (fun hw0 => ?_) (hs.wops _ _ ‹s.wops.get? _ = some _›)
                  obtain ⟨hw1, hw2, hw3, hw4⟩ := hw0
                  have e1 := sge_of_m1 hm
                  have e2 := sge_of_m1 hw2
                  have e3 := sge_of_0 hw1
                  simp only [e1, e2, e3, sge_0_two, Bool.false_eq_true, Bool.and_false,
                    if_false] at *))
  all_goals first
  | exact noRR_nil.rrep
  | (apply NoRR.rrep; rr_sends)

theorem startPhase1_noRR {s s' : RState} {q i b : w32} {ps : List Proposal} {cs : List Cmd}
    {o : List Out} (h : startPhase1 s q i b ps cs = .ok (s', o)) : NoRR o := by
  unfold startPhase1 at h
  peel h
  all_goals (cases h; rr_sends)

/-- **Read replies, per step.** -/
theorem step_rr {r : Fin 3} {s s' : RState} {e : Ev} {o : List Out}
    (h : stepR r s e = .ok (s', o)) (hs : VS Q s) (hm : ∀ m, e.recv = some m → VM Q m)
    (hkey : ∀ K rd, s.rops.get? K = some rd → K = shiftInts rd.requestId rd.clientId) :
    RRep Q s e o := by
  cases e with
  | read =>
    change stepClientRead _ _ _ _ _ = _ at h
    unfold stepClientRead at h; peel h; cases h
    exact (noRR_sends (sends_mapPeer ‹List.mapM _ _ = some o›)).rrep
  | write =>
    change stepClientWrite _ _ _ _ _ _ = _ at h
    unfold stepClientWrite at h; peel h; cases h
    exact (noRR_sends (sends_mapTo ‹List.mapM _ _ = some o›)).rrep
  | rmw =>
    change stepClientRMW _ _ _ _ _ _ _ = _ at h
    unfold stepClientRMW at h; peel h; obtain ⟨-, -, h⟩ := handlePropose_ok h; unfold handleProposeBody at h
    exact (startPhase1_noRR h).rrep
  | msg m =>
    have hm' := hm m rfl
    cases m with
    | read1 =>
      change stepRead1 _ _ = _ at h
      unfold stepRead1 at h; peel h
      all_goals (cases h; apply NoRR.rrep; rr_sends)
    | read2 =>
      change stepRead2 _ _ = _ at h
      unfold stepRead2 at h; peel h
      all_goals (cases h; apply NoRR.rrep; rr_sends)
    | write1 =>
      change stepWrite1 _ _ = _ at h
      unfold stepWrite1 at h; peel h
      all_goals (cases h; apply NoRR.rrep; first | exact noRR_nil | rr_sends)
    | write2 =>
      change stepWrite2 _ _ = _ at h
      unfold stepWrite2 at h; peel h
      all_goals (cases h; apply NoRR.rrep; rr_sends)
    | read1Reply => exact stepRead1Reply_rr h hs hm' hkey
    | read2Reply => exact stepRead2Reply_rr h hs hkey
    | write1Reply => exact stepWrite1Reply_rr h hs hm'
    | write2Reply => exact stepWrite2Reply_rr h hs
    | _ => exact (noRR_of_noR (step_fr_other h rfl).2).rrep
  | _ => exact (noRR_of_noR (step_fr_other h rfl).2).rrep

end

theorem mem_extsIn {o : List Out} {x : Ext} (h : x ∈ extsIn o) : Out.ext x ∈ o := by
  unfold extsIn at h
  obtain ⟨y, hy, hx⟩ := List.mem_filterMap.1 h
  cases y with
  | send _ _ => cases hx
  | ext x' => cases hx; exact hy

/-- **L3 for a read's reply.** -/
theorem prod_read' {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) {o : Op}
    (hi : o.inp = .read) {j : Nat} {v : w64} (hr : readReply l o = some (j, v))
    {t : model.Tag} (ht : readPlace l o = some t) : Prod l v t := by
  -- the reply
  have hr0 := hr
  unfold readReply firstFrom at hr
  obtain ⟨j0, -, hj0⟩ := List.exists_of_findSome?_eq_some hr
  obtain ⟨x, hx, hxv⟩ := List.exists_of_findSome?_eq_some hj0
  split at hxv
  · rename_i cid rid v' z
    split at hxv
    · rename_i hk
      simp only [Option.some.injEq, Prod.mk.injEq] at hxv
      obtain ⟨rfl, rfl⟩ := hxv
      simp only [Prod.mk.injEq] at hk
      obtain ⟨rfl, rfl⟩ := hk
      -- the place
      unfold readPlace at ht
      rw [hr0] at ht
      simp only [Option.bind_some] at ht
      split at ht
      · rename_i e he
        obtain ⟨n, s', outs, hn, hc, hs, -, ho⟩ := proj_step h he
        obtain ⟨-, -, -, -, -, -, hrecv⟩ := grun_label h hn
        obtain ⟨cn, hcn, -, h3⟩ := grun_cut h n
        have hst : stR cn o.r = stOf o.r ((projR l o.r).take j0) := by
          rw [← hc]; obtain ⟨o', ho'⟩ := h3 o.r; unfold cutSt; rw [stOf_of_runP ho']; rfl
        have hvi := vinv h _ _ hcn (List.take_prefix n l)
        have hvs := (hvi o.r).1
        rw [hst] at hvs
        have hm : ∀ m, e.recv = some m → VM (QL l) m := by
          intro m hm
          obtain ⟨cn', hin, hrun⟩ := hrecv m hm
          have := (vinv h _ _ hrun (List.take_prefix n l) o.r).2 m hin
          exact this
        have hkey' : ∀ K rd, (stOf o.r ((projR l o.r).take j0)).rops.get? K = some rd →
            K = shiftInts rd.requestId rd.clientId := by
          intro K rd hK; rw [← hst] at hK; exact ((rinv hcn).2.1.rops o.r K rd hK).2.1
        rw [ho] at hx
        obtain ⟨vt, hq, hv, htag⟩ := step_rr hs hvs hm hkey' _ _ _ _ (mem_extsIn hx)
        have : Op.key o = shiftInts o.rid o.cid := rfl
        rw [← this, ht] at htag
        cases htag
        rw [← hv]; exact hq.1
      · cases ht
    · cases hxv
  · cases hxv

end Perennial.gryff.pure
