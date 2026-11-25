/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureA/StepBase.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit A1, internal: the common part of the step cases of `inv_step` (`Inv.lean`, `Step*.lean`).
* transport: `CopyOk`, `InstOk`, `MsgOk` only look at the copies of their instance (and, for a
  ballot-0 PreAccept, at the multiplicity of its message): `copyOk_congr`, `instOk_congr`,
  `msgOk_congr`;
* `inv_quiet`: a step that changes no replica's id, instance space nor `crtInstance`, consumes at
  most a message outside EPaxos (`isEp`) and sends none keeps `CInv` with the same history: the
  Gryff handlers (`quiet_*`: their outputs are Gryff messages) and `forceWrite`;
* `StepInv`, the conclusion of a step case.
-/
module

public import Dsverify.Proof.gryff.PureA.Exec

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pureA

open Perennial Perennial.gryff.model Perennial.gryff.pure Perennial.gryff.kahn

/-! ## Transport -/

theorem balOf_congr {c c1 : Cfg gNet} {q i : w32} (h : ∀ a, cpOf c1 a q i = cpOf c a q i) :
    balOf c1 q i = balOf c q i := by
  funext a; simp only [balOf, h]

theorem copyOk_congr {c c1 : Cfg gNet} {G : GG} {q i : w32} {a : Fin 3} {cp : Copy}
    (hb : balOf c1 q i = balOf c q i) (h : CopyOk c G q i a cp) : CopyOk c1 G q i a cp :=
  { h with preparing := by rw [hb]; exact h.preparing }

theorem instOk_congr {c c1 : Cfg gNet} {G : GG} {q i : w32} (h : ∀ a, cpOf c1 a q i = cpOf c a q i)
    (I : InstOk c G q i) : InstOk c1 G q i := by
  have hb := balOf_congr h
  exact
    { ainv := hb ▸ I.ainv
      copies := fun a cp hc => copyOk_congr hb (I.copies a cp ((h a).symm.trans hc))
      noCopy := fun a hc => I.noCopy a ((h a).symm.trans hc)
      fastL := fun v hv => by rw [h]; exact I.fastL v hv
      leaderCopy := fun ⟨a, cp, hc⟩ => by
        rw [h]; exact I.leaderCopy ⟨a, cp, (h a).symm.trans hc⟩
      ownMono := fun b R hR hp => by rw [hb]; exact I.ownMono b R hR hp
      fresh := fun hn => I.fresh fun a => (h a).symm.trans (hn a) }

/-- The EPaxos messages (the others' `MsgOk` is `True`). -/
def isEp : Msg → Bool
  | .preAccept _ | .preAcceptReply _ | .preAcceptOK _ | .accept _ | .acceptReply _ | .commit _
  | .prepare _ | .prepareReply _ => true
  | _ => false

theorem msgOk_quiet {c : Cfg gNet} {G : GG} {d : Fin 3} {m : Msg} (h : isEp m = false) :
    MsgOk c G d m := by
  cases m <;> first | trivial | cases h

theorem msgOk_congr {c c1 : Cfg gNet} {G : GG} {d : Fin 3} {m : Msg}
    (hcp : ∀ q j, msgInst m = some (q, j) → ∀ a, cpOf c1 a q j = cpOf c a q j)
    (hcnt : ∀ x, m = .preAccept x → (c.inflight d).count (Msg.preAccept x : gNet.M) = 1 →
      (c1.inflight d).count (Msg.preAccept x : gNet.M) = 1)
    (h : MsgOk c G d m) : MsgOk c1 G d m := by
  cases m with
  | preAccept x =>
    have e := hcp _ _ rfl
    have ec := hcnt x rfl
    unfold MsgOk at h ⊢
    simp only [e] at h ⊢
    exact ⟨fun hb => let k := h.1 hb; ⟨k.1, k.2.1, k.2.2.1, k.2.2.2.1, ec k.2.2.2.2⟩, h.2⟩
  | prepare x =>
    have e := balOf_congr (hcp _ _ rfl)
    simp only [MsgOk, e] at h ⊢; exact h
  | prepareReply x =>
    have e := balOf_congr (hcp _ _ rfl)
    simp only [MsgOk, e] at h ⊢; exact h
  | _ => exact h

/-! ## Steps outside EPaxos -/

/-- The step's result as `kahn.GStep` gives it. -/
def Post (c : Cfg gNet) (a : Fin 3) (e : Ev) (s' : RState) (o : List Out) (c1 : Cfg gNet) : Prop :=
  c1.st = (fun j => if j = a then s' else c.st j) ∧
    c1.inflight = (fun j =>
      (if j = a then consume (gNet.recv e) (c.inflight j) else c.inflight j) ++ sentTo gNet j o)

/-- No EPaxos message among the outputs. -/
def QuietO (o : List Out) : Prop := ∀ d m, Out.send d m ∈ o → isEp m = false

theorem sentTo_quiet {o : List Out} (h : QuietO o) {j : Fin 3} {m : Msg}
    (hm : m ∈ sentTo gNet j o) : isEp m = false := by
  unfold sentTo at hm
  obtain ⟨y, hy, hy'⟩ := List.mem_filterMap.1 hm
  cases y with
  | send d m' =>
    simp only at hy'
    split at hy'
    · cases hy'; subst_vars; exact h _ _ hy
    · cases hy'
  | ext x => cases hy'

/-- The in-flight messages after a quiet step: a sublist of the old ones plus quiet messages. -/
theorem quiet_inflight {c c1 : Cfg gNet} {a : Fin 3} {e : Ev} {s' : RState} {o : List Out}
    (hp : Post c a e s' o c1) (ho : QuietO o) (d : Fin 3) :
    ∃ l : List gNet.M, List.Sublist l (c.inflight d) ∧ c1.inflight d = l ++ sentTo gNet d o ∧
      (∀ m, m ∈ sentTo gNet d o → isEp m = false) := by
  refine ⟨if d = a then consume (gNet.recv e) (c.inflight d) else c.inflight d, ?_, by rw [hp.2],
    fun m hm => sentTo_quiet ho hm⟩
  split
  · unfold consume; split
    · exact List.erase_sublist
    · exact List.Sublist.refl _
  · exact List.Sublist.refl _

theorem countP_quiet {l l' new : List Msg} (hs : List.Sublist l l')
    (hn : ∀ m, m ∈ new → isEp m = false) {p : Msg → Bool} (hp : ∀ m, isEp m = false → p m = false) :
    (l ++ new).countP p ≤ l'.countP p := by
  rw [List.countP_append]
  have : new.countP p = 0 := List.countP_eq_zero.2 fun m hm => by rw [hp m (hn m hm)]; simp
  rw [this]; exact Nat.le_trans (Nat.le_of_eq (Nat.add_zero _)) hs.countP_le

/-- **A quiet step** keeps the invariant with the same history. -/
theorem inv_quiet {c c1 : Cfg gNet} {G : GG} {a : Fin 3} {e : Ev} {s' : RState} {o : List Out}
    (I : CInv c G) (hp : Post c a e s' o c1) (hf : Frame (c.st a) s') (ho : QuietO o) :
    CInv c1 G ∧ ∀ q i, Evolve (rowOf q) (G q i) (balOf c q i) (G q i) (balOf c1 q i) := by
  have hst : ∀ j : Fin 3, Frame (c.st j) (c1.st j) := fun j => by
    rw [hp.1]
    by_cases h : j = a
    · subst h; simp only [ite_true]; exact hf
    · simp only [h, ite_false]; exact ⟨rfl, rfl, rfl⟩
  have hcp : ∀ a q i, cpOf c1 a q i = cpOf c a q i := fun a q i => by
    simp only [cpOf, (hst a).2.1]
  have hcrt : ∀ (j : Fin 3) q, (c1.st j).crt q = (c.st j).crt q := fun j q => by
    simp only [RState.crt, (hst j).2.2]
  have hinf := quiet_inflight hp ho
  have hmem : ∀ d m, m ∈ c1.inflight d → isEp m = true → m ∈ c.inflight d := fun d m hm he => by
    obtain ⟨l, hs, hl, hn⟩ := hinf d
    rw [hl] at hm
    rcases List.mem_append.1 hm with h | h
    · exact hs.subset h
    · rw [hn m h] at he; cases he
  have hcntle : ∀ d (p : Msg → Bool), (∀ m, isEp m = false → p m = false) →
      (c1.inflight d).countP p ≤ (c.inflight d).countP p := fun d p hpq => by
    obtain ⟨l, hs, hl, hn⟩ := hinf d
    rw [hl]; exact countP_quiet hs hn hpq
  refine ⟨{ ids := ?_, inst := ?_, msgs := ?_, crtOwn := ?_, copyBelow := ?_, msgBelow := ?_,
            crtLen := ?_, leaderHas := ?_, prepMult := ?_ }, fun q i => ?_⟩
  · intro j; rw [(hst j).1]; exact I.ids j
  · intro q i; exact instOk_congr (fun a => hcp a q i) (I.inst q i)
  · intro d m hm
    cases hq : isEp m
    · exact msgOk_quiet hq
    · refine msgOk_congr (fun q j _ a => hcp a q j) (fun x hx h3 => ?_) (I.msgs d m (hmem d m hm hq))
      subst hx
      have h1 := hcntle d (fun y => y == (Msg.preAccept x : gNet.M)) (fun y hy => by
        cases y <;> simp_all [isEp])
      have h2 : 0 < (c1.inflight d).count (Msg.preAccept x : gNet.M) := List.count_pos_iff.2 hm
      have e1 : (c1.inflight d).count (Msg.preAccept x : gNet.M) =
          (c1.inflight d).countP (fun y => y == (Msg.preAccept x : gNet.M)) := rfl
      have e2 : (c.inflight d).count (Msg.preAccept x : gNet.M) =
          (c.inflight d).countP (fun y => y == (Msg.preAccept x : gNet.M)) := rfl
      omega
  · intro j q; rw [hcrt, hcrt]; exact I.crtOwn j q
  · intro j q i cp hc; rw [hcrt]; exact I.copyBelow j q i cp ((hcp j q i).symm.trans hc)
  · intro d m q j hm hj
    rw [hcrt]
    have he : isEp m = true := by cases m <;> simp_all [msgInst, isEp]
    exact I.msgBelow d m q j (hmem d m hm he) hj
  · intro j; rw [(hst j).2.2]; exact I.crtLen j
  · intro q j h0 h1; rw [hcrt] at h1; rw [hcp]; exact I.leaderHas q j h0 h1
  · intro R q i cp lb hc h1 h2 h3 h4
    obtain ⟨k1, k2⟩ := I.prepMult R q i cp lb ((hcp R q i).symm.trans hc) h1 h2 h3 h4
    have hP : ∀ m, isEp m = false → isPrepareAt q i cp.ballot m = false := fun m hm => by
      cases m <;> simp_all [isEp, isPrepareAt]
    have hR : ∀ Y m, isEp m = false → isOKReplyAt q i cp.ballot Y m = false := fun Y m hm => by
      cases m <;> simp_all [isEp, isOKReplyAt]
    refine ⟨fun Y => Nat.le_trans (Nat.add_le_add (hcntle Y _ hP) (hcntle R _ (hR Y))) (k1 Y),
      fun ho => ?_⟩
    obtain ⟨k3, k4, k5⟩ := k2 ho
    exact ⟨k3, Nat.le_zero.1 (k4 ▸ hcntle _ _ hP), Nat.le_zero.1 (k5 ▸ hcntle R _ (hR _))⟩
  · rw [balOf_congr (fun a => hcp a q i)]; exact Evolve.refl (I.inst q i).ainv

/-! ### The Gryff handlers send no EPaxos message -/

theorem quietO_nil : QuietO [] := fun _ _ h => by cases h
theorem quietO_append {a b : List Out} (ha : QuietO a) (hb : QuietO b) : QuietO (a ++ b) :=
  fun d m h => (List.mem_append.1 h).elim (ha d m) (hb d m)
theorem quietO_ext {x : Ext} : QuietO [.ext x] := fun d m h => by simp at h

theorem sendTo_send {q : w32} {m : Msg} {x : Out} (h : sendTo q m = some x) :
    ∃ d, x = .send d m := by
  unfold sendTo at h
  obtain ⟨d, _, rfl⟩ := Option.map_eq_some_iff.1 h; exact ⟨d, rfl⟩

theorem sendPeer_send {s : RState} {q : w32} {m : Msg} {x : Out} (h : sendPeer s q m = some x) :
    ∃ d, x = .send d m := by
  unfold sendPeer at h; split at h
  · cases h
  · exact sendTo_send h

theorem quietO_single {x : Out} {m : Msg} (hx : ∃ d, x = .send d m) (hm : isEp m = false) :
    QuietO [x] := fun d m' h => by
  obtain ⟨d0, rfl⟩ := hx
  simp only [List.mem_singleton, Out.send.injEq] at h
  obtain ⟨-, rfl⟩ := h; exact hm

theorem mapM_mem {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {r : List β}, l.mapM f = some r → ∀ y ∈ r, ∃ a ∈ l, f a = some y
  | [], r, h => by simp at h; subst h; simp
  | a :: l, r, h => by
    simp only [List.mapM_cons, bind, Option.bind] at h
    cases hfa : f a with
    | none => simp [hfa] at h
    | some b =>
      simp only [hfa] at h
      cases hl : l.mapM f with
      | none => simp [hl] at h
      | some bs =>
        simp only [hl, pure, Option.some.injEq] at h
        subst h
        intro y hy
        rcases List.mem_cons.1 hy with rfl | hy
        · exact ⟨a, by simp, hfa⟩
        · obtain ⟨a', ha', h'⟩ := mapM_mem hl y hy
          exact ⟨a', by simp [ha'], h'⟩

theorem quietO_mapM_sendTo {l : List w32} {m : Msg} {r : List Out}
    (h : l.mapM (fun q => sendTo q m) = some r) (hm : isEp m = false) : QuietO r := by
  intro d m' hy
  obtain ⟨a, _, h'⟩ := mapM_mem h _ hy
  obtain ⟨d0, e⟩ := sendTo_send h'
  cases e; exact hm

theorem quietO_mapM_sendPeer {s : RState} {l : List w32} {m : Msg} {r : List Out}
    (h : l.mapM (fun q => sendPeer s q m) = some r) (hm : isEp m = false) : QuietO r := by
  intro d m' hy
  obtain ⟨a, _, h'⟩ := mapM_mem h _ hy
  obtain ⟨d0, e⟩ := sendPeer_send h'
  cases e; exact hm

theorem shortCircuit_quiet {s s' : RState} {n : w32} {v : ValTag} {f : Bool} {o : List Out}
    (h : shortCircuit s n v f = some (s', o)) : QuietO o := by
  rcases Perennial.gryff.model.shortCircuit_cases h with h | ⟨rfl, rfl⟩
  rotate_left
  · exact quietO_nil
  unfold Perennial.gryff.model.shortCircuitReads at h
  opeel h
  all_goals
    cases h
    refine forIn_opt_invA _ _ _ (fun p : RState × List Out => QuietO p.2) quietO_nil ?_ _ ‹_›
    intro a b st hb hf
    opeel hf
    all_goals (cases hf; first | exact hb | exact quietO_append hb quietO_ext)

theorem shortCircuit_ite_quiet {s s' : RState} {c : Prop} [Decidable c] {n : w32} {v : ValTag}
    {f : Bool} {o : List Out}
    (h : (if c then shortCircuit s n v f else some (s, [])) = some (s', o)) : QuietO o := by
  split at h
  · exact shortCircuit_quiet h
  · cases h; exact quietO_nil

macro "quiet_fin" : tactic => `(tactic| (
  first
  | exact quietO_nil
  | exact quietO_ext
  | exact quietO_single (sendPeer_send ‹sendPeer _ _ _ = some _›) rfl
  | exact quietO_single (sendTo_send ‹sendTo _ _ = some _›) rfl
  | exact quietO_mapM_sendTo ‹_› rfl
  | exact quietO_mapM_sendPeer ‹_› rfl
  | exact quietO_append (shortCircuit_quiet ‹_›) quietO_ext
  | exact quietO_append (shortCircuit_ite_quiet ‹_›) quietO_ext
  | exact quietO_append (quietO_mapM_sendTo ‹_› rfl) quietO_ext))

macro "quiet_close" h:ident : tactic => `(tactic| (
  peel $h:ident
  all_goals (cases $h:ident; quiet_fin)))

theorem stepRead1_quiet {s s' : RState} {m : Read1ProxiedM} {o : List Out}
    (h : stepRead1 s m = .ok (s', o)) : QuietO o := by unfold stepRead1 at h; quiet_close h
theorem stepRead2_quiet {s s' : RState} {m : Read2ProxiedM} {o : List Out}
    (h : stepRead2 s m = .ok (s', o)) : QuietO o := by unfold stepRead2 at h; quiet_close h
theorem stepWrite1_quiet {s s' : RState} {m : Write1ProxiedM} {o : List Out}
    (h : stepWrite1 s m = .ok (s', o)) : QuietO o := by unfold stepWrite1 at h; quiet_close h
theorem stepWrite2_quiet {s s' : RState} {m : Write2ProxiedM} {o : List Out}
    (h : stepWrite2 s m = .ok (s', o)) : QuietO o := by unfold stepWrite2 at h; quiet_close h
theorem stepRead1Reply_quiet {s s' : RState} {m : Read1ReplyM} {o : List Out}
    (h : stepRead1Reply s m = .ok (s', o)) : QuietO o := by unfold stepRead1Reply at h; quiet_close h
theorem stepRead2Reply_quiet {s s' : RState} {m : Read2ReplyM} {o : List Out}
    (h : stepRead2Reply s m = .ok (s', o)) : QuietO o := by unfold stepRead2Reply at h; quiet_close h
theorem stepWrite1Reply_quiet {s s' : RState} {m : Write1ReplyM} {o : List Out}
    (h : stepWrite1Reply s m = .ok (s', o)) : QuietO o := by unfold stepWrite1Reply at h; quiet_close h
theorem stepWrite2Reply_quiet {s s' : RState} {m : Write2ReplyM} {o : List Out}
    (h : stepWrite2Reply s m = .ok (s', o)) : QuietO o := by unfold stepWrite2Reply at h; quiet_close h
theorem stepClientWrite_quiet {s s' : RState} {rid cid : w32} {k v : w64} {d : Dep} {o : List Out}
    (h : stepClientWrite s rid cid k v d = .ok (s', o)) : QuietO o := by
  unfold stepClientWrite at h; quiet_close h
theorem stepClientRead_quiet {s s' : RState} {rid cid : w32} {k : w64} {d : Dep} {o : List Out}
    (h : stepClientRead s rid cid k d = .ok (s', o)) : QuietO o := by
  unfold stepClientRead at h; quiet_close h

/-! ## The conclusion of a step case

Each `inv_<event>`: the step from `c` by replica `a` (`Post`, the step `.ok`, its message in flight)
keeps `CInv` with an extended history (`StepInv`). -/

/-- The conclusion of a step case. -/
def StepInv (c c1 : Cfg gNet) (G : GG) : Prop :=
  ∃ G', CInv c1 G' ∧ ∀ q i, Evolve (rowOf q) (G q i) (balOf c q i) (G' q i) (balOf c1 q i)

theorem inv_quiet' {c c1 : Cfg gNet} {G : GG} {a : Fin 3} {e : Ev} {s' : RState} {o : List Out}
    (I : CInv c G) (hp : Post c a e s' o c1) (hf : Frame (c.st a) s') (ho : QuietO o) :
    StepInv c c1 G := ⟨G, inv_quiet I hp hf ho⟩

end Perennial.gryff.pureA
