/-
Pure facts of the executor's command step (`Sys.execCmd`) the Iris step `ep_execCmd` uses: what
the step changes, and its outcome for the abstract state and the fired outputs (`execOutcome`:
either nothing is fired and every reply carries an already fired output, or exactly the slot's
op fires, from the abstract state, with the reply's output).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.GhostDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.Basic

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs model

variable [GooseExts]

/-- Every op's input meets the run's premise, with its command (what `epInv` knows of the ops,
through their connections). -/
def opsPre [GoGlobalContext] (S : Sys) : Prop :=
  ∀ o ∈ S.ops, ∃ inp : KvI, inPre inp ∧ o.2.cmd = cmdOf inp

/-- The outcome of a command step for the abstract state and the fired outputs. -/
def execOutcome [GoGlobalContext] (S S' : Sys) (outs : List Out) : Prop :=
  (S'.kv = S.kv ∧ S'.fired = S.fired ∧
    ∀ p v, Out.reply p v ∈ outs → ∃ o, S.fired p.cid = some o ∧ replyValOk o v) ∨
  (∃ (r : Nat) (p : Proposal) (o : KvO), (r, p) ∈ S.ops ∧ S.fired p.cid = none ∧
    S'.fired = upd S.fired p.cid (some o) ∧
    (∀ inp, p.cmd = cmdOf inp → inPre inp → (kvScan w8).step S.kv inp S'.kv o) ∧
    ∀ p' v, Out.reply p' v ∈ outs → p' = p ∧ replyValOk o v)

/-- The executor's outputs are client replies. -/
theorem execCmdAt_outs (σ : RState) (w : InstRec) (idx : Nat) :
    ∀ o ∈ (execCmdAt σ w idx).2, ∃ p v, o = Out.reply p v := by
  intro o ho
  simp only [execCmdAt] at ho
  split at ho
  · simp at ho
  · split at ho
    · simp at ho; exact ⟨_, _, ho⟩
    · split at ho <;> simp at ho

/-! ## `fire` -/

theorem fire_old (S : Sys) (e : Slot × WCmd) (h : e ∈ S.gexec e.2.key) : S.fire e = S := by
  unfold Sys.fire; rw [if_pos h]

theorem fire_gexec_new (S : Sys) (e : Slot × WCmd) (h : e ∉ S.gexec e.2.key) :
    (S.fire e).gexec = fun k => if Sys.touches e.2 k then S.gexec k ++ [e] else S.gexec k := by
  unfold Sys.fire; rw [if_neg h]; dsimp only; split <;> rfl

theorem fire_fired_new (S : Sys) (e : Slot × WCmd) (h : e ∉ S.gexec e.2.key) (p : Proposal)
    (hp : S.slotOp e.1 = some p) :
    (S.fire e).fired = upd S.fired p.cid (some (Sys.outOf S.gexec e.2)) := by
  unfold Sys.fire; rw [if_neg h]; dsimp only; rw [hp]

/-- What firing leaves. -/
theorem fire_same (S : Sys) (e : Slot × WCmd) :
    (S.fire e).rep = S.rep ∧ (S.fire e).outbox = S.outbox ∧
    (S.fire e).pending = S.pending ∧ (S.fire e).execCur = S.execCur ∧
    (S.fire e).execIdx = S.execIdx ∧ (S.fire e).proposeChan = S.proposeChan ∧
    (S.fire e).sent = S.sent ∧ (S.fire e).delivered = S.delivered ∧
    (S.fire e).ops = S.ops ∧ (S.fire e).owner = S.owner := by
  unfold Sys.fire
  split
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · dsimp only
    split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The global sequences only grow by firing. -/
theorem fire_gexec_mono (S : Sys) (e : Slot × WCmd) (k : w64) (e' : Slot × WCmd)
    (h : e' ∈ S.gexec k) : e' ∈ (S.fire e).gexec k := by
  by_cases hn : e ∈ S.gexec e.2.key
  · rw [fire_old S e hn]; exact h
  · rw [fire_gexec_new S e hn]; dsimp only; split <;> simp [h]

theorem fire_kv_congr (S T : Sys) (e : Slot × WCmd) (h : T.gexec = S.gexec) :
    (T.fire e).kv = (S.fire e).kv := by
  by_cases hn : e ∈ S.gexec e.2.key
  · rw [fire_old S e hn, fire_old T e (h ▸ hn)]; unfold Sys.kv; rw [h]
  · unfold Sys.kv; rw [fire_gexec_new S e hn, fire_gexec_new T e (h ▸ hn), h]

theorem pendFold_replies (os : List Out) (h : ∀ o ∈ os, ∃ p v, o = Out.reply p v)
    (p : Option Bcast) : pendFold os p = p := by
  unfold pendFold
  induction os generalizing p with
  | nil => rfl
  | cons o os ih =>
    obtain ⟨q, v, rfl⟩ := h o (by simp)
    simp only [List.foldl_cons]
    exact ih (fun o ho => h o (List.mem_cons_of_mem _ ho)) p

/-- The step's effect on the tracked fields. -/
theorem execCmd_fields (S : Sys) (i : Nat) (x : InstId) (w : InstRec) :
    let S' := S.execCmd i x w
    S'.rep = upd S.rep i (execCmdAt (S.rep i) w (S.execIdx i)).1 ∧ S'.outbox = S.outbox ∧
    S'.pending = S.pending ∧ S'.execCur = S.execCur ∧
    S'.execIdx = upd S.execIdx i (S.execIdx i + 1) ∧ S'.proposeChan = S.proposeChan ∧
    S'.sent = S.sent ∧ S'.delivered = S.delivered ∧ S'.ops = S.ops := by
  intro S'
  have hout := execCmdAt_outs (S.rep i) w (S.execIdx i)
  generalize hr : execCmdAt (S.rep i) w (S.execIdx i) = r at hout
  obtain ⟨σ', os⟩ := r
  have h1 : os.filterMap Out.reprop = [] := by
    rw [List.filterMap_eq_nil_iff]; intro o ho
    obtain ⟨p, v, rfl⟩ := hout o ho; rfl
  have h2 : ∀ to, os.filterMap (Out.sendTo to) = [] := by
    intro to; rw [List.filterMap_eq_nil_iff]; intro o ho
    obtain ⟨p, v, rfl⟩ := hout o ho; rfl
  have h3 : ∀ p, pendFold os p = p := fun p => pendFold_replies os (fun o ho => hout o ho) p
  -- the step before the firing
  let S2 : Sys := { S.applyStep i (σ', os) with
    execIdx := upd (S.applyStep i (σ', os)).execIdx i (S.execIdx i + 1) }
  have hS2 : S2.rep = upd S.rep i σ' ∧ S2.outbox = S.outbox ∧ S2.pending = S.pending ∧
      S2.execCur = S.execCur ∧ S2.execIdx = upd S.execIdx i (S.execIdx i + 1) ∧
      S2.proposeChan = S.proposeChan ∧ S2.sent = S.sent ∧ S2.delivered = S.delivered ∧
      S2.ops = S.ops := by
    refine ⟨by simp [S2], ?_, ?_, by simp [S2], by simp [S2], ?_, by simp [S2], by simp [S2],
      by simp [S2]⟩
    · funext fr to; simp [S2, h2]
    · funext fr; simp only [S2, Sys.applyStep_pending, h3]; split <;> simp_all
    · funext fr; simp [S2, h1]
  have e : S' = if ((w.cmds.getD []).getD (S.execIdx i) default).op = opNONE then S2
      else S2.fire ((x, S.execIdx i), (w.cmds.getD []).getD (S.execIdx i) default) := by
    show S.execCmd i x w = _
    unfold Sys.execCmd; simp only []; rw [hr]
  rw [e]
  split
  · exact hS2
  · obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, -⟩ :=
      fire_same S2 ((x, S.execIdx i), (w.cmds.getD []).getD (S.execIdx i) default)
    obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := hS2
    exact ⟨a1.trans b1, a2.trans b2, a3.trans b3, a4.trans b4, a5.trans b5, a6.trans b6,
      a7.trans b7, a8.trans b8, a9.trans b9⟩

/-! ## `lastPut` -/

theorem lastPut_foldl (s : List (Slot × WCmd)) (v0 : Option (List w8)) :
    s.foldl (fun v e => if e.2.op = opPUT then some e.2.val else v) v0 =
      (Sys.writes s).foldl (fun v e => if e.2.op = opPUT then some e.2.val else v) v0 := by
  induction s generalizing v0 with
  | nil => rfl
  | cons e s ih =>
    simp only [List.foldl_cons, Sys.writes, List.filter_cons]
    by_cases h : e.2.op = opPUT
    · simp only [h, decide_true, ite_true, List.foldl_cons]; exact ih _
    · simp only [h, decide_false, ite_false, Bool.false_eq_true]; exact ih _

theorem lastPut_writes (s : List (Slot × WCmd)) : Sys.lastPut s = Sys.lastPut (Sys.writes s) := by
  unfold Sys.lastPut
  rw [lastPut_foldl, lastPut_foldl (Sys.writes s)]

theorem lastPut_eq_of_writes {s t : List (Slot × WCmd)} (h : Sys.writes s = Sys.writes t) :
    Sys.lastPut s = Sys.lastPut t := by
  rw [lastPut_writes s, lastPut_writes t, h]

theorem lastPut_mem_foldl (s : List (Slot × WCmd)) (v0 : Option (List w8)) (val : List w8)
    (h : s.foldl (fun v e => if e.2.op = opPUT then some e.2.val else v) v0 = some val) :
    v0 = some val ∨ ∃ e ∈ s, e.2.op = opPUT ∧ e.2.val = val := by
  induction s generalizing v0 with
  | nil => exact Or.inl h
  | cons e s ih =>
    simp only [List.foldl_cons] at h
    rcases ih _ h with h' | ⟨e', he', h1, h2⟩
    · by_cases hp : e.2.op = opPUT
      · simp only [hp, ite_true] at h'
        exact Or.inr ⟨e, by simp, hp, Option.some.inj h'⟩
      · simp only [hp, ite_false] at h'; exact Or.inl h'
    · exact Or.inr ⟨e', List.mem_cons_of_mem _ he', h1, h2⟩

theorem lastPut_mem {s : List (Slot × WCmd)} {val : List w8} (h : Sys.lastPut s = some val) :
    ∃ e ∈ s, e.2.op = opPUT ∧ e.2.val = val := by
  rcases lastPut_mem_foldl s none val h with h | h
  · cases h
  · exact h

theorem inv_execPrefix {S : Sys} (h : Inv S) : Inv.execPrefix S :=
  h.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem inv_slots {S : Sys} (h : Inv S) : Inv.slots S :=
  h.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem inv_clientOps {S : Sys} (h : Inv S) : Inv.clientOps S :=
  h.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- A slot's op is one of the ops. -/
theorem slotOp_ops {S : Sys} (hS : Inv S) {s : Slot} {p : Proposal} (h : S.slotOp s = some p) :
    (s.1.q, p) ∈ S.ops := by
  unfold Sys.slotOp at h
  cases ho : S.owner s.1 with
  | none => rw [ho] at h; cases h
  | some ps =>
    rw [ho] at h
    exact (inv_slots hS).2 s.1 ps ho p (List.mem_of_getElem? h)

/-- The values the global sequences put are non-empty (the ops' premise). -/
theorem gexec_put_ne [GoGlobalContext] {S : Sys} (hS : Inv S) (hops : opsPre S) {k : w64}
    {e : Slot × WCmd} (he : e ∈ S.gexec k) (hp : e.2.op = opPUT) : e.2.val ≠ [] := by
  obtain ⟨-, -, -, ⟨q, hq, hcmd⟩, -⟩ := (inv_clientOps hS).2.2.2.1 k e he
  obtain ⟨inp, hpre, hinp⟩ := hops _ (slotOp_ops hS hq)
  rw [← hcmd, hinp] at hp ⊢
  cases inp with
  | get k' => simp [cmdOf, opGET, opPUT] at hp
  | put k' v => simp only [cmdOf]; exact hpre.2.1
  | scan k' n => simp [cmdOf, opSCAN, opPUT] at hp

theorem replyOk_get [GoGlobalContext] {S : Sys} (hS : Inv S) (hops : opsPre S) {k : w64}
    {pre : List (Slot × WCmd)} (hpre : ∀ e ∈ pre, e ∈ S.gexec k) :
    replyValOk (.got (Sys.lastPut pre)) ((Sys.lastPut pre).getD []) := by
  cases h : Sys.lastPut pre with
  | none => rfl
  | some val =>
    obtain ⟨e, he, hp, hv⟩ := lastPut_mem h
    exact ⟨rfl, hv ▸ gexec_put_ne hS hops (hpre e he) hp⟩

theorem filterMap_congr' {α β : Type} {l : List α} {f g : α → Option β}
    (h : ∀ a ∈ l, f a = g a) : l.filterMap f = l.filterMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.filterMap_cons, h a (by simp), ih (fun b hb => h b (by simp [hb]))]

/-- The reply value the executor computes is the output against sequences `G` with the replica's
writes on every key the command touches (stage 2: per touched key, a SCAN's range included). -/
theorem reply_ok [GoGlobalContext] {S : Sys} (hS : Inv S) (hops : opsPre S) {i : Nat} (hi : i < nR)
    (c : WCmd) (G : w64 → List (Slot × WCmd))
    (hG : ∀ k, Sys.touches c k → ∀ e ∈ G k, e ∈ S.gexec k)
    (hwr : ∀ k, Sys.touches c k → Sys.writes (G k) = Sys.writes (S.lexec i k)) :
    replyValOk (Sys.outOf G c) (execCmd (S.rep i).store c).2 := by
  have hst : ∀ k, Sys.touches c k → (S.rep i).store k = Sys.lastPut (G k) := fun k hk => by
    rw [(inv_execPrefix hS).2.1 i hi k]; exact lastPut_eq_of_writes (hwr k hk).symm
  unfold Sys.outOf
  by_cases hg : c.op = opGET
  · have hnp : c.op ≠ opPUT := by rw [hg]; decide
    simp only [hg, ite_true, execCmd, hnp, ite_false]
    rw [hst c.key (Or.inl rfl)]
    exact replyOk_get hS hops (hG c.key (Or.inl rfl))
  · by_cases hs : c.op = opSCAN
    · have hnp : c.op ≠ opPUT := by rw [hs]; decide
      rw [if_neg hg, if_pos hs]
      unfold execCmd
      rw [if_neg hnp, if_neg hg, if_pos hs]
      show _ = _
      dsimp only
      rw [filterMap_congr' (fun k hk => hst k (rangeKeys_touches c k hs hk))]
    · simp only [hg, hs, ite_false]; trivial

/-- The run's premise keeps a SCAN's range from wrapping (S4). -/
theorem kitpre_range [GoGlobalContext] (inp : KvI) (h : inPre inp) : inpRangeOk inp := by
  cases inp with
  | get k' => trivial
  | put k' v => trivial
  | scan k' n =>
    have h1 : k'.toNat < 2 := h.1
    have h2 : n.toNat < 2 := h.2
    show k'.toNat + n.toNat < 2 ^ 63
    omega

/-- A client command's input meets the premise: the command is `OpCmdOk`. -/
theorem opCmdOk_of_pre [GoGlobalContext] (inp : KvI) (h : inPre inp) : OpCmdOk (cmdOf inp) := by
  cases inp with
  | get k' => exact ⟨h, Or.inl ⟨rfl, rfl⟩⟩
  | put k' v => exact ⟨h.1, Or.inr (Or.inl ⟨rfl, h.2.1, h.2.2⟩)⟩
  | scan k' n => exact ⟨h.1, Or.inr (Or.inr ⟨rfl, n, h.2, rfl⟩)⟩

theorem applyStep_gexec' (S : Sys) (i : Nat) (r : RState × List Out) :
    (S.applyStep i r).gexec = S.gexec ∧ (S.applyStep i r).fired = S.fired ∧
    (S.applyStep i r).owner = S.owner := by
  unfold Sys.applyStep
  exact ⟨Sys.foldl_emit_gexec _ _ _, Sys.foldl_emit_fired _ _ _, Sys.foldl_emit_owner _ _ _⟩

/-- The outcome of the command step (from the invariant before and after it, and the model's
execution laws `inv_exec_first`, `inv_exec_again`, `fire_kv_step`). -/
theorem exec_outcome [GoGlobalContext] (S : Sys) (i : Nat) (x : InstId) (rest : List InstId)
    (w : InstRec) (hS : Inv S) (hS' : Inv (S.execCmd i x w)) (hi : i < nR)
    (hcur : S.execCur i = x :: rest)
    (hw : (S.rep i).inst x = some w) (hidx : S.execIdx i < (w.cmds.getD []).length)
    (hops : opsPre S) :
    execOutcome S (S.execCmd i x w) (execCmdAt (S.rep i) w (S.execIdx i)).2 := by
  have hco := inv_clientOps hS
  have hco' := inv_clientOps hS'
  generalize hidxd : S.execIdx i = idx at hidx ⊢
  generalize hcd : (w.cmds.getD []).getD idx default = c
  have hcc : curCmd S i w = c := by rw [← hcd, ← hidxd]; rfl
  -- the replies
  have houts : ∀ p v, Out.reply p v ∈ (execCmdAt (S.rep i) w idx).2 → c.op ≠ opNONE ∧
      ∃ lb ps, w.lb = some lb ∧ lb.clientProposals = some ps ∧ p = ps.getD idx default ∧
        v = (execCmd (S.rep i).store c).2 := by
    intro p v h
    simp only [execCmdAt, hcd] at h
    split at h
    · simp at h
    · rename_i hcn
      split at h
      · rename_i ps hlb
        simp at h
        obtain ⟨lb, hlb1, hlb2⟩ := Option.bind_eq_some_iff.mp hlb
        exact ⟨hcn, lb, ps, hlb1, hlb2, h.1, h.2⟩
      · split at h <;> simp at h
  let S2 : Sys := { S.applyStep i (execCmdAt (S.rep i) w idx) with
    execIdx := upd (S.applyStep i (execCmdAt (S.rep i) w idx)).execIdx i (idx + 1) }
  have e : S.execCmd i x w = if c.op = opNONE then S2 else S2.fire ((x, idx), c) := by
    unfold Sys.execCmd; simp only []; rw [hidxd, hcd]
  obtain ⟨g2, f2, o2⟩ := applyStep_gexec' S i (execCmdAt (S.rep i) w idx)
  have hg2 : S2.gexec = S.gexec := g2
  have hf2 : S2.fired = S.fired := f2
  have ho2 : S2.owner = S.owner := o2
  have hkv2 : S2.kv = S.kv := by unfold Sys.kv; rw [hg2]
  have hsl2 : S2.slotOp = S.slotOp := by funext sl; unfold Sys.slotOp; rw [ho2]
  have hown : ∀ lb ps, w.lb = some lb → lb.clientProposals = some ps → S.owner x = some ps :=
    fun lb ps h1 h2 => (hS.1.1.2.1 i hi x w hw).2.2.2.2.2.2 lb ps h1 h2
  rw [e] at hS' ⊢
  rw [e] at hco'
  by_cases hcn : c.op = opNONE
  · left
    rw [if_pos hcn]
    exact ⟨hkv2, hf2, fun p v h => absurd hcn (houts p v h).1⟩
  rw [if_neg hcn] at hS' hco' ⊢
  have hcn' : (curCmd S i w).op ≠ opNONE := by rw [hcc]; exact hcn
  by_cases hnew : ((x, idx), c) ∈ S.gexec c.key
  · -- executed before: nothing fires
    left
    rw [fire_old S2 _ (by rw [hg2]; exact hnew)]
    refine ⟨hkv2, hf2, ?_⟩
    intro p v h
    obtain ⟨-, lb, ps, hlb, hps, rfl, rfl⟩ := houts p v h
    have hnew' := hnew
    rw [← hcc, ← hidxd] at hnew'
    obtain ⟨hall, hf⟩ := inv_exec_again S i x rest w hS hi hcur hw
      (by rw [hidxd]; exact hidx) hcn' hnew'
    simp only [hcc, hidxd] at hall hf
    obtain ⟨-, -, -, ⟨q, hq, -⟩, -⟩ := hco.2.2.2.1 _ _ hnew
    have hpq : ps[idx]? = some q := by
      unfold Sys.slotOp at hq; rw [hown lb ps hlb hps] at hq; exact hq
    have hget : ps.getD idx default = q := by simp [List.getD_eq_getElem?_getD, hpq]
    rw [hget]
    refine ⟨_, hf q hq, reply_ok hS hops hi c _ ?_ ?_⟩
    · intro k _ e' he'
      exact (List.takeWhile_sublist _).subset he'
    · intro k hk
      obtain ⟨pre, post, hgk, hwr⟩ := hall k hk
      rw [before_eq S hS k pre post _ hgk]; exact hwr
  · -- the first execution: the slot's op fires
    right
    have hnew2 : ((x, idx), c) ∉ S2.gexec ((x, idx), c).2.key := by rw [hg2]; exact hnew
    have hin' : ((x, idx), c) ∈ (S2.fire ((x, idx), c)).gexec c.key := by
      rw [fire_gexec_new S2 _ hnew2]; simp [Sys.touches]
    have hslot' : (S2.fire ((x, idx), c)).slotOp = S.slotOp := by
      funext sl; unfold Sys.slotOp; rw [(fire_same S2 _).2.2.2.2.2.2.2.2.2, ho2]
    obtain ⟨-, -, -, ⟨p, hp, hpc⟩, -⟩ := hco'.2.2.2.1 _ _ hin'
    rw [hslot'] at hp
    have hpc' : p.cmd = c := hpc
    refine ⟨x.q, p, Sys.outOf S.gexec c, slotOp_ops hS hp, ?_, ?_, ?_, ?_⟩
    · cases hfd : S.fired p.cid with
      | none => rfl
      | some o0 =>
        exfalso
        obtain ⟨e', p', he', hsl, hcid, -⟩ := (hco.2.2.2.2 p.cid o0).1 hfd
        have he'' : e' ∈ (S2.fire ((x, idx), c)).gexec e'.2.key :=
          fire_gexec_mono S2 _ _ _ (by rw [hg2]; exact he')
        have h1 := hco'.2.1 c.key e'.2.key _ e' p p' hin' he''
          (by rw [hslot']; exact hp) (by rw [hslot']; exact hsl) hcid.symm
        obtain ⟨-, -, -, ⟨p'', hp'', hp''c⟩, -⟩ := hco.2.2.2.1 _ _ he'
        rw [← h1] at hp''
        have : p'' = p := Option.some.inj (hp''.symm.trans hp)
        subst this
        have he : e' = ((x, idx), c) := Prod.ext h1.symm (by rw [← hp''c, hpc'])
        subst he
        exact hnew he'
    · rw [fire_fired_new S2 _ hnew2 p (by rw [hsl2]; exact hp), hf2, hg2]
    · intro inp hcmd hpre
      have hce : ((x, idx), c).2 = cmdOf inp := by rw [← hpc', hcmd]
      rw [fire_kv_congr S S2 _ hg2]
      exact fire_kv_step S ((x, idx), c) inp hce (kitpre_range inp hpre) hnew
    · intro p' v h
      obtain ⟨-, lb, ps, hlb, hps, rfl, rfl⟩ := houts p' v h
      have hpq : ps[idx]? = some p := by
        unfold Sys.slotOp at hp; rw [hown lb ps hlb hps] at hp; exact hp
      refine ⟨by simp [List.getD_eq_getElem?_getD, hpq], ?_⟩
      have hnew' : ((x, S.execIdx i), curCmd S i w) ∉ S.gexec (curCmd S i w).key := by
        rw [hcc, hidxd]; exact hnew
      have hwr := inv_exec_first S i x rest w hS hi hcur hw (by rw [hidxd]; exact hidx) hcn' hnew'
      rw [hcc] at hwr
      exact reply_ok hS hops hi c _ (fun _ _ e he => he) hwr

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
