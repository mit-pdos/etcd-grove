/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Pure/Agree.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Agreement (stage 2, unit A; `notes/stage2-proof.md` §A, §A'): one committed value per EPaxos
instance, the interference of committed instances with commands (D1), and the executed sequences'
agreement (D2).

An instance is `(q, i)` (row `q` = its leader's id, slot `i`, as the model's words). Its *value* is
`(cmds, seq, deps, base)` (`IVal`). A value is *committed* in a configuration (`CommittedIn`) when a
replica holds a COMMITTED or EXECUTED copy with it, a `Commit` for the instance carrying it is in
flight, or a `PrepareReply` reporting a COMMITTED or EXECUTED copy with it is in flight (G22 commits
such a reply's value).
-/
module

public import Dsverify.Proof.gryff.Pure.Run
public import Dsverify.Proof.gryff.PureA.Inv
public import Dsverify.Proof.gryff.PureA.IntfRun
public import Dsverify.Proof.gryff.PureA.AEChain

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure

open model kahn

/-- An instance's value. -/
structure IVal where
  cmds : List Cmd
  seq : w32
  deps : Deps
  base : ValTag
deriving DecidableEq, Repr

def _root_.Perennial.gryff.model.Copy.ival (c : Copy) : IVal := ⟨c.cmds, c.seq, c.deps, c.base⟩
def _root_.Perennial.gryff.model.ECommitM.ival (m : ECommitM) : IVal := ⟨m.cmds, m.seq, m.deps, m.base⟩
def _root_.Perennial.gryff.model.PrepareReplyM.ival (m : PrepareReplyM) : IVal :=
  ⟨m.cmds, m.seq, m.deps, m.base⟩

/-- A status of a committed copy (COMMITTED or EXECUTED). -/
def committedSt (st : w8) : Prop := st = St.COMMITTED ∨ st = St.EXECUTED

/-- `v` is a committed value of instance `(q, i)` in configuration `c`. -/
def CommittedIn (c : Cfg gNet) (q i : w32) (v : IVal) : Prop :=
  (∃ (r : Fin 3) (cp : Copy), (c.st r).inst q i = some cp ∧ committedSt cp.status ∧ cp.ival = v) ∨
  (∃ (r : Fin 3) (m : ECommitM), Msg.commit m ∈ c.inflight r ∧ m.replica = q ∧ m.inst = i ∧
    m.ival = v) ∨
  (∃ (r : Fin 3) (m : PrepareReplyM), Msg.prepareReply m ∈ c.inflight r ∧ m.replica = q ∧
    m.inst = i ∧ committedSt m.status ∧ m.ival = v)

/-- **Agreement over a run** (A1-A5): every two values committed for an instance, at any two points
of a run, are equal. -/
theorem agree_run {l l' : List Label} {c c' : Cfg gNet} (h : GRun (Cfg.init gNet) l c)
    (h' : GRun c l' c') {q i : w32} {v v' : IVal} (hv : CommittedIn c q i v)
    (hv' : CommittedIn c' q i v') : v = v' := by
  -- unit A1: the invariant `pureA.CInv` with its history (`GryffProof/PureA/Concrete.lean`)
  have chosen : ∀ {c : Cfg gNet} {G : pureA.GG}, pureA.CInv c G → ∀ {v : IVal}, CommittedIn c q i v →
      pureA.Chosen (G q i) (v.cmds, v.seq, v.deps, v.base) := by
    intro c G I v hv
    rcases hv with ⟨r, cp, h1, h2, rfl⟩ | ⟨r, m, h1, rfl, rfl, rfl⟩ | ⟨r, m, h1, rfl, rfl, h2, rfl⟩
    · exact pureA.committed_copy_chosen I h1 h2
    · exact pureA.committed_commit_chosen I h1
    · exact pureA.committed_reply_chosen I h1 h2
  obtain ⟨G, I⟩ := pureA.inv_reach h
  obtain ⟨G', I', E⟩ := pureA.inv_run I h'
  have e := pureA.chosen_unique (I'.inst q i).ainv
    (pureA.chosen_mono (E q i).le (chosen I hv)) (chosen I' hv')
  cases v; cases v'
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl, rfl, rfl⟩ := e
  rfl

/-- **Agreement in a reachable configuration**: committed copies and in-flight `Commit`s (and
committed `PrepareReply`s) of an instance carry one value. -/
theorem agree {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) {q i : w32}
    {v v' : IVal} (hv : CommittedIn c q i v) (hv' : CommittedIn c q i v') : v = v' :=
  agree_run h (GRun.nil c) hv hv'

/-- Value `v` (of some instance) depends on instance `(q', i')`: `i' ≤ deps[q']` (signed; the
executor's `depR`). -/
def IVal.dependsOn (v : IVal) (q' i' : w32) : Prop := sint.Z i' ≤ sint.Z (v.deps.at q'.toNat)

/-- **Interference (D1)**: of two distinct instances committed with commands, one depends on the
other. (No-ops are excluded: a no-op's deps are 0 on the other rows.) -/
theorem interf {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) {q i q' i' : w32}
    {v v' : IVal} (hv : CommittedIn c q i v) (hv' : CommittedIn c q' i' v') (hne : (q, i) ≠ (q', i'))
    (hc : v.cmds ≠ []) (hc' : v'.cmds ≠ []) :
    v.dependsOn q' i' ∨ v'.dependsOn q i := by
  -- unit AI: the interference invariant `pureA.AI.IInv` (`GryffProof/PureA/Intf*.lean`)
  obtain ⟨κ, rc, dg, I⟩ := pureA.AI.intf_reach h
  have val : ∀ {q i : w32} {v : IVal}, CommittedIn c q i v → v.cmds ≠ [] →
      pureA.AI.SameRow q i v.deps ∧ pureA.AI.Wp2 rc κ q i v.deps := by
    intro q i v hv hc
    rcases hv with ⟨r, cp, h1, h2, rfl⟩ | ⟨r, m, h1, rfl, rfl, rfl⟩ | ⟨r, m, h1, rfl, rfl, h2, rfl⟩
    · exact pureA.AI.copy_committed I h1 h2 hc
    · exact pureA.AI.commit_committed I h1 hc
    · exact pureA.AI.reply_committed I h1 h2 hc
  exact pureA.AI.interf_vals I (val hv hc) (val hv' hc') hne

/-- Replica `r`'s executed sequence in its events `es`: its executions with a command (`exec`
events whose step outputs an `ExecuteOverwrite`), in order, each with its instance and its result
`(v, t)`. Executions of no-ops (no result) are not in it. -/
noncomputable def execSeq (r : Fin 3) (es : List Ev) : List ((w32 × w32) × ValTag) :=
  (List.range es.length).filterMap fun j =>
    match es[j]? with
    | some (Ev.exec q i) => (execRes (outsOf r es j)).map fun vt => ((q, i), vt)
    | _ => none

/-- A committed copy at a replica's state at a cut is committed in the cut's configuration. -/
theorem exec_cutCom {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) {k : Nat}
    {a : Fin 3} {x : replica.Node} {cp : Copy} (hc : committedCopy (cutSt l k a) x = some cp) :
    ∃ cn, GRun (Cfg.init gNet) (l.take k) cn ∧
      CommittedIn cn (BitVec.ofInt 32 x.1) (BitVec.ofInt 32 x.2) cp.ival := by
  obtain ⟨cn, h1, -, h3⟩ := grun_cut h k
  obtain ⟨o, ho⟩ := h3 a
  have e : cutSt l k a = cn.st a := stOf_of_runP ho
  rw [e] at hc
  obtain ⟨-, -, -, hi, hs⟩ := pureA.AE.inst_of_cc hc
  exact ⟨cn, h1, Or.inl ⟨a, cp, hi, hs, rfl⟩⟩

theorem exec_agreeH {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) :
    pureA.AE.AgreeH l := by
  -- a later cut's configuration is reached from an earlier one's
  have later : ∀ {k k' : Nat} {cn cn' : Cfg gNet}, k ≤ k' → GRun (Cfg.init gNet) (l.take k) cn →
      GRun (Cfg.init gNet) (l.take k') cn' → ∃ l', GRun cn l' cn' := by
    intro k k' cn cn' hkk h1 h2
    have h2' : GRun (Cfg.init gNet) ((l.take k').take k ++ (l.take k').drop k) cn' := by
      rw [List.take_append_drop]; exact h2
    obtain ⟨c1, h3, h4⟩ := Perennial.gryff.pure.grun_append h2'
    rw [List.take_take, Nat.min_eq_left hkk] at h3
    have := pureA.AE.grun_det h1 h3; subst this
    exact ⟨_, h4⟩
  have key : ∀ {x cp cp'}, pureA.AE.CutCom l x cp → pureA.AE.CutCom l x cp' → cp.ival = cp'.ival := by
    intro x cp cp' ⟨k, a, hk⟩ ⟨k', a', hk'⟩
    obtain ⟨cn, h1, hv⟩ := exec_cutCom h hk
    obtain ⟨cn', h1', hv'⟩ := exec_cutCom h hk'
    rcases Nat.le_total k k' with hkk | hkk
    · obtain ⟨l', hr⟩ := later hkk h1 h1'
      exact agree_run h1 hr hv hv'
    · obtain ⟨l', hr⟩ := later hkk h1' h1
      exact (agree_run h1' hr hv' hv).symm
  intro x cp cp' h1 h2
  have e := key h1 h2
  simp only [Copy.ival, IVal.mk.injEq] at e
  exact e

theorem exec_interfH {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) :
    pureA.AE.InterfH l := by
  have fin : ∀ a : Fin 3, cutSt l l.length a = c.st a := by
    intro a
    obtain ⟨o, ho⟩ := kahn.grun_state h a
    unfold cutSt; rw [List.take_length]; exact stOf_of_runP ho
  intro a a' x y cp cp' hx hy hcx hcy hne
  have hx0 := hx; have hy0 := hy
  rw [fin] at hx hy
  obtain ⟨-, -, ex, hix, hsx⟩ := pureA.AE.inst_of_cc hx
  obtain ⟨-, -, ey, hiy, hsy⟩ := pureA.AE.inst_of_cc hy
  have hne' : (BitVec.ofInt 32 x.1, BitVec.ofInt 32 x.2) ≠ (BitVec.ofInt 32 y.1, BitVec.ofInt 32 y.2) := by
    intro e; apply hne; rw [← ex, ← ey, e]
  rcases interf h (Or.inl ⟨a, cp, hix, hsx, rfl⟩) (Or.inl ⟨a', cp', hiy, hsy, rfl⟩) hne' hcx hcy
    with d | d
  · exact Or.inl (pureA.AE.depR_of_le hx0 hy0 d)
  · exact Or.inr (pureA.AE.depR_of_le hy0 hx0 d)

/-- **The chain (D2)**: in a run, any two replicas' executed sequences (instances and results) are
prefix-comparable: all are prefixes of one chain. -/
theorem exec_agree {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) (r r' : Fin 3) :
    execSeq r (projR l r) <+: execSeq r' (projR l r') ∨
      execSeq r' (projR l r') <+: execSeq r (projR l r) :=
  -- unit AE: `pureA.AE.chain_agree` (`GryffProof/PureA/AEChain.lean`)
  pureA.AE.chain_agree h (exec_agreeH h) (exec_interfH h) r r'

/-- An instance's execution result is the same at every replica that executed it (with a
command). -/
theorem exec_same {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) (r r' : Fin 3)
    {x : w32 × w32} {vt vt' : ValTag} (hx : (x, vt) ∈ execSeq r (projR l r))
    (hx' : (x, vt') ∈ execSeq r' (projR l r')) : vt = vt' :=
  -- unit AE: `pureA.AE.chain_same` (`GryffProof/PureA/AEChain.lean`)
  pureA.AE.chain_same h (exec_agreeH h) (exec_interfH h) r r' hx hx'

/-- A replica executes an instance at most once. -/
theorem exec_nodup {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) (r : Fin 3) :
    ((execSeq r (projR l r)).map Prod.fst).Nodup := by
  -- unit A1: `pureA.exec_twice` (`GryffProof/PureA/Exec.lean`)
  obtain ⟨o, hrun⟩ := kahn.grun_state h r
  refine List.Pairwise.map _ (fun _ _ h => h) (List.Pairwise.filterMap _ ?_ List.pairwise_lt_range)
  intro j1 j2 hlt b1 hb1 b2 hb2 heq
  change runP gNet r (projR l r) = _ at hrun
  generalize hes : projR l r = es at hb1 hb2 hrun
  cases e1 : es[j1]? with
  | none => simp [e1] at hb1
  | some ev1 =>
    cases e2 : es[j2]? with
    | none => simp [e2] at hb2
    | some ev2 =>
      cases ev1 <;> simp only [e1] at hb1 <;> try cases hb1
      cases ev2 <;> simp only [e2] at hb2 <;> try cases hb2
      rename_i q1 i1 q2 i2
      obtain ⟨vt1, -, rfl⟩ := Option.map_eq_some_iff.1 hb1
      obtain ⟨vt2, hv2, rfl⟩ := Option.map_eq_some_iff.1 hb2
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      have hres : ∃ x, stepR r (stOf r (es.take j2)) (.exec q1 i1) = .ok x := by
        unfold outsOf at hv2
        split at hv2
        · rename_i hr; unfold resOf at hr; rw [e2] at hr; exact ⟨_, hr⟩
        · simp [execRes] at hv2
      obtain ⟨x, hx⟩ := hres
      exact pureA.exec_twice hrun hlt e1 e2 x hx

end Perennial.gryff.pure
