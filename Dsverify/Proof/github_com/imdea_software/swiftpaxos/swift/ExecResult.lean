/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/ExecResult.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
**`exec_result`** (request SWC-2; notes/prove-swift.md §1.3 and "SWC-2 (round S1)"): executing
commands in an order that puts each after its dependencies, where each command's dependencies
include its `depsIn` in one sequence `s` of the leader, gives each command its `resultIn s`.

Pure. `sp.execY Y` is the store after executing `Y` (model ids) from the empty store, as
`swift.applyX` (Deliver.lean) is for the execution record (`swift.applyX_eq_execY`, ReplyChan).
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Model.Seq
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.state.Specs
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.WireWf

@[expose] public section

noncomputable section

set_option linter.unusedSimpArgs false

namespace Perennial.github_com.imdea_software.swiftpaxos

namespace sp

/-- An executed command (model ids): its id, its command, the dependencies it was executed
after. -/
abbrev ExY := CmdId × Cmd × List CmdId

/-- The store after executing `Y` in order from the empty store (`state.execS`). -/
def execY (Y : List ExY) : w64 → Option (List w8) :=
  Y.foldl (fun σ e => (state.execS e.2.1.op e.2.1.key e.2.1.val σ).1) (fun _ => none)

/-- A put of key `k`. -/
def isPutK (k : w64) (e : ExY) : Bool := e.2.1.key == k && e.2.1.isPut

theorem execY_snoc (Y : List ExY) (e : ExY) :
    execY (Y ++ [e]) = (state.execS e.2.1.op e.2.1.key e.2.1.val (execY Y)).1 := by
  unfold execY; rw [List.foldl_append]; rfl

theorem isPut_iff (c : Cmd) : c.isPut = true ↔ c.op = W8 1 := by
  unfold Cmd.isPut opPUT; simp only [beq_iff_eq]; rfl

/-- A key's value after `Y`: its last put's. -/
theorem execY_lookup (Y : List ExY) (k : w64) :
    execY Y k = ((Y.filter (isPutK k)).getLast?).map (fun e => e.2.1.val) := by
  induction Y using revInd with
  | h0 => simp [execY]
  | hs Y e ih =>
    rw [execY_snoc, List.filter_append]
    unfold state.execS
    by_cases hop : e.2.1.op = W8 1
    · have hp : e.2.1.isPut = true := (isPut_iff _).2 hop
      simp only [hop, ↓reduceIte]
      by_cases hk : k = e.2.1.key
      · subst hk
        have : isPutK e.2.1.key e = true := by simp [isPutK, hp]
        simp [this, List.getLast?_append]
      · have : isPutK k e = false := by simp [isPutK, hk, Ne.symm hk]
        simp [this, hk, ih]
    · have hp : e.2.1.isPut = false := by
        cases h : e.2.1.isPut
        · rfl
        · exact absurd ((isPut_iff _).1 h) hop
      have : isPutK k e = false := by simp [isPutK, hp]
      simp only [hop, ↓reduceIte]
      split <;> simp [this, ih]

/-- The hypotheses of `exec_result` on an execution `Y'` against a sequence `s`. -/
structure ExecOk (s : Seq) (Y' : List ExY) : Prop where
  snd : (s.map Prod.fst).Nodup
  ynd : (Y'.map Prod.fst).Nodup
  /-- each command was executed after its dependencies -/
  before : ∀ i e, Y'[i]? = some e → ∀ d ∈ e.2.2, d ∈ (Y'.take i).map Prod.fst
  /-- each command is in `s`, its dependencies there among those it was executed after -/
  ins : ∀ e ∈ Y', (e.1, e.2.1) ∈ s ∧ ∀ d ∈ depsIn s e.1, d ∈ e.2.2

theorem cmdIn_mem (s : Seq) (hnd : (s.map Prod.fst).Nodup) (q : CmdId × Cmd) (hq : q ∈ s) :
    cmdIn s q.1 = some q.2 := by
  obtain ⟨t, u, rfl⟩ := List.append_of_mem hq
  apply cmdIn_split
  intro hm
  simp only [List.map_append, List.map_cons, List.nodup_append, List.nodup_cons] at hnd
  exact hnd.2.2 _ hm _ (List.mem_cons_self) rfl

theorem notin_of_split (t u : Seq) (q : CmdId × Cmd) (hnd : ((t ++ q :: u).map Prod.fst).Nodup) :
    q.1 ∉ t.map Prod.fst := by
  intro hm
  simp only [List.map_append, List.map_cons, List.nodup_append, List.nodup_cons] at hnd
  exact hnd.2.2 _ hm _ (List.mem_cons_self) rfl

theorem ExecOk.cmd_eq {s : Seq} {Y' : List ExY} (h : ExecOk s Y') {e : ExY} (he : e ∈ Y')
    {q : CmdId × Cmd} (hq : q ∈ s) (hid : q.1 = e.1) : q.2 = e.2.1 := by
  have h1 := cmdIn_mem s h.snd q hq
  have h2 := cmdIn_mem s h.snd (e.1, e.2.1) (h.ins e he).1
  rw [hid] at h1; rw [h1] at h2; exact Option.some.inj h2

theorem mem_take_idx {Y' : List ExY} {j : Nat} {d : CmdId} (hd : d ∈ (Y'.take j).map Prod.fst) :
    ∃ j' e, j' < j ∧ Y'[j']? = some e ∧ e.1 = d := by
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hd
  obtain ⟨j', hj'⟩ := List.mem_iff_getElem?.1 he
  rw [List.getElem?_take] at hj'
  split at hj'
  · exact ⟨j', e, by omega, hj', rfl⟩
  · simp at hj'

theorem take_map_mono {Y' : List ExY} {j' j : Nat} (hle : j' ≤ j) {d : CmdId}
    (hd : d ∈ (Y'.take j').map Prod.fst) : d ∈ (Y'.take j).map Prod.fst := by
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hd
  apply List.mem_map_of_mem
  have : Y'.take j' = (Y'.take j).take j' := by rw [List.take_take, Nat.min_eq_left hle]
  rw [this] at he
  exact List.mem_of_mem_take he

/-- **The dependency chains of a put** (the heart of `exec_result`): if a put `w` of `s` was
executed at index `j`, every command of its key before it in `s` was executed before `j`. -/
theorem ExecOk.reach {s : Seq} {Y' : List ExY} (h : ExecOk s Y') :
    ∀ (n : Nat) (t : Seq) (w : CmdId × Cmd) (u : Seq), t.length = n → s = t ++ w :: u →
      w.2.isPut = true → ∀ (j : Nat) (ew : ExY), Y'[j]? = some ew → ew.1 = w.1 →
      ∀ a ∈ t, a.2.key = w.2.key → a.1 ∈ (Y'.take j).map Prod.fst := by
  intro n
  refine Nat.strongRecOn n ?_
  intro n ih t w u htn hs hwp j ew hj hid a ha haK
  have hwt : w.1 ∉ t.map Prod.fst := notin_of_split t u w (hs ▸ h.snd)
  have hmem : ew ∈ Y' := List.mem_of_getElem? hj
  have hws : w ∈ s := by rw [hs]; simp
  have hcmd : w.2 = ew.2.1 := h.cmd_eq hmem hws hid.symm
  have hdeps : ∀ d ∈ lkDeps t w.2, d ∈ (Y'.take j).map Prod.fst := by
    intro d hd
    have hd' : d ∈ depsIn s ew.1 := by
      rw [hid, hs, depsIn_split t u w hwt]; exact hd
    exact h.before j ew hj d ((h.ins ew hmem).2 d hd')
  by_cases hput : ∃ q ∈ t, q.2.key = w.2.key ∧ q.2.isPut = true
  · obtain ⟨b1, L, b2, rfl, hLk, hLp, hb2⟩ := last_put_split t w.2.key hput
    have hL : L.1 ∈ lkDeps (b1 ++ L :: b2) w.2 :=
      (mem_lkDeps _ _ _).2 ⟨b1, L, b2, rfl, rfl, hLk, hb2, Or.inl hLp⟩
    rcases List.mem_append.1 ha with ha1 | ha2
    · obtain ⟨j', eL, hj'j, hj', heL⟩ := mem_take_idx (hdeps L.1 hL)
      have hrec := ih b1.length (by simp at htn; omega) b1 L (b2 ++ w :: u) rfl
        (by rw [hs]; simp) hLp j' eL hj' heL a ha1 (by rw [haK, hLk])
      exact take_map_mono (Nat.le_of_lt hj'j) hrec
    · obtain ⟨c1, c2, hc⟩ := List.append_of_mem ha2
      apply hdeps
      refine (mem_lkDeps _ _ _).2 ⟨b1 ++ c1, a, c2, by rw [hc]; simp, rfl, haK, ?_, Or.inr hwp⟩
      intro q hq hqk
      apply hb2 q _ hqk
      cases c1 with
      | nil => simp at hc; rw [hc.2]; exact hq
      | cons c0 c1' => simp at hc; rw [hc.2]; simp [hq]
  · obtain ⟨c1, c2, hc⟩ := List.append_of_mem ha
    apply hdeps
    refine (mem_lkDeps _ _ _).2 ⟨c1, a, c2, hc, rfl, haK, fun q hq hqk => ?_, Or.inr hwp⟩
    cases hqp : q.2.isPut
    · rfl
    · exact absurd ⟨q, by rw [hc]; simp [hq], hqk, hqp⟩ hput

/-- Every put of `x`'s key executed before `x` is before `x` in `s`. -/
theorem ExecOk.put_before {s : Seq} {Y : List ExY} {y : ExY} (h : ExecOk s (Y ++ [y]))
    (t u : Seq) (hs : s = t ++ (y.1, y.2.1) :: u) (e : ExY) (he : e ∈ Y)
    (hpk : isPutK y.2.1.key e = true) : (e.1, e.2.1) ∈ t := by
  have hnd := h.ynd
  have hxY : y.1 ∉ Y.map Prod.fst := by
    intro hm
    simp only [List.map_append, List.map_cons, List.map_nil, List.nodup_append] at hnd
    exact hnd.2.2 _ hm _ (by simp) rfl
  have heY' : e ∈ Y ++ [y] := List.mem_append_left _ he
  have hes := (h.ins e heY').1
  simp only [isPutK, Bool.and_eq_true, beq_iff_eq] at hpk
  rw [hs] at hes
  rcases List.mem_append.1 hes with h1 | h2
  · exact h1
  · exfalso
    rcases List.mem_cons.1 h2 with h3 | h3
    · exact hxY (List.mem_map.2 ⟨e, he, (Prod.mk.inj h3).1⟩)
    · obtain ⟨u1, u2, hu⟩ := List.append_of_mem h3
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 he
      have hjl : j < Y.length := (List.getElem?_eq_some_iff.1 hj).1
      have hj' : (Y ++ [y])[j]? = some e := by rw [List.getElem?_append_left hjl]; exact hj
      have hr := h.reach _ (t ++ (y.1, y.2.1) :: u1) (e.1, e.2.1) u2 rfl
        (by rw [hs, hu]; simp) hpk.2 j e hj' rfl (y.1, y.2.1) (by simp) hpk.1.symm
      rw [List.take_append_of_le_length (by omega)] at hr
      exact hxY (List.mem_map.2 (by
        obtain ⟨e', he', hid⟩ := List.mem_map.1 hr
        exact ⟨e', List.mem_of_mem_take he', hid⟩))

/-- **`exec_result`**: the last command `y` of an execution `Y ++ [y]` that is `ExecOk` against
`s` gets `resultIn s y.1`. -/
theorem exec_result {s : Seq} {Y : List ExY} {y : ExY} (h : ExecOk s (Y ++ [y])) :
    (state.execS y.2.1.op y.2.1.key y.2.1.val (execY Y)).2 = resultIn s y.1 := by
  have hyin := h.ins y (by simp)
  obtain ⟨t, u, hs⟩ := List.append_of_mem hyin.1
  have hxt : y.1 ∉ t.map Prod.fst := notin_of_split t u (y.1, y.2.1) (hs ▸ h.snd)
  have hcmd : cmdIn s y.1 = some y.2.1 := by rw [hs]; exact cmdIn_split t u (y.1, y.2.1) hxt
  have hbef : before s y.1 = t := by rw [hs]; exact before_split t u (y.1, y.2.1) hxt
  unfold resultIn putsBefore
  rw [hcmd]
  simp only [hbef]
  unfold state.execS
  by_cases hop1 : y.2.1.op = W8 1
  · have : y.2.1.isGet = false := by unfold Cmd.isGet opGET; rw [hop1]; decide
    simp [hop1, this]
  by_cases hop2 : y.2.1.op ≠ W8 2
  · have : y.2.1.isGet = false := by
      unfold Cmd.isGet opGET; simp only [beq_eq_false_iff_ne]; exact hop2
    rw [if_neg hop1, if_neg hop2]; simp [this]
  have hop2 : y.2.1.op = W8 2 := by simpa using hop2
  have hg : y.2.1.isGet = true := by unfold Cmd.isGet opGET; rw [hop2]; decide
  simp only [hop1, hop2, ↓reduceIte, hg]
  congr 1
  rw [execY_lookup]
  -- the puts of the key before `y` in `s`, and those executed before `y`
  by_cases hP : ∃ q ∈ t, q.2.key = y.2.1.key ∧ q.2.isPut = true
  · obtain ⟨b1, pm, b2, rfl, hpk, hpp, hb2⟩ := last_put_split t y.2.1.key hP
    have hPl : ((b1 ++ pm :: b2).filter (fun p => p.2.key == y.2.1.key && p.2.isPut)).getLast? =
        some pm := by
      have h0 : b2.filter (fun p => p.2.key == y.2.1.key && p.2.isPut) = [] := by
        rw [List.filter_eq_nil_iff]; intro q hq; simp only [Bool.and_eq_true, beq_iff_eq, not_and]
        intro hk; rw [hb2 q hq hk]; simp
      rw [List.filter_append, List.filter_cons, h0]; simp [hpk, hpp]
    rw [hPl]
    -- `pm` is a dependency of `y`, so executed before it
    have hdep : pm.1 ∈ depsIn s y.1 := by
      rw [hs, depsIn_split _ u (y.1, y.2.1) hxt]
      exact (mem_lkDeps _ _ _).2 ⟨b1, pm, b2, rfl, rfl, hpk, hb2, Or.inl hpp⟩
    have hyl : (Y ++ [y])[Y.length]? = some y := by simp
    have hpY := h.before Y.length y hyl pm.1 ((h.ins y (by simp)).2 pm.1 hdep)
    rw [List.take_left' rfl] at hpY
    obtain ⟨e, he, heid⟩ := List.mem_map.1 hpY
    have hec : pm.2 = e.2.1 := h.cmd_eq (List.mem_append_left _ he) (by rw [hs]; simp) heid.symm
    obtain ⟨Y1, Y2, hY⟩ := List.append_of_mem he
    have hnd := h.ynd
    rw [hY] at hnd
    have hY2 : Y2.filter (isPutK y.2.1.key) = [] := by
      rw [List.filter_eq_nil_iff]
      intro e2 he2 hp2
      have hin := h.put_before (b1 ++ pm :: b2) u hs e2 (by rw [hY]; simp [he2]) hp2
      have hne : e2.1 ≠ e.1 := by
        intro hq
        simp only [List.map_append, List.map_cons, List.map_nil, List.nodup_append,
          List.nodup_cons] at hnd
        exact hnd.1.2.1.1 (List.mem_map.2 ⟨e2, he2, hq⟩)
      have hnY1 : e2.1 ∉ Y1.map Prod.fst := by
        intro hq
        simp only [List.map_append, List.map_cons, List.map_nil, List.nodup_append,
          List.nodup_cons] at hnd
        exact hnd.1.2.2 _ hq _ (by simp [List.mem_map.2 ⟨e2, he2, rfl⟩]) rfl
      simp only [isPutK, Bool.and_eq_true, beq_iff_eq] at hp2
      rcases List.mem_append.1 hin with h1 | h2
      · -- before `pm`: executed before `e` (`reach` at `pm`)
        have hj : (Y ++ [y])[Y1.length]? = some e := by rw [hY]; simp
        have hr := h.reach _ b1 pm (b2 ++ (y.1, y.2.1) :: u) rfl (by rw [hs]; simp) hpp
          Y1.length e hj heid (e2.1, e2.2.1) h1 (by rw [hp2.1, hpk])
        rw [hY, List.append_assoc, List.take_left' rfl] at hr
        exact hnY1 hr
      · rcases List.mem_cons.1 h2 with h3 | h3
        · exact hne (by rw [heid]; exact congrArg Prod.fst h3)
        · have := hb2 _ h3 hp2.1; simp at this; rw [this] at hp2; exact absurd hp2.2 (by simp)
    have heP : isPutK y.2.1.key e = true := by
      simp [isPutK, ← hec, hpk, hpp]
    rw [hY, List.filter_append, List.filter_cons, heP, hY2]
    simp [hec]
  · -- no put of the key before `y` in `s`: none executed before it
    have h0 : t.filter (fun p => p.2.key == y.2.1.key && p.2.isPut) = [] := by
      rw [List.filter_eq_nil_iff]; intro q hq; simp only [Bool.and_eq_true, beq_iff_eq, not_and]
      intro hk hp; exact hP ⟨q, hq, hk, hp⟩
    have hQ : Y.filter (isPutK y.2.1.key) = [] := by
      rw [List.filter_eq_nil_iff]
      intro e he hp
      have hin := h.put_before t u hs e he hp
      simp only [isPutK, Bool.and_eq_true, beq_iff_eq] at hp
      exact hP ⟨_, hin, hp.1, hp.2⟩
    rw [h0, hQ]; rfl

/-- The results of executions of well-formed commands are short (`Msg.wf`'s value bound). -/
theorem execS_result_wf (Y : List ExY) (hwf : ∀ e ∈ Y, e.2.1.wf) (c : Cmd) :
    (state.execS c.op c.key c.val (execY Y)).2.length < 2 ^ 16 := by
  unfold state.execS
  split
  · simp
  split
  · rw [execY_lookup]
    cases hl : (Y.filter (isPutK c.key)).getLast? with
    | none => simp
    | some e =>
      have he : e ∈ Y := (List.mem_filter.1 (List.mem_of_getLast? hl)).1
      have := hwf e he; unfold Cmd.wf at this; simpa using this
  · simp

end sp

end Perennial.github_com.imdea_software.swiftpaxos
