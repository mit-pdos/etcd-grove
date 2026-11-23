/-
The executor's command step (`Sys.execCmd`, p-modelexec): the replica's store, its command index,
and, at a first execution, the key's global sequence and the op's output. `Inv` is kept: the
executed writes stay prefixes of the global ones (`exec_first`/`exec_again`), the new slot's op
is a client op owning no other executed slot (the proposal tokens).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.AuxSteps

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

open github_com.imdea_software.swiftpaxos_epaxos.kvs AuxProof

namespace ExecOrd

/-! ## Lists -/

theorem filter_lt_range (m : Nat) :
    ∀ n, m ≤ n → (List.range n).filter (fun j => decide (j < m)) = List.range m
  | 0, h => by simp at h; subst h; rfl
  | n + 1, h => by
    rw [List.range_succ, List.filter_append]
    by_cases hm : m = n + 1
    · subst hm
      rw [show (List.range n).filter (fun j => decide (j < n + 1)) = List.range n by
        rw [List.filter_eq_self]; intro a ha; simp at ha ⊢; omega]
      simp [List.range_succ]
    · rw [filter_lt_range m n (by omega)]
      simp; omega

theorem blk_filter (σ : RState) (k : w64) (x : InstId) (m : Nat) (hm : m ≤ (cmdsAt σ x).length) :
    (blk σ k x).filter (fun e => decide (e.1.2 < m)) =
      ((List.range m).map (fun idx => ((x, idx), (cmdsAt σ x).getD idx default))).filter
        (fun e => e.2.op ≠ opNONE ∧ Sys.touches e.2 k) := by
  unfold blk
  rw [← filter_lt_range m _ hm]
  simp only [List.filter_map, List.filter_filter]
  congr 1
  apply List.filter_congr
  intro j _
  simp only [Function.comp, Bool.and_comm]

theorem blk_succ (σ : RState) (k : w64) (x : InstId) (idx : Nat)
    (h : idx < (cmdsAt σ x).length) :
    (blk σ k x).filter (fun e => decide (e.1.2 < idx + 1)) =
      (blk σ k x).filter (fun e => decide (e.1.2 < idx)) ++
        (if ((cmdsAt σ x).getD idx default).op ≠ opNONE ∧ Sys.touches ((cmdsAt σ x).getD idx default) k
          then [((x, idx), (cmdsAt σ x).getD idx default)] else []) := by
  rw [blk_filter _ _ _ _ h, blk_filter _ _ _ _ (Nat.le_of_lt h), List.range_succ, List.map_append,
    List.filter_append]
  congr 1
  simp only [List.map_cons, List.map_nil, List.filter_cons, List.filter_nil]
  split <;> simp_all

theorem lastPut_snoc (l : List (Slot × WCmd)) (e : Slot × WCmd) :
    Sys.lastPut (l ++ [e]) = if e.2.op = opPUT then some e.2.val else Sys.lastPut l := by
  simp [Sys.lastPut, List.foldl_append]

theorem writes_append (l l' : List (Slot × WCmd)) :
    Sys.writes (l ++ l') = Sys.writes l ++ Sys.writes l' := List.filter_append ..

/-- A decomposition of a list with a last element. -/
theorem decomp_snoc {α : Type} {l pre post : List α} {a b : α}
    (h : l ++ [a] = pre ++ b :: post) :
    (post = [] ∧ pre = l ∧ b = a) ∨ (∃ post', post = post' ++ [a] ∧ l = pre ++ b :: post') := by
  rcases List.eq_nil_or_concat post with rfl | ⟨L, z, rfl⟩
  · left
    have := List.append_inj' (s₁ := l) (s₂ := pre) (t₁ := [a]) (t₂ := [b]) h rfl
    simp only [List.cons.injEq, and_true] at this
    exact ⟨rfl, this.1.symm, this.2.symm⟩
  · right
    have h' : l ++ [a] = (pre ++ b :: L) ++ [z] := by rw [h]; simp [List.concat_eq_append]
    have := List.append_inj' h' rfl
    simp only [List.cons.injEq, and_true] at this
    exact ⟨L, by rw [this.2, List.concat_eq_append], this.1⟩

/-! ## `before`, `outOf`, `touches` -/

theorem before_not_mem {l : List (Slot × WCmd)} {e : Slot × WCmd} (h : e ∉ l) :
    Sys.before l e = l := by
  unfold Sys.before
  induction l with
  | nil => rfl
  | cons a l ih =>
    have ha : a ≠ e := fun h' => h (h' ▸ List.mem_cons_self ..)
    have := ih (fun h' => h (List.mem_cons_of_mem _ h'))
    simp only [ne_eq, decide_not] at this
    simp [ha, this]

theorem before_append_of_mem {l : List (Slot × WCmd)} {e : Slot × WCmd} (t : List (Slot × WCmd))
    (h : e ∈ l) : Sys.before (l ++ t) e = Sys.before l e := by
  unfold Sys.before
  induction l with
  | nil => cases h
  | cons a l ih =>
    by_cases ha : a = e
    · subst ha; simp
    · have := ih ((List.mem_cons.mp h).resolve_left (Ne.symm ha))
      simp only [ne_eq, decide_not] at this
      simp [ha, this]

/-- `outOf` reads only the sequences of the keys the command touches. -/
theorem outOf_congr {G G' : w64 → List (Slot × WCmd)} (c : WCmd)
    (h : ∀ k, Sys.touches c k → G k = G' k) : Sys.outOf G c = Sys.outOf G' c := by
  unfold Sys.outOf
  by_cases hg : c.op = opGET
  · simp only [hg, if_true, h c.key (Or.inl rfl)]
  · by_cases hs : c.op = opSCAN
    · rw [if_neg hg, if_neg hg, if_pos hs, if_pos hs]
      have key : ∀ l : List w64, (∀ k ∈ l, Sys.touches c k) →
          l.filterMap (fun k => Sys.lastPut (G k)) = l.filterMap (fun k => Sys.lastPut (G' k)) := by
        intro l hl
        induction l with
        | nil => rfl
        | cons a l ih =>
          simp only [List.filterMap_cons, h a (hl a (List.mem_cons_self ..)),
            ih (fun k hk => hl k (List.mem_cons_of_mem _ hk))]
      rw [key _ (fun k hk => Or.inr ⟨hs, hk⟩)]
    · simp only [hg, hs, if_false]

theorem touches_iff_of_ne {c : WCmd} {k : w64} (h : c.op ≠ opSCAN) :
    Sys.touches c k ↔ c.key = k := by
  unfold Sys.touches; constructor
  · rintro (h' | ⟨h', -⟩)
    · exact h'
    · exact absurd h' h
  · exact Or.inl

/-! ## The step's shape -/

/-- The store after a command. -/
def newStore (σ : RState) (c : WCmd) : w64 → Option (List w8) :=
  if c.op = opPUT then upd σ.store c.key (some c.val) else σ.store

theorem execCmdAt_eq (σ : RState) (w : InstRec) (idx : Nat) :
    (execCmdAt σ w idx).1 = { σ with store := newStore σ ((w.cmds.getD []).getD idx default) } ∧
      ∀ o ∈ (execCmdAt σ w idx).2, ∃ a b, o = Out.reply a b := by
  unfold execCmdAt newStore
  generalize (w.cmds.getD []).getD idx default = c
  by_cases hn : c.op = opNONE
  · have : c.op ≠ opPUT := by rw [hn]; decide
    simp only [hn, this, if_true, if_false]
    exact ⟨by cases σ; rfl, by simp⟩
  · simp only [hn, if_false]
    cases hcp : w.lb.bind (·.clientProposals) with
    | some ps =>
      by_cases hp : c.op = opPUT
      · simp [hp, execCmd]
      · by_cases hg : c.op = opGET
        · simp only [execCmd, hp, hg, if_false, if_true]
          constructor <;> (try simp) <;> (try (cases σ; rfl))
        · by_cases hs : c.op = opSCAN
          · simp only [execCmd, hp, hg, hs, if_false, if_true]
            constructor <;> (try simp) <;> (try (cases σ; rfl))
          · simp only [execCmd, hp, hg, hs, if_false]
            constructor <;> (try simp) <;> (try (cases σ; rfl))
    | none =>
      by_cases hp : c.op = opPUT
      · simp [hp, execCmd]
      · simp only [hp, if_false]
        constructor <;> (try simp) <;> (try (cases σ; rfl))

theorem foldl_emit_replies (i : Nat) : ∀ (os : List Out) (T : Sys),
    (∀ o ∈ os, ∃ a b, o = Out.reply a b) → os.foldl (fun S o => S.emit i o) T = T
  | [], T, _ => rfl
  | o :: os, T, h => by
    obtain ⟨a, b, rfl⟩ := h o (by simp)
    exact foldl_emit_replies i os T (fun o' ho => h o' (by simp [ho]))

section
variable (S : Sys) (i : Nat) (x : InstId) (w : InstRec) (idx : Nat) (c : WCmd)
  (hidef : S.execIdx i = idx) (hcdef : (w.cmds.getD []).getD idx default = c)
include hidef hcdef

/-- Whether the slot is executed for the first time anywhere. -/
abbrev Fire (S : Sys) (x : InstId) (idx : Nat) (c : WCmd) : Prop :=
  c.op ≠ opNONE ∧ ((x, idx), c) ∉ S.gexec c.key

theorem execCmd_shape :
    (S.execCmd i x w).rep = upd S.rep i { S.rep i with store := newStore (S.rep i) c } ∧
    (S.execCmd i x w).execIdx = upd S.execIdx i (idx + 1) ∧
    (S.execCmd i x w).gexec =
      (if Fire S x idx c then
        (fun k => if Sys.touches c k then S.gexec k ++ [((x, idx), c)] else S.gexec k)
       else S.gexec) ∧
    (S.execCmd i x w).fired =
      (if Fire S x idx c then
        (match S.slotOp (x, idx) with
          | some p => upd S.fired p.cid (some (Sys.outOf S.gexec c))
          | none => S.fired)
       else S.fired) ∧
    (S.execCmd i x w).sent = S.sent ∧ (S.execCmd i x w).outbox = S.outbox ∧
    (S.execCmd i x w).pending = S.pending ∧ (S.execCmd i x w).delivered = S.delivered ∧
    (S.execCmd i x w).ops = S.ops ∧ (S.execCmd i x w).proposeChan = S.proposeChan ∧
    (S.execCmd i x w).owner = S.owner ∧ (S.execCmd i x w).execLog = S.execLog ∧
    (S.execCmd i x w).execCur = S.execCur ∧ (S.execCmd i x w).hist = S.hist := by
  obtain ⟨h1, h2⟩ := execCmdAt_eq (S.rep i) w idx
  rw [hcdef] at h1
  have hA : S.applyStep i (execCmdAt (S.rep i) w idx) =
      { S with rep := upd S.rep i { S.rep i with store := newStore (S.rep i) c } } := by
    unfold Sys.applyStep
    rw [foldl_emit_replies i _ _ h2, h1]
  unfold Sys.execCmd
  simp only [hidef, hcdef]
  rw [hA]
  by_cases hn : c.op = opNONE
  · have : ¬ Fire S x idx c := fun h => h.1 hn
    simp only [hn, this, ite_true, ite_false]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial
  · simp only [hn, ite_false, Sys.fire]
    by_cases hg : ((x, idx), c) ∈ S.gexec c.key
    · have : ¬ Fire S x idx c := fun h => h.2 hg
      simp only [hg, this, ite_true, ite_false]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial
    · have : Fire S x idx c := ⟨hn, hg⟩
      simp only [hg, ite_true, ite_false, Sys.slotOp, if_pos this]
      cases (S.owner x).bind (fun ps => ps[idx]?) <;> dsimp only <;>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial

end

/-! ## Facts about the slot -/

/-- A slot with a non-NONE decided command is in an instance holding its proposals. -/
theorem not_dead {S : Sys} (h0 : Inv0 S) {y : InstId} {v : Val} {j : Nat} {c' : WCmd}
    (hv : S.committedVal y v) (hj : v.cmds[j]? = some c') (hc : c'.op ≠ opNONE) :
    ¬ S.propDead y := by
  rintro ⟨⟨v', c0, hv', hcs, hc0⟩, -⟩
  have := I0.uniq h0 hv hv'
  subst this
  rw [hcs] at hj
  cases j with
  | zero => simp at hj; subst hj; exact hc hc0
  | succ j => simp at hj

section
variable {S : Sys} (h0 : Inv0 S) {i : Nat} {x : InstId} {rest : List InstId} {w : InstRec}
  {idx : Nat} {c : WCmd} (hi : i < nR) (hcur : S.execCur i = x :: rest)
  (hw : (S.rep i).inst x = some w) (hcdef : (w.cmds.getD []).getD idx default = c)
  (hidx : idx < (w.cmds.getD []).length) (hc : c.op ≠ opNONE)
include h0 hi hcur hw hcdef hidx hc

theorem slot_info :
    S.committedVal x (instVal w) ∧ (instVal w).cmds[idx]? = some c ∧
    ∃ p, S.slotOp (x, idx) = some p ∧ p.cmd = c := by
  have hxe : x ∈ S.eseq i := by simp [Sys.eseq, hcur]
  obtain ⟨w', hw', -, -, hcv, -⟩ := eseq_info h0 hi hxe
  rw [hw] at hw'; cases hw'
  have hget : (instVal w).cmds[idx]? = some c := by
    simp only [instVal]; rw [← hcdef, List.getElem?_eq_getElem hidx, ← List.getElem_eq_getD]
  refine ⟨hcv, hget, ?_⟩
  rcases (I0.slots h0).1 x _ hcv with hn | ⟨ps, hps, hcm⟩
  · rw [hn] at hget
    cases idx with
    | zero => simp [noop] at hget; subst hget; exact absurd rfl hc
    | succ j => simp [noop] at hget
  · rw [hcm, List.getElem?_map] at hget
    cases hp : ps[idx]? with
    | none => rw [hp] at hget; cases hget
    | some p =>
      rw [hp] at hget
      simp only [Option.map_some, Option.some.injEq] at hget
      exact ⟨p, by simp [Sys.slotOp, hps, hp], hget⟩

end

/-! ## The command step keeps `Inv` -/

section
variable {S : Sys} (hS : Inv S) {i : Nat} {x : InstId} {rest : List InstId} {w : InstRec}
  (hi : i < nR) (hcur : S.execCur i = x :: rest) (hw : (S.rep i).inst x = some w)
  (hidx : S.execIdx i < (w.cmds.getD []).length)
include hS hi hcur hw hidx

theorem inv_step_execCmd'' : Inv (S.execCmd i x w) := by
  have h0 := hS.1
  have hX := hS.2.exec
  generalize hidef : S.execIdx i = idx at hidx
  generalize hcdef : (w.cmds.getD []).getD idx default = c
  obtain ⟨erep, eidx, egex, efir, esent, eob, epend, edel, eops, echan, eown, elog, ecur, ehist⟩ :=
    execCmd_shape S i x w idx c hidef hcdef
  have hcmdx : cmdsAt (S.rep i) x = w.cmds.getD [] := by simp [cmdsAt, hw]
  -- the slot, when it is a command
  have hslot := fun (hc : c.op ≠ opNONE) => slot_info h0 hi hcur hw hcdef hidx hc
  have hxi : x ∈ S.eseq i := by simp [Sys.eseq, hcur]
  have hfirst := fun (hc : c.op ≠ opNONE) =>
    exec_first h0 hX hi hcur hw hidef hcdef hidx hc
  have hagain := fun (hc : c.op ≠ opNONE) =>
    exec_again h0 hX hi hcur hw hidef hcdef hidx hc
  generalize S.execCmd i x w = S' at *
  -- the replicas
  have hinst : ∀ r, (S'.rep r).inst = (S.rep r).inst := by
    intro r; rw [erep]; by_cases h : r = i
    · subst h; simp
    · simp [upd_other _ _ _ _ h]
  have hid : ∀ r, (S'.rep r).id = (S.rep r).id := by
    intro r; rw [erep]; by_cases h : r = i
    · subst h; simp
    · simp [upd_other _ _ _ _ h]
  have hcrt : ∀ r, (S'.rep r).crtInstance = (S.rep r).crtInstance := by
    intro r; rw [erep]; by_cases h : r = i
    · subst h; simp
    · simp [upd_other _ _ _ _ h]
  have hcf : ∀ r, (S'.rep r).conflicts = (S.rep r).conflicts := by
    intro r; rw [erep]; by_cases h : r = i
    · subst h; simp
    · simp [upd_other _ _ _ _ h]
  have hcls : ∀ r, (S'.rep r).lastScan = (S.rep r).lastScan ∧
      (S'.rep r).lastPut = (S.rep r).lastPut := by
    intro r; rw [erep]; by_cases h : r = i
    · subst h; simp
    · simp [upd_other _ _ _ _ h]
  have hexe : ∀ r, (S'.rep r).execedUpTo = (S.rep r).execedUpTo := by
    intro r; rw [erep]; by_cases h : r = i
    · subst h; simp
    · simp [upd_other _ _ _ _ h]
  have hpo : ∀ r, (S'.rep r).peerOrder = (S.rep r).peerOrder := by
    intro r; rw [erep]; by_cases h : r = i
    · subst h; simp
    · simp [upd_other _ _ _ _ h]
  have hsto : ∀ r, (S'.rep r).store = if r = i then newStore (S.rep i) c else (S.rep r).store := by
    intro r; rw [erep]; by_cases h : r = i
    · subst h; simp
    · simp [upd_other _ _ _ _ h, h]
  have hle : ∀ r, sccLe (S'.rep r) = sccLe (S.rep r) := by
    intro r; funext a b; simp only [sccLe, hinst]
  have hmsgs : S'.msgs = S.msgs := by
    funext fr to; simp only [Sys.msgs, Sys.intended, esent, eob, epend]
  have hcmd : ∀ r y, cmdsAt (S'.rep r) y = cmdsAt (S.rep r) y := by
    intro r y; simp only [cmdsAt, hinst]
  -- the executed sequences
  have hlx : ∀ r k, S'.lexec r k = if r = i ∧ c.op ≠ opNONE ∧ Sys.touches c k then
      S.lexec r k ++ [((x, idx), c)] else S.lexec r k := by
    intro r k
    have hso : ∀ r, Sys.slotsOn (S'.rep r) = Sys.slotsOn (S.rep r) := by
      intro r; funext xs k; exact slotsOn_congr_cmds _ _ k xs (fun y _ => hcmd r y)
    unfold Sys.lexec Sys.curSlots
    simp only [hso, elog, ecur, eidx]
    by_cases hr : r = i
    · subst hr
      simp only [hcur, upd_same, slotsOn_eq, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [blk_succ _ k x idx (by rw [hcmdx]; exact hidx), hcmdx, hcdef, hidef]
      by_cases hc : c.op ≠ opNONE ∧ Sys.touches c k
      · rw [if_pos hc, if_pos (by first | exact ⟨rfl, hc⟩ | exact ⟨trivial, hc⟩ | exact hc),
          List.append_assoc]
      · rw [if_neg hc, if_neg (by first | exact (fun h => hc h.2) | exact hc), List.append_nil]
    · simp only [upd_other _ _ _ _ hr, hr, false_and, if_false]
  -- the global sequences
  have hgk : ∀ k, S'.gexec k = if Fire S x idx c ∧ Sys.touches c k then
      S.gexec k ++ [((x, idx), c)] else S.gexec k := by
    intro k; rw [egex]
    by_cases hf : Fire S x idx c
    · rw [if_pos hf]
      by_cases hk : Sys.touches c k
      · rw [if_pos hk, if_pos ⟨hf, hk⟩]
      · rw [if_neg hk, if_neg (fun h => hk h.2)]
    · rw [if_neg hf, if_neg (fun h => hf h.1)]
  have hgpre : ∀ k, S.gexec k <+: S'.gexec k := by
    intro k; rw [hgk]; split
    · exact List.prefix_append _ _
    · exact List.prefix_refl _
  have hgmem : ∀ k e', e' ∈ S'.gexec k ↔
      e' ∈ S.gexec k ∨ (Fire S x idx c ∧ Sys.touches c k ∧ e' = ((x, idx), c)) := by
    intro k e'; rw [hgk]; split
    · rename_i h
      obtain ⟨hf, hk⟩ := h
      simp only [List.mem_append, List.mem_singleton]
      constructor
      · rintro (a | a)
        · exact Or.inl a
        · exact Or.inr ⟨hf, hk, a⟩
      · rintro (a | ⟨-, -, a⟩)
        · exact Or.inl a
        · exact Or.inr a
    · rename_i h
      constructor
      · exact Or.inl
      · rintro (h' | ⟨h1, h2, -⟩)
        · exact h'
        · exact absurd ⟨h1, h2⟩ h
  have hwpre : ∀ {l l' : List (Slot × WCmd)}, l <+: l' → Sys.writes l <+: Sys.writes l' := by
    intro l l' ⟨t, ht⟩; exact ⟨Sys.writes t, by rw [← ht, writes_append]⟩
  have hcvS : ∀ y v, S'.committedVal y v ↔ S.committedVal y v := by
    intro y v; simp only [Sys.committedVal, Sys.ev, ehist, hmsgs]
  have hso' : S'.slotOp = S.slotOp := by funext s; simp only [Sys.slotOp, eown]
  -- `Inv0`
  have h0' : Inv0 S' := by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
      h20, h21, h22, h23, h24, h25, h26, h27⟩ := h0
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_⟩
    case refine_19 =>
      intro r hr
      have := h19 r hr
      simp only [ecur, eidx, RState.executed, RState.ready, RState.depEdge, sccSort, hle, hinst] at this ⊢
      by_cases h : r = i
      · subst h
        rw [upd_same]
        obtain ⟨-, h2⟩ := this
        refine ⟨fun h => (by rw [hcur] at h; cases h), fun hne => ?_⟩
        obtain ⟨done, C, a1, a2, a3, a4, a5, a6, a7⟩ := h2 hne
        refine ⟨done, C, a1, a2, a3, a4, a5, a6, fun y w' hy hw' => ?_⟩
        rw [hcur] at hy; simp only [List.head?_cons, Option.some.injEq] at hy; subst hy
        rw [hw] at hw'; cases hw'; omega
      · simp only [upd_other _ _ _ _ h]; exact this
    case refine_21 =>
      obtain ⟨p1, p2, p3⟩ := h21
      refine ⟨fun r hr k => ?_, fun r hr k => ?_, fun r hr k pre e post hsp => ?_⟩
      · rw [hlx]
        split
        · rename_i hc; obtain ⟨rfl, hcn, hk⟩ := hc
          by_cases hg : ((x, idx), c) ∈ S.gexec c.key
          · obtain ⟨pre, post, hgd, hwr⟩ := (hagain hcn hg).1 k hk
            rw [hgk, if_neg (fun h => h.1.2 hg), hgd, writes_append, ← hwr, writes_append]
            exact ⟨Sys.writes post, by
              rw [show ((x, idx), c) :: post = [((x, idx), c)] ++ post from rfl, writes_append]
              simp [List.append_assoc]⟩
          · rw [hgk, if_pos ⟨⟨hcn, hg⟩, hk⟩, writes_append, writes_append, hfirst hcn hg k hk]
            exact List.prefix_refl _
        · exact (p1 r hr k).trans (hwpre (hgpre k))
      · rw [hlx, hsto]
        by_cases hr' : r = i
        · subst hr'
          simp only [if_true, true_and]
          unfold newStore
          by_cases hc : c.op ≠ opNONE ∧ Sys.touches c k
          · rw [if_pos hc, lastPut_snoc, ← p2 r hr k]
            by_cases hp : c.op = opPUT
            · have hk := (touches_iff_of_ne (by rw [hp]; decide)).mp hc.2
              simp only [hp, if_true]; rw [← hk, upd_same]
            · simp only [hp, if_false]
          · rw [if_neg hc]
            by_cases hp : c.op = opPUT
            · have : k ≠ c.key := fun e => hc ⟨by rw [hp]; decide, Or.inl e.symm⟩
              simp only [hp, if_true]; rw [upd_other _ _ _ _ this]; exact p2 r hr k
            · simp only [hp, if_false]; exact p2 r hr k
        · simp only [hr', if_false, false_and]; exact p2 r hr k
      · rw [hlx] at hsp
        split at hsp
        · rename_i hc; obtain ⟨rfl, hcn, hk⟩ := hc
          rcases decomp_snoc hsp with ⟨rfl, rfl, rfl⟩ | ⟨post', rfl, hsp'⟩
          · by_cases hg : ((x, idx), c) ∈ S.gexec c.key
            · obtain ⟨gpre, gpost, hgd, hwr⟩ := (hagain hcn hg).1 k hk
              refine ⟨gpre, gpost, ?_, hwr.symm⟩
              rw [hgk, if_neg (fun h => h.1.2 hg)]; exact hgd
            · refine ⟨S.gexec k, [], ?_, (hfirst hcn hg k hk).symm⟩
              rw [hgk, if_pos ⟨⟨hcn, hg⟩, hk⟩]
          · obtain ⟨gpre, gpost, hgd, hwr⟩ := p3 r hr _ pre e post' hsp'
            obtain ⟨t, ht⟩ := hgpre k
            exact ⟨gpre, gpost ++ t, by rw [← ht, hgd]; simp, hwr⟩
        · obtain ⟨gpre, gpost, hgd, hwr⟩ := p3 r hr k pre e post hsp
          obtain ⟨t, ht⟩ := hgpre k
          exact ⟨gpre, gpost ++ t, by rw [← ht, hgd]; simp, hwr⟩
    case refine_20 =>
      have hdE : S'.dEdge = S.dEdge := by funext a b; simp only [Sys.dEdge, hcvS]
      have hsO : S'.sccOrd = S.sccOrd := by funext a b; simp only [Sys.sccOrd, hcvS]
      intro r hr i0 j a b hij ha hb ht
      rw [elog] at ha hb; rw [hdE] at ht ⊢; rw [hsO]
      exact h20 r hr i0 j a b hij ha hb ht
    case refine_23 =>
      obtain ⟨c1, c2, c3, c4, c5⟩ := h23
      by_cases hf : Fire S x idx c
      case neg =>
        have hg' : S'.gexec = S.gexec := by funext k; rw [hgk, if_neg (fun h => hf h.1)]
        have hf' : S'.fired = S.fired := by rw [efir, if_neg hf]
        refine ⟨by rw [eops]; exact c1, ?_, ?_, ?_, ?_⟩ <;>
        simp only [hg', hf', hso', hcvS] <;> assumption
      case pos =>
        obtain ⟨hcn, hg⟩ := hf
        obtain ⟨hcvx, hcmdi, p, hp, hpc⟩ := hslot hcn
        have h0r : Inv0 S := ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
          h17, h18, h19, h20, h21, h22, ⟨c1, c2, c3, c4, c5⟩, h24, h25, h26, h27⟩
        -- no executed slot is the new one, or another slot of its op
        have hE : ∀ k2 e2, e2 ∈ S.gexec k2 → e2.1 = (x, idx) → False := by
          intro k2 e2 hm2 he
          obtain ⟨-, -, d3, -, v, hv, hvc⟩ := c4 k2 e2 hm2
          rw [he] at hv hvc
          have := I0.uniq h0r hv hcvx
          subst this
          simp only at hvc
          rw [hcmdi] at hvc
          have hc2 : e2.2 = c := (Option.some.inj hvc).symm
          have he' : e2 = ((x, idx), c) := by
            obtain ⟨a, b⟩ := e2; simp only at he hc2; subst he hc2; rfl
          subst he'
          exact hg (d3 c.key (Or.inl rfl))
        have hEn : ∀ k, ((x, idx), c) ∉ S.gexec k := fun k h => hE k _ h rfl
        have hK : ∀ k2 e2 p2, e2 ∈ S.gexec k2 → S.slotOp e2.1 = some p2 → p2.cid = p.cid → False := by
          intro k2 e2 p2 hm2 hs2 hc2
          by_cases he : e2.1 = (x, idx)
          · exact hE k2 e2 hm2 he
          · obtain ⟨-, hn2, -, -, v, hv, hvc⟩ := c4 k2 e2 hm2
            rcases hX.tokSlot (x, idx) e2.1 p p2 (Ne.symm he) hp hs2 hc2.symm with h | h
            · exact not_dead h0r hcvx hcmdi hcn h
            · exact not_dead h0r hv hvc hn2 h
        have hf' : ∀ cid, S'.fired cid =
            if cid = p.cid then some (Sys.outOf S.gexec c) else S.fired cid := by
          intro cid; rw [efir, if_pos ⟨hcn, hg⟩, hp]; simp only [upd_apply]
        have hfire : Fire S x idx c := ⟨hcn, hg⟩
        -- the sequences before the new slot are the old ones
        have hbnew : (fun k => Sys.before (S'.gexec k) ((x, idx), c)) = S.gexec := by
          funext k; rw [hgk]; split
          · exact takeWhile_split _ [] _ (hEn k)
          · exact before_not_mem (hEn k)
        -- the sequences before an old slot are the old ones, at the keys it touches
        have hbold : ∀ e', (∀ k, Sys.touches e'.2 k → e' ∈ S.gexec k) →
            Sys.outOf (fun k => Sys.before (S'.gexec k) e') e'.2 =
              Sys.outOf (fun k => Sys.before (S.gexec k) e') e'.2 := by
          intro e' hall
          refine outOf_congr _ (fun k hk => ?_)
          rw [hgk]; split
          · exact before_append_of_mem _ (hall k hk)
          · rfl
        have c2' : ∀ (k1 k2 : w64) (e1 e2 : Slot × WCmd) (p1 p2 : Proposal), e1 ∈ S'.gexec k1 →
            e2 ∈ S'.gexec k2 → S'.slotOp e1.1 = some p1 → S'.slotOp e2.1 = some p2 →
            p1.cid = p2.cid → e1.1 = e2.1 := by
          intro k1 k2 e1 e2 p1 p2 hm1 hm2 hs1 hs2 hc12
          rw [hso'] at hs1 hs2
          rcases (hgmem k1 e1).mp hm1 with g1 | ⟨-, -, rfl⟩ <;>
            rcases (hgmem k2 e2).mp hm2 with g2 | ⟨-, -, rfl⟩
          · exact c2 k1 k2 e1 e2 p1 p2 g1 g2 hs1 hs2 hc12
          · rw [hp] at hs2; cases hs2; exact (hK k1 e1 p1 g1 hs1 hc12).elim
          · rw [hp] at hs1; cases hs1; exact (hK k2 e2 p2 g2 hs2 hc12.symm).elim
          · rfl
        refine ⟨by rw [eops]; exact c1, c2', fun k => ?_, fun k e' he' => ?_, fun cid o => ?_⟩
        · rw [hgk]; split
          · rw [List.map_append, List.nodup_append]
            refine ⟨c3 k, by simp, fun a ha b hb e => ?_⟩
            simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
            obtain ⟨e2, hm2, rfl⟩ := List.mem_map.mp ha
            exact hE _ e2 hm2 (e.trans hb)
          · exact c3 k
        · rw [hso']
          rcases (hgmem k e').mp he' with g | ⟨-, hk, rfl⟩
          · obtain ⟨d1, d2, d3, d4, v, hv, hvc⟩ := c4 k e' g
            exact ⟨d1, d2, fun k' hk' => (hgpre k').subset (d3 k' hk'), d4, v, (hcvS _ _).mpr hv, hvc⟩
          · refine ⟨hk, hcn, fun k' hk' => ?_, ⟨p, hp, hpc⟩, _, (hcvS _ _).mpr hcvx, hcmdi⟩
            exact (hgmem k' _).mpr (Or.inr ⟨hfire, hk', rfl⟩)
        · rw [hf']
          split
          · rename_i hcid; subst hcid
            constructor
            · intro ho
              refine ⟨((x, idx), c), p, ?_, by rw [hso']; exact hp, rfl, ?_⟩
              · exact (hgmem _ _).mpr (Or.inr ⟨hfire, Or.inl rfl, rfl⟩)
              · rw [← (Option.some.inj ho)]; simp only; rw [hbnew]
            · rintro ⟨e', p', hm', hs', hc', rfl⟩
              rw [hso'] at hs'
              rcases (hgmem _ e').mp hm' with g | ⟨-, -, rfl⟩
              · exact (hK _ e' p' g hs' hc').elim
              · simp only; rw [hbnew]
          · rename_i hcid
            rw [c5 cid o]
            constructor
            · rintro ⟨e', p', hm', hs', hc', ho⟩
              refine ⟨e', p', (hgpre _).subset hm', by rw [hso']; exact hs', hc', ?_⟩
              rw [ho, hbold e' (c4 _ e' hm').2.2.1]
            · rintro ⟨e', p', hm', hs', hc', ho⟩
              rw [hso'] at hs'
              rcases (hgmem _ e').mp hm' with g | ⟨-, -, rfl⟩
              · refine ⟨e', p', g, hs', hc', ?_⟩
                rw [ho, hbold e' (c4 _ e' g).2.2.1]
              · rw [hp] at hs'; cases hs'; exact absurd hc'.symm hcid
    all_goals
      simp only [Inv.wf, Inv.msgWf, Inv.replyTargets, Inv.noTPA, Inv.ballots, Inv.ballotOwner,
        Inv.oneProposal, Inv.votesFollowProposals, Inv.repliesReportVotes, Inv.prepReplyHighest,
        Inv.lbInv, Inv.agreement, Inv.decidedChosen, Inv.chosenSafe, Inv.depsCover, Inv.witnesses,
        Inv.attrsCover, Inv.execClosed, Inv.execOrder, Inv.slots, Inv.commitMsgs, Inv.pendingKind,
        Inv.safe, Inv.reports, Sys.safeAcc, Sys.safePh, Sys.blocked, Sys.fastBlocked, Sys.noPA,
        Sys.fastLive, Sys.fastReplies, Sys.slowChosen, Sys.committedVal, Sys.ev, Sys.evBefore,
        Sys.prepReport, Sys.dEdge, Sys.sccOrd, Sys.deliveredMsg, Sys.slotOp, RState.executed,
        RState.ready, RState.depEdge, hinst, hid, hcrt, hcf, hexe, hmsgs, esent, eob, epend, edel,
        eops, eown, elog, ecur, ehist] at * <;>
      assumption
  -- `InvAux` and `InvExec`
  have hdE : S'.dEdge = S.dEdge := by funext a b; simp only [Sys.dEdge, hcvS]
  have hsO : S'.sccOrd = S.sccOrd := by funext a b; simp only [Sys.sccOrd, hcvS]
  have hes : S'.eseq = S.eseq := by funext r; simp only [Sys.eseq, elog, ecur]
  have hdead : ∀ y, S'.propDead y ↔ S.propDead y := by
    intro y; simp only [Sys.propDead, hcvS, hinst]
  have hX' : InvExec S' := by
    refine ⟨fun r hr a b => ?_, fun r hr l1 l2 a b => ?_, fun k e' he' => ?_,
      fun s s' p p' => ?_, fun j p s p' => ?_, fun j1 j2 n m p p' => ?_, fun j p => ?_⟩
    · rw [hes, hdE]; exact hX.reach r hr a b
    · rw [hes, hdE, hsO]; exact hX.ord r hr l1 l2 a b
    · rcases (hgmem k e').mp he' with g | ⟨⟨hcn, -⟩, hk, rfl⟩
      · obtain ⟨r, hr, h⟩ := hX.gloc k e' g
        refine ⟨r, hr, ?_⟩
        rw [hlx]; split
        · exact List.mem_append_left _ h
        · exact h
      · exact ⟨i, hi, by rw [hlx, if_pos ⟨rfl, hcn, hk⟩]; simp⟩
    · rw [hso', hdead, hdead]; exact hX.tokSlot s s' p p'
    · rw [echan, hso', hdead]; exact hX.tokChan j p s p'
    · rw [echan]; exact hX.chanOnce j1 j2 n m p p'
    · rw [echan, eops]; exact hX.chanOps j p
  exact ⟨h0', aux_congr S S' hS.2 h0.1.2.2.2.2.2.2.1
    (frame_same S S' hinst hcrt hpo ehist hmsgs (fun d h => by rw [edel]; exact h) hcf eown hS.2 hcls)
    (PMProof.pm_same hS.2.pm hinst ehist hmsgs (fun _ _ _ h => by rw [esent]; exact h) epend
      (fun _ _ _ h => by rw [esent, eob] at h; exact h)) hX'
    (execLo_of_eq hS.2.execLo (fun r _ => hexe r))⟩

end

end ExecOrd

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model
