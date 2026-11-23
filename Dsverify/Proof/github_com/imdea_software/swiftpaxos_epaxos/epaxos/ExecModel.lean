/-
The executor's pure side, over the model: the replica's graph as a `tarjan.Gr`, the relation
between the states before and after executed components (`ExRel`), the facts of the invariant
the executor's code needs (`ExecWf`, from `Inv`), and the sort: `sort.Sort(nodeArray(list))`'s
result is the model's `sccSort` (`sort_eq_sccSort`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.Tarjan
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Inv

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

open tarjan

/-- The replica's graph (edges: `deps`; executed; committed with commands). -/
def gr (σ : RState) : Gr InstId := ⟨σ.depEdge, σ.executed, σ.ready⟩

/-- `σ'` is `σ` with some instances executed (status `EXECUTED`, nothing else changed) and the
store changed: what executing components does. -/
def ExRel (σ σ' : RState) : Prop :=
  (∃ (I : InstId → Option InstRec) (st : w64 → Option (List w8)),
    σ' = { σ with inst := I, store := st }) ∧
  ∀ x, σ'.inst x = σ.inst x ∨
    ∃ w, σ.inst x = some w ∧ σ'.inst x = some { w with status := stEXECUTED }

theorem ExRel.refl (σ : RState) : ExRel σ σ :=
  ⟨⟨σ.inst, σ.store, by cases σ; rfl⟩, fun _ => Or.inl rfl⟩

theorem ExRel.trans {σ1 σ2 σ3 : RState} (h1 : ExRel σ1 σ2) (h2 : ExRel σ2 σ3) : ExRel σ1 σ3 := by
  obtain ⟨⟨I2, s2, e2⟩, h2'⟩ := h1
  obtain ⟨⟨I3, s3, e3⟩, h3'⟩ := h2
  refine ⟨⟨I3, s3, by rw [e3, e2]⟩, fun x => ?_⟩
  rcases h3' x with h | ⟨w, hw, hw'⟩
  · rw [h]; exact h2' x
  · rcases h2' x with h' | ⟨w0, hw0, hw0'⟩
    · exact Or.inr ⟨w, by rw [← h']; exact hw, hw'⟩
    · rw [hw0'] at hw; cases hw
      exact Or.inr ⟨w0, hw0, by rw [hw']⟩

theorem ExRel.deps {σ σ' : RState} (h : ExRel σ σ') (x : InstId) :
    (σ'.inst x).map (·.deps) = (σ.inst x).map (·.deps) := by
  rcases h.2 x with e | ⟨w, hw, hw'⟩
  · rw [e]
  · rw [hw, hw']; rfl

theorem ExRel.depEdge {σ σ' : RState} (h : ExRel σ σ') : σ'.depEdge = σ.depEdge := by
  funext x y
  apply propext
  unfold RState.depEdge
  have hd := h.deps x
  constructor
  · rintro ⟨w, hw, h1, h2⟩
    rcases hx : σ.inst x with _ | w0
    · rw [hw, hx] at hd; cases hd
    · rw [hw, hx] at hd; simp at hd
      exact ⟨w0, rfl, h1, by rw [← hd]; exact h2⟩
  · rintro ⟨w, hw, h1, h2⟩
    rcases hx : σ'.inst x with _ | w0
    · rw [hw, hx] at hd; cases hd
    · rw [hw, hx] at hd; simp at hd
      exact ⟨w0, rfl, h1, by rw [hd]; exact h2⟩

theorem ExRel.executed {σ σ' : RState} (h : ExRel σ σ') {x : InstId} (he : σ.executed x) :
    σ'.executed x := by
  obtain ⟨w, hw, hs⟩ := he
  rcases h.2 x with e | ⟨w', hw', e⟩
  · exact ⟨w, by rw [e, hw], hs⟩
  · exact ⟨_, e, rfl⟩

theorem ExRel.fields {σ σ' : RState} (h : ExRel σ σ') :
    σ'.id = σ.id ∧ σ'.crtInstance = σ.crtInstance ∧ σ'.committedUpTo = σ.committedUpTo ∧
    σ'.execedUpTo = σ.execedUpTo ∧ σ'.conflicts = σ.conflicts ∧
    σ'.maxSeqPerKey = σ.maxSeqPerKey ∧ σ'.maxSeq = σ.maxSeq ∧ σ'.isLeader = σ.isLeader ∧
    σ'.maxRecvBallot = σ.maxRecvBallot ∧ σ'.peerOrder = σ.peerOrder := by
  obtain ⟨⟨I, st, e⟩, -⟩ := h; subst e; simp

theorem ExRel.gE {σ σ' : RState} (h : ExRel σ σ') : (gr σ').E = (gr σ).E := h.depEdge

theorem execCmdAt_fst (σ : RState) (w : InstRec) (idx : Nat) :
    ∃ st, (execCmdAt σ w idx).1 = { σ with store := st } := by
  unfold execCmdAt
  dsimp only
  split
  · exact ⟨σ.store, rfl⟩
  · split
    · exact ⟨_, rfl⟩
    · split
      · exact ⟨_, rfl⟩
      · exact ⟨σ.store, rfl⟩

theorem execCmd_store (st : w64 → Option (List w8)) (c : WCmd) (k : w64) (v : List w8)
    (h : (execCmd st c).1 k = some v) : st k = some v ∨ (c.op = opPUT ∧ k = c.key ∧ v = c.val) := by
  unfold execCmd at h
  split at h
  · simp only [upd] at h; split at h
    · cases h; exact Or.inr ⟨by assumption, by assumption, rfl⟩
    · exact Or.inl h
  · split at h
    · exact Or.inl h
    · split at h <;> exact Or.inl h

theorem ExRel.execCmdAt (σ : RState) (w : InstRec) (idx : Nat) :
    ExRel σ (execCmdAt σ w idx).1 := by
  obtain ⟨st, e⟩ := execCmdAt_fst σ w idx
  rw [e]; exact ⟨⟨σ.inst, st, rfl⟩, fun _ => Or.inl rfl⟩

theorem ExRel.execDone (σ : RState) (x : InstId) : ExRel σ (execDone σ x) := by
  unfold model.execDone
  rcases hx : σ.inst x with _ | w
  · exact ExRel.refl σ
  · refine ⟨⟨_, σ.store, rfl⟩, fun y => ?_⟩
    simp only [RState.setInst, upd]
    split
    · subst_vars; exact Or.inr ⟨w, hx, rfl⟩
    · exact Or.inl rfl

/-! ## What the executor needs of the state -/

/-- The facts of `Inv` the executor's code relies on (no panic, B11; `Execute`'s and
`ReplyProposeTS`'s preconditions). -/
structure ExecWf (σ : RState) : Prop where
  ids : ∀ x w, σ.inst x = some w → x.q < nR ∧ x.i + 1 < MAX_INSTANCE
  deps : ∀ x w, σ.inst x = some w → w.status ≠ stNONE → depsOk w.deps
  exUp : ∀ q < nR, ∀ n : Nat, (n : Int) ≤ zz (σ.execedUpTo q) → σ.executed ⟨q, n⟩
  exLo : ∀ q < nR, -1 ≤ zz (σ.execedUpTo q) ∧ zz (σ.execedUpTo q) + 1 < MAX_INSTANCE
  cmdsOk : ∀ x w, σ.inst x = some w → isCommitted w.status →
    ∀ c ∈ w.cmds.getD [], c.op ≠ opNONE → OpCmdOk c
  props : ∀ x w lb ps, σ.inst x = some w → isCommitted w.status → w.lb = some lb →
    lb.clientProposals = some ps →
    ∀ idx c, (w.cmds.getD [])[idx]? = some c → c.op ≠ opNONE → idx < ps.length
  store : ∀ k v, σ.store k = some v → k.toNat < 2 ∧ v.length < 2 ^ 15

theorem ExecWf.execCmdAt {σ : RState} (h : ExecWf σ) {x : InstId} {w : InstRec}
    (hw : σ.inst x = some w) (hc : isCommitted w.status) (idx : Nat) :
    ExecWf (model.execCmdAt σ w idx).1 := by
  obtain ⟨st, e⟩ := execCmdAt_fst σ w idx
  have hcmd : ∀ c, c = (w.cmds.getD []).getD idx default → c.op = opPUT →
      c.key.toNat < 2 ∧ c.val.length < 2 ^ 15 := by
    intro c hc' hp
    have hmem : c ∈ w.cmds.getD [] := by
      rw [hc']
      rcases hl : (w.cmds.getD [])[idx]? with _ | c'
      · exfalso; rw [hc'] at hp; simp [List.getD, hl] at hp; revert hp; decide
      · simp [List.getD, hl]; exact List.mem_of_getElem? hl
    have hok := h.cmdsOk x w hw hc c hmem (by rw [hp]; decide)
    refine ⟨hok.1, ?_⟩
    rcases hok.2 with ⟨h1, -⟩ | ⟨-, -, h2⟩ | ⟨h1, -⟩
    · rw [hp] at h1; exact absurd h1 (by decide)
    · exact h2
    · rw [hp] at h1; exact absurd h1 (by decide)
  have hst : ∀ k v, (model.execCmdAt σ w idx).1.store k = some v →
      k.toNat < 2 ∧ v.length < 2 ^ 15 := by
    intro k v hk
    unfold model.execCmdAt at hk
    dsimp only at hk
    split at hk
    · exact h.store k v hk
    · split at hk
      · rcases execCmd_store _ _ _ _ hk with h1 | ⟨h1, h2, h3⟩
        · exact h.store k v h1
        · rw [h2, h3]; exact hcmd _ rfl h1
      · split at hk
        · rcases execCmd_store _ _ _ _ hk with h1 | ⟨h1, h2, h3⟩
          · exact h.store k v h1
          · rw [h2, h3]; exact hcmd _ rfl h1
        · exact h.store k v hk
  rw [e] at hst ⊢
  exact ⟨h.ids, h.deps, h.exUp, h.exLo, h.cmdsOk, h.props, hst⟩

theorem ExecWf.execDone {σ : RState} (h : ExecWf σ) {x : InstId} {w : InstRec}
    (hw : σ.inst x = some w) (hc : isCommitted w.status) : ExecWf (model.execDone σ x) := by
  have hR := ExRel.execDone σ x
  have hinst : ∀ y w', (model.execDone σ x).inst y = some w' →
      ∃ w0, σ.inst y = some w0 ∧ w'.deps = w0.deps ∧ w'.cmds = w0.cmds ∧ w'.lb = w0.lb ∧
        (isCommitted w0.status → isCommitted w'.status) ∧ (w0.status ≠ stNONE → w'.status ≠ stNONE) ∧
        (w'.status ≠ w0.status → y = x ∧ w'.status = stEXECUTED ∧ isCommitted w0.status) := by
    intro y w' hy
    unfold model.execDone at hy
    rw [hw] at hy
    simp only [RState.setInst, upd] at hy
    split at hy
    · subst_vars; cases hy
      refine ⟨w, hw, rfl, rfl, rfl, fun _ => Or.inr rfl, fun _ => by show stEXECUTED ≠ stNONE; decide,
        fun _ => ⟨rfl, rfl, hc⟩⟩
    · exact ⟨w', hy, rfl, rfl, rfl, id, id, fun h' => absurd rfl h'⟩
  have hfields := hR.fields
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y w' hy; obtain ⟨w0, h0, -⟩ := hinst y w' hy; exact h.ids y w0 h0
  · intro y w' hy hs; obtain ⟨w0, h0, hd, -, -, -, hn, hch⟩ := hinst y w' hy
    rw [hd]; apply h.deps y w0 h0
    intro h0s
    by_cases hc' : w'.status = w0.status
    · exact hs (hc' ▸ h0s)
    · obtain ⟨-, -, hcc⟩ := hch hc'
      rcases hcc with e | e <;> rw [e] at h0s <;> revert h0s <;> decide
  · intro q hq n hn; rw [hfields.2.2.2.1] at hn; exact hR.executed (h.exUp q hq n hn)
  · intro q hq; rw [hfields.2.2.2.1]; exact h.exLo q hq
  · intro y w' hy hc'; obtain ⟨w0, h0, -, hcm, -, -, -, hch⟩ := hinst y w' hy
    rw [hcm]; apply h.cmdsOk y w0 h0
    by_cases hs : w'.status = w0.status
    · exact hs ▸ hc'
    · exact (hch hs).2.2
  · intro y w' lb ps hy hc' hlb hps; obtain ⟨w0, h0, -, hcm, hl, -, -, hch⟩ := hinst y w' hy
    rw [hcm]; apply h.props y w0 lb ps h0 _ (hl ▸ hlb) hps
    by_cases hs : w'.status = w0.status
    · exact hs ▸ hc'
    · exact (hch hs).2.2
  · obtain ⟨⟨I, st, e⟩, -⟩ := hR
    have : (model.execDone σ x).store = σ.store := by
      unfold model.execDone; rw [hw]; rfl
    rw [this]; exact h.store

/-- A SCAN meeting `OpCmdOk` reads at most two keys (S4/S5: key and count below 2). -/
theorem rangeKeys_length_le (c : WCmd) (hok : OpCmdOk c) (hs : c.op = opSCAN) :
    (rangeKeys c).length ≤ 2 := by
  obtain ⟨hk, hc⟩ := hok
  obtain ⟨n, hn, hv⟩ : ∃ n : w64, n.toNat < 2 ∧ c.val = u64Le n := by
    rcases hc with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, h2⟩
    · rw [hs] at h1; exact absurd h1 (by decide)
    · rw [hs] at h1; exact absurd h1 (by decide)
    · exact h2
  have htake : leToU64 (c.val.take 8) = n := by
    rw [hv, List.take_of_length_le (by simp [u64Le_length])]; exact u64Le_to_word n
  unfold rangeKeys
  simp only [htake]
  have hk' : c.key = 0 ∨ c.key = 1 := by bv_omega
  have hn' : n = 0 ∨ n = 1 := by bv_omega
  split
  · simp only [List.length_map, List.length_range]
    rcases hk' with e | e <;> rcases hn' with e' | e' <;> rw [e, e'] <;> decide
  · simp

theorem filterMap_flatten_len (st : w64 → Option (List w8)) (l : List w64)
    (hb : ∀ k v, st k = some v → v.length < 2 ^ 15) :
    ((l.filterMap st).flatten).length ≤ l.length * 32767 := by
  induction l with
  | nil => simp
  | cons k l ih =>
    rw [List.filterMap_cons]
    have e : (k :: l).length * 32767 = l.length * 32767 + 32767 := by
      simp only [List.length_cons]; rw [Nat.succ_mul]
    rw [e]
    rcases hk : st k with _ | v
    · exact Nat.le_trans ih (Nat.le_add_right _ _)
    · simp only [List.flatten_cons, List.length_append]
      have h1 : v.length ≤ 32767 := Nat.le_of_lt_succ (hb k v hk)
      rw [Nat.add_comm (l.length * 32767)]
      exact Nat.add_le_add h1 ih

/-- (stage 2, review T1-3, S5) A command's `Execute` result fits `Value.Marshal`'s 16-bit length:
a GET's value, or a SCAN's concatenation of at most two stored values (keys 0 and 1), each below
`2^15` bytes. -/
theorem ExecWf.execCmd_reply_lt {σ : RState} (h : ExecWf σ) {x : InstId} {w : InstRec}
    (hw : σ.inst x = some w) (hc : isCommitted w.status) (c : WCmd)
    (hcm : c ∈ w.cmds.getD []) (hn : c.op ≠ opNONE) :
    (execCmd σ.store c).2.length < 2 ^ 16 := by
  have hok := h.cmdsOk x w hw hc c hcm hn
  unfold execCmd
  split
  · simp
  · split
    · rcases hv : σ.store c.key with _ | v
      · simp
      · simp only [Option.getD_some]; have := (h.store _ _ hv).2; omega
    · split
      · rename_i hp hg hs
        have hlen := rangeKeys_length_le c hok hs
        have hb := filterMap_flatten_len σ.store (rangeKeys c) (fun k v hk => (h.store k v hk).2)
        simp only at hb ⊢
        have : (rangeKeys c).length * 32767 ≤ 2 * 32767 :=
          Nat.mul_le_mul_right _ hlen
        omega
      · simp

/-! ## The sort -/

/-- `nodeArray.Less` on ids: `(Seq, replica, instance)`, strictly, lexicographically. -/
def keyLt (σ : RState) (a b : InstId) : Prop :=
  let sa := ((σ.inst a).map (·.seq)).getD 0
  let sb := ((σ.inst b).map (·.seq)).getD 0
  zz sa < zz sb ∨ (sa = sb ∧ (a.q < b.q ∨ (a.q = b.q ∧ a.i < b.i)))

theorem zz_inj {a b : w32} (h : zz a = zz b) : a = b := by
  simp only [zz, sint.Z] at h; exact BitVec.toInt_inj.mp h

theorem sccLe_iff (σ : RState) (a b : InstId) : sccLe σ a b = true ↔ ¬ keyLt σ b a := by
  unfold sccLe keyLt
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  generalize ((σ.inst a).map (·.seq)).getD 0 = sa
  generalize ((σ.inst b).map (·.seq)).getD 0 = sb
  have hslt : sa.slt sb = true ↔ zz sa < zz sb := by simp [BitVec.slt, zz, sint.Z]
  rw [hslt]
  constructor
  · rintro (h | ⟨rfl, h⟩)
    · rintro (h' | ⟨e, -⟩)
      · omega
      · rw [e] at h; omega
    · rintro (h' | ⟨-, h'⟩)
      · omega
      · omega
  · intro h
    by_cases h1 : zz sa < zz sb
    · exact Or.inl h1
    · right
      have h2 : zz sa = zz sb := by
        exact Classical.byContradiction fun hne => h (Or.inl (by omega))
      have e := zz_inj h2
      refine ⟨e, ?_⟩
      refine Classical.byContradiction fun hh => ?_
      exact h (Or.inr ⟨e.symm, by omega⟩)

theorem sccLe_trans (σ : RState) (a b c : InstId) (h1 : sccLe σ a b = true)
    (h2 : sccLe σ b c = true) : sccLe σ a c = true := by
  rw [sccLe_iff] at *
  unfold keyLt at *
  intro h
  generalize ((σ.inst a).map (·.seq)).getD 0 = sa at *
  generalize ((σ.inst b).map (·.seq)).getD 0 = sb at *
  generalize ((σ.inst c).map (·.seq)).getD 0 = sc at *
  rcases h with h | ⟨e, h⟩
  · by_cases hb : zz sb < zz sa
    · exact h1 (Or.inl hb)
    · by_cases hb' : zz sc < zz sb
      · exact h2 (Or.inl hb')
      · omega
  · by_cases hb : zz sb < zz sa
    · exact h1 (Or.inl hb)
    · by_cases hb' : zz sa < zz sb
      · exact h2 (Or.inl (by rw [e]; exact hb'))
      · have e2 := zz_inj (show zz sb = zz sa by omega)
        have hh1 : ¬ (b.q < a.q ∨ (b.q = a.q ∧ b.i < a.i)) := fun hh => h1 (Or.inr ⟨e2, hh⟩)
        have hh2 : ¬ (c.q < b.q ∨ (c.q = b.q ∧ c.i < b.i)) :=
          fun hh => h2 (Or.inr ⟨by rw [e, e2], hh⟩)
        omega

theorem sccLe_total (σ : RState) (a b : InstId) : (sccLe σ a b || sccLe σ b a) = true := by
  rw [Bool.or_eq_true, sccLe_iff, sccLe_iff]
  refine Classical.byContradiction fun h => ?_
  simp only [not_or, Classical.not_not] at h
  obtain ⟨h1, h2⟩ := h
  unfold keyLt at h1 h2
  rcases h1 with h1 | ⟨e, h1⟩ <;> rcases h2 with h2 | ⟨e', h2⟩
  · omega
  · rw [e'] at h1; omega
  · rw [e] at h2; omega
  · omega

theorem sccLe_antisymm (σ : RState) (a b : InstId) (h1 : sccLe σ a b = true)
    (h2 : sccLe σ b a = true) : a = b := by
  rw [sccLe_iff] at h1 h2
  unfold keyLt at h1 h2
  generalize ((σ.inst a).map (·.seq)).getD 0 = sa at *
  generalize ((σ.inst b).map (·.seq)).getD 0 = sb at *
  have e := zz_inj (show zz sa = zz sb by
    refine Classical.byContradiction fun hne => ?_
    rcases Int.lt_or_gt_of_ne hne with h | h
    · exact h2 (Or.inl h)
    · exact h1 (Or.inl h))
  have hh1 : ¬ (b.q < a.q ∨ (b.q = a.q ∧ b.i < a.i)) := fun hh => h1 (Or.inr ⟨e.symm, hh⟩)
  have hh2 : ¬ (a.q < b.q ∨ (a.q = b.q ∧ a.i < b.i)) := fun hh => h2 (Or.inr ⟨e, hh⟩)
  obtain ⟨q1, i1⟩ := a; obtain ⟨q2, i2⟩ := b
  simp only [InstId.mk.injEq] at hh1 hh2 ⊢
  omega

theorem eq_of_perm_pairwise {α : Type} {r : α → α → Prop} :
    ∀ {l1 l2 : List α}, l1.Perm l2 → l1.Pairwise r → l2.Pairwise r →
      (∀ a b, r a b → r b a → a = b) → l1 = l2
  | [], l2, hp, _, _, _ => by rw [List.Perm.nil_eq hp]
  | a :: l1, [], hp, _, _, _ => by have := hp.length_eq; simp at this
  | a :: l1, b :: l2, hp, h1, h2, hanti => by
    rw [List.pairwise_cons] at h1 h2
    have hab : a = b := by
      refine Classical.byContradiction fun hne => ?_
      have ha2 : a ∈ l2 := by
        have : a ∈ b :: l2 := hp.subset (by simp)
        rcases List.mem_cons.mp this with e | e
        · exact absurd e hne
        · exact e
      have hb1 : b ∈ l1 := by
        have : b ∈ a :: l1 := hp.symm.subset (by simp)
        rcases List.mem_cons.mp this with e | e
        · exact absurd e.symm hne
        · exact e
      exact hne (hanti a b (h1.1 b hb1) (h2.1 a ha2))
    subst hab
    rw [eq_of_perm_pairwise (List.perm_cons a |>.mp hp) h1.2 h2.2 hanti]

/-- **The sort.** A permutation `ys` of the component in which no element is `keyLt`-below an
earlier one (`sort.Sort`'s result, `nodeArray.Less` on the instances' ids and seqs) is the
model's `sccSort`. -/
theorem sort_eq_sccSort (σ : RState) (C ys : List InstId) (hp : ys.Perm C)
    (hs : ∀ (i j : Nat) (xi xj : InstId), ys[i]? = some xi → ys[j]? = some xj → i < j →
      ¬ keyLt σ xj xi) :
    ys = sccSort σ C := by
  have hys : ys.Pairwise (fun a b => sccLe σ a b = true) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    rw [sccLe_iff]
    exact hs i j _ _ (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem hj) hij
  apply eq_of_perm_pairwise (hp.trans (List.mergeSort_perm C (sccLe σ)).symm) hys
  · exact List.pairwise_mergeSort (sccLe_trans σ) (sccLe_total σ) C
  · exact sccLe_antisymm σ

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model
