/-
Lean-first (no Rocq counterpart).

# Parity B2: the relation after a leader's write's `OnDisk` (`od_relD`)

A `-parallel` leader's `write` report (B 462-470) runs `OnDisk` on its queued item with the binding's
in-memory variables, which its `mem` already set (`InMemory`: role, leaders, leader logs): at node
`n` the log, commit, confirmation, facts, undo record, `chain`, `termLen` and queue change, at the
node's own term; the role, leaders, leader logs, votes and vote stay (`wrS`). `od_relD`: under side
conditions on the new values (`WriteOk`: `ReadyOk`'s for these fields, the announced write's
confirmation and facts the old ones and the new ones, `MemCommit` kept), the B2 relation and
`GlobalOk` hold at the new state, given the node's own part (#33 parity B2, Sim round 20).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.WriteP

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntSim

open GMap go_etcd_io.raft.v3 AntCheck

section writeRel
variable [GooseExts]

/-- The binding's state after a write at node `n` at its own term (`OnDisk`'s successor with the
role, leaders, leader logs and votes kept, the queue's head popped to `q`, `Step`'s `i`). -/
def wrS (S : State) (n : Nat) (L1 : List Entry) (c : Int) (cf : Confirmed) (M : List Fact) (p : Pre)
    (ch : List Entry) (tl : TermFn Int) (q : List QItem) : State :=
  { S with
    log := S.log.set n L1
    commitIndex := S.commitIndex.set n c
    confirmed := S.confirmed.set n cf
    msgs := M
    undo := S.undo.set n (some p)
    chain := ch
    termLen := tl
    queue := S.queue.set n q
    i := S.i + 1 }

/-- `OnDisk`'s successor at the node's own term, no vote, with the queue popped and `Step`'s `i`. -/
theorem odS_wrS (S : State) (n : Nat) (h : n < S.currentTerm.length) (L1 : List Entry) (c : Int)
    (cf : Confirmed) (M : List Fact) (p : Pre) (ch : List Entry) (tl : TermFn Int) (q : List QItem) :
    { { odS S n (S.currentTerm[n]!) none L1 c S.role cf M S.votes S.leaders S.ledLog p ch tl S.viol with
        queue := S.queue.set n q } with i := S.i + 1 } = wrS S n L1 c cf M p ch tl q := by
  unfold odS wrS
  simp only [set_get!_self h]

/-- **The side conditions of a write** at node `n` (a leader at its term `T`): `ReadyOk`'s for the
log, commit, confirmation, facts, `chain` and `termLen`; the announced write (`pre`) the old disk with
the old confirmation and the new facts; the in-memory commit kept and recorded. -/
structure WriteOk (R : RunCfg) (S : State) (G : RaftFacts) (n : Fin R.N) (L1 : List Entry) (c : Int)
    (cf : Confirmed) (M : List Fact) (p : Pre) (ch : List Entry) (tl : TermFn Int) (q : List QItem) :
    Prop where
  lead : S.role[n.val]! = leader
  lself : { server := nameOf (nodeId n), term := S.currentTerm[n.val]! } ∈ S.leaders
  cge : S.commitIndex[n.val]! ≤ c
  mcSelf : ∃ c', (wrS S n.val L1 c cf M p ch tl q).memCommit n.val = .ok c' ∧
    (termAt L1 c' = S.currentTerm[n.val]! → c' ≤ tlOld tl (S.currentTerm[n.val]!)) ∧
    tlOld tl (S.currentTerm[n.val]!) ≤ c'
  mcGe : ∀ c0, S.memCommit n.val = .ok c0 →
    ∃ c', (wrS S n.val L1 c cf M p ch tl q).memCommit n.val = .ok c' ∧ c0 ≤ c'
  pre : PreOk S n.val L1 p
  pconf : p.confirmed = S.confirmed[n.val]!
  pmsgs : ∀ a, a ∈ p.msgs ↔ a ∈ M ∧ a ∉ S.msgs
  msub : ∀ f ∈ S.msgs, f ∈ M
  mnew : ∀ f ∈ M, f ∉ S.msgs →
    f.type = go!"ack" ∧ f.src = nameOf (nodeId n) ∧ (∃ j : Fin R.N, f.dst = nameOf (nodeId j)) ∧
      f.term = S.currentTerm[n.val]! ∧ ((cf.term = f.term ∧ f.index ≤ cf.index) ∨ f.index ≤ c)
  cmono : cf = S.confirmed[n.val]! ∨
    (cf.term = S.currentTerm[n.val]! ∧ S.ledLog.has cf.term = true ∧
      ((S.confirmed[n.val]!).term = cf.term → (S.confirmed[n.val]!).index ≤ cf.index))
  hconf : ∀ l, S.ledLog.get cf.term = .ok l →
    cf.index ≤ L1.length ∧ cf.index ≤ l.length ∧ L1.take cf.index.toNat = l.take cf.index.toNat
  hchain : S.chain <+: ch
  chainC : c ≤ ch.length ∧ ch.take c.toNat = L1.take c.toNat
  tlLen : ∀ x ∈ tl, x.2 ≤ ch.length
  tlC : c = 0 ∨ ∃ x ∈ tl, x.1 ≤ S.currentTerm[n.val]! ∧ c ≤ x.2
  tlDom : ∀ x ∈ S.termLen, ∃ x' ∈ tl, x'.1 = x.1 ∧ x.2 ≤ x'.2
  tlSort : tl.Pairwise (fun a b => a.1 < b.1)
  tlMono : ∀ T, tlOld S.termLen T ≤ tlOld tl T
  tlNew : ∀ T, tlOld S.termLen T < tlOld tl T → T = S.currentTerm[n.val]! ∧
    ∀ k : Fin R.N, k ≠ n → S.role[k.val]! = leader → S.currentTerm[k.val]! ≠ T
  chainG : ∃ c' ≤ G.committed.length, ch = logOf (G.committed.take c')
  tlG : ∀ x ∈ tl, 0 ≤ x.2 ∧ ∃ y, uint.Z y = x.1 ∧ (y, x.2.toNat) ∈ G.commits
  logG : ∃ l ∈ G.logs, L1 = logOf l

section main
variable {R : RunCfg} {dec : CCDec} {S : State} {V : Fin R.N → NodeView} {net : List Msg}
  {xnet : List XMsg} {G : RaftFacts} {n : Fin R.N} {L1 : List Entry} {c : Int} {cf : Confirmed}
  {M : List Fact} {p : Pre} {ch : List Entry} {tl : TermFn Int} {q : List QItem}

set_option hygiene false in
local notation "S₂" => wrS S n.val L1 c cf M p ch tl q

theorem wr_ne {k : Fin R.N} (hk : k ≠ n) : k.val ≠ n.val := fun e => hk (Fin.ext e)

/-- `EffTerm` only grows: the node's new undo record is at its term. -/
theorem wr_eff (hs : Shape R S) (hok : WriteOk R S G n L1 c cf M p ch tl q) (j : Fin R.N) :
    S.effTerm j.val ≤ (S₂).effTerm j.val := by
  have e : (S₂).effTerm j.val = match (S.undo.set n.val (some p))[j.val]! with
      | none => S.currentTerm[j.val]!
      | some u => imin (S.currentTerm[j.val]!) u.term := rfl
  rw [e]
  by_cases hj : j = n
  · rw [hj, get!_set_self _ (by rw [hs.2.2.2.2.2.2.2.2.2.2.2.1]; exact n.isLt)]
    have h1 := effTerm_le S n.val
    show _ ≤ imin (S.currentTerm[n.val]!) p.term
    rw [hok.pre.2.1]; unfold imin; simp only [Int.le_refl, if_true]
    exact h1
  · rw [get!_set_ne _ _ (wr_ne hj)]
    exact Int.le_refl _

theorem wr_memCommit_o {k : Fin R.N} (hk : k ≠ n) : (S₂).memCommit k.val = S.memCommit k.val := by
  have e : (S₂).memCommit k.val = match ((S.queue.set n.val q)[k.val]!).getLast? with
      | none => pure ((S.commitIndex.set n.val c)[k.val]!)
      | some x => need x.ev.commit := rfl
  rw [e, get!_set_ne _ _ (wr_ne hk), get!_set_ne _ _ (wr_ne hk)]; rfl

theorem wr_shape (hs : Shape R S) : Shape R (S₂) := by
  obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14⟩ := hs
  exact ⟨s0, s1, s2, s3, by show (S.log.set _ _).length = R.N; rw [List.length_set]; exact s4, by show (S.commitIndex.set _ _).length = R.N; rw [List.length_set]; exact s5,
    s6, s7, s8, s9, by show (S.confirmed.set _ _).length = R.N; rw [List.length_set]; exact s10, by show (S.undo.set _ _).length = R.N; rw [List.length_set]; exact s11, s12,
    by show (S.queue.set _ _).length = R.N; rw [List.length_set]; exact s13, s14⟩

theorem wr_global (hgo : GlobalOk R S net G) (hs : Shape R S) (hok : WriteOk R S G n L1 c cf M p ch tl q) :
    GlobalOk R (S₂) net G := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ := hgo
  refine ⟨g1, g2, fun k => ?_, g4, ?_, hok.tlG, g7, g8⟩
  · by_cases hk : k = n
    · subst hk
      show ∃ l ∈ G.logs, (S.log.set k.val L1)[k.val]! = logOf l
      rw [get!_set_self _ (by rw [hs.2.2.2.2.1]; exact k.isLt)]; exact hok.logG
    · show ∃ l ∈ G.logs, (S.log.set n.val L1)[k.val]! = logOf l
      rw [get!_set_ne _ _ (wr_ne hk)]; exact g3 k
  · obtain ⟨c', h1, h2⟩ := hok.chainG; exact ⟨c', h1, h2⟩

theorem wr_log_n (hs : Shape R S) : (S₂).log[n.val]! = L1 :=
  get!_set_self _ (by rw [hs.2.2.2.2.1]; exact n.isLt)
theorem wr_log_o {k : Fin R.N} (hk : k ≠ n) : (S₂).log[k.val]! = S.log[k.val]! := get!_set_ne _ _ (wr_ne hk)
theorem wr_cm_n (hs : Shape R S) : (S₂).commitIndex[n.val]! = c :=
  get!_set_self _ (by rw [hs.2.2.2.2.2.1]; exact n.isLt)
theorem wr_cm_o {k : Fin R.N} (hk : k ≠ n) : (S₂).commitIndex[k.val]! = S.commitIndex[k.val]! :=
  get!_set_ne _ _ (wr_ne hk)
theorem wr_cf_n (hs : Shape R S) : (S₂).confirmed[n.val]! = cf :=
  get!_set_self _ (by rw [hs.2.2.2.2.2.2.2.2.2.2.1]; exact n.isLt)
theorem wr_cf_o {k : Fin R.N} (hk : k ≠ n) : (S₂).confirmed[k.val]! = S.confirmed[k.val]! :=
  get!_set_ne _ _ (wr_ne hk)
theorem wr_undo_n (hs : Shape R S) : (S₂).undo[n.val]! = some p :=
  get!_set_self _ (by rw [hs.2.2.2.2.2.2.2.2.2.2.2.1]; exact n.isLt)
theorem wr_undo_o {k : Fin R.N} (hk : k ≠ n) : (S₂).undo[k.val]! = S.undo[k.val]! :=
  get!_set_ne _ _ (wr_ne hk)

/-- An old fact is not one the write added. -/
theorem wr_old (hok : WriteOk R S G n L1 c cf M p ch tl q) {a : Fact} (ha : a ∈ M) (hp : a ∉ p.msgs) :
    a ∈ S.msgs :=
  Classical.byContradiction fun h => hp ((hok.pmsgs a).mpr ⟨ha, h⟩)

/-- **C3 at the new state.** -/
theorem wr_binding (hs : AntSimD R dec S V net xnet) (hok : WriteOk R S G n L1 c cf M p ch tl q) :
    BindingOkD R dec (S₂) := by
  have hsh := hs.1
  obtain ⟨⟨hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16,
    hb17, hb18⟩, u1, u2, u3⟩ := hs.2.1
  have hcm0 : 0 ≤ S.commitIndex[n.val]! := by
    rw [(hs.2.2.2.2 n).1.2.2.2]; exact uint_Z_nonneg _
  have hl := hok.hchain.length_le
  have hT := hok.pre.2.1
  refine ⟨⟨hb1, hok.tlLen, fun k => ?_, fun k => ?_, fun k l hlg => ?_, fun k a ha ht hsrc hct => ?_, hb7,
    hb8, fun f hf hty => ?_, hb10, hb11, fun k a ha ht hsrc => ?_, hb13, fun j => ?_, ⟨fun T' hT' => ?_,
    fun k hk => ?_⟩, hb16, hok.tlSort, ⟨hb18.1, fun f hf hty => ?_⟩⟩, fun T' hT' => ?_, fun j => ?_,
    fun j u hj hm => ?_⟩
  · -- commits within chain
    by_cases hk : k = n
    · rw [hk, wr_cm_n hsh, wr_log_n hsh]; exact hok.chainC
    · rw [wr_cm_o hk, wr_log_o hk]
      obtain ⟨h1, h2⟩ := hb3 k
      exact ⟨by show S.commitIndex[k.val]! ≤ (ch.length : Int); omega, by
        show ch.take _ = _; rw [rr_take_prefix hok.hchain (by omega), h2]⟩
  · -- commits recorded
    by_cases hk : k = n
    · rw [hk, wr_cm_n hsh]; exact hok.tlC
    · rw [wr_cm_o hk]
      rcases hb4 k with h | ⟨x, hx, h1, h2⟩
      · exact .inl h
      · obtain ⟨x', hx', e1, e2⟩ := hok.tlDom x hx
        exact .inr ⟨x', hx', by show x'.1 ≤ S.currentTerm[k.val]!; omega, by omega⟩
  · -- confirmations prefixes of leader logs
    by_cases hk : k = n
    · rw [hk, wr_cf_n hsh] at hlg ⊢; rw [wr_log_n hsh]; exact hok.hconf l hlg
    · rw [wr_cf_o hk] at hlg ⊢; rw [wr_log_o hk]; exact hb5 k l hlg
  · -- acks at the term
    change a ∈ M at ha
    change a.term = S.currentTerm[k.val]! at hct
    by_cases hn : a ∈ S.msgs
    · by_cases hk : k = n
      · rw [hk, wr_cf_n hsh, wr_cm_n hsh]; rw [hk] at hct hsrc
        rcases hb6 n a hn ht hsrc hct with ⟨h1, h2⟩ | h
        · rcases hok.cmono with he | ⟨e1, -, e3⟩
          · rw [he]; exact .inl ⟨h1, h2⟩
          · exact .inl ⟨by omega, Int.le_trans h2 (e3 (by omega))⟩
        · exact .inr (Int.le_trans h (hok.cge))
      · rw [wr_cf_o hk, wr_cm_o hk]; exact hb6 k a hn ht hsrc hct
    · obtain ⟨-, hs', -, -, h⟩ := hok.mnew a ha hn
      obtain rfl : k = n := name_inj (hsrc.symm.trans hs')
      rw [wr_cf_n hsh, wr_cm_n hsh]; exact h
  · -- facts' endpoints
    change f ∈ M at hf
    by_cases hn : f ∈ S.msgs
    · exact hb9 f hn hty
    · obtain ⟨-, hs', hd, -⟩ := hok.mnew f hf hn
      exact ⟨⟨n, hs'⟩, hd⟩
  · -- AckTermsOk
    change a ∈ M at ha
    by_cases hn : a ∈ S.msgs
    · exact hb12 k a hn ht hsrc
    · obtain ⟨-, hs', -, he, -⟩ := hok.mnew a ha hn
      obtain rfl : k = n := name_inj (hsrc.symm.trans hs')
      show a.term ≤ S.currentTerm[k.val]!; omega
  · -- ConfirmedOk
    by_cases hk : j = n
    · rw [hk, wr_cf_n hsh]
      rcases hok.cmono with he | ⟨e1, e2, -⟩
      · rw [he]; exact hb14 n
      · exact ⟨.inr (.inl e2), by show cf.term ≤ S.currentTerm[n.val]!; omega⟩
    · rw [wr_cf_o hk]; exact hb14 j
  · -- TermLenOkM, the kept terms
    change 0 < tlOld tl T' at hT'
    by_cases hlt : tlOld S.termLen T' < tlOld tl T'
    · obtain ⟨rfl, -⟩ := hok.tlNew T' hlt
      exact .inl ⟨_, hok.lself, rfl⟩
    · exact hb15.1 T' (by have := hok.tlMono T'; omega)
  · -- TermLenOkM, the leaders' commits
    change S.role[k.val]! = leader at hk
    by_cases hkn : k = n
    · rw [hkn, wr_log_n hsh]; exact hok.mcSelf
    · obtain ⟨c0, h0, h1, h2⟩ := hb15.2 k hk
      have heq : tlOld tl (S.currentTerm[k.val]!) = tlOld S.termLen (S.currentTerm[k.val]!) := by
        rcases Int.lt_or_eq_of_le (hok.tlMono (S.currentTerm[k.val]!)) with hlt | h
        · exact absurd rfl ((hok.tlNew _ hlt).2 k hkn hk)
        · exact h.symm
      refine ⟨c0, by rw [wr_memCommit_o hkn]; exact h0, ?_, ?_⟩
      · show termAt ((S₂).log[k.val]!) c0 = S.currentTerm[k.val]! → c0 ≤ tlOld tl (S.currentTerm[k.val]!)
        rw [wr_log_o hkn, heq]; exact h1
      · show tlOld tl (S.currentTerm[k.val]!) ≤ c0; rw [heq]; exact h2
  · -- BootTermOk: the new facts are acks
    change f ∈ M at hf
    by_cases hn : f ∈ S.msgs
    · exact hb18.2 f hn hty
    · obtain ⟨ht', -⟩ := hok.mnew f hf hn
      rw [ht'] at hty; exact absurd hty (by decide)
  · -- UndoBindOk, the kept terms
    change 0 < tlOld tl T' at hT'
    by_cases hlt : tlOld S.termLen T' < tlOld tl T'
    · obtain ⟨rfl, -⟩ := hok.tlNew T' hlt
      exact .inl ⟨_, hok.lself, rfl⟩
    · rcases u1 T' (by have := hok.tlMono T'; omega) with h | h
      · exact .inl h
      · exact .inr fun i => Int.lt_of_lt_of_le (h i) (wr_eff hsh hok i)
  · -- UndoBindOk, the confirmations
    have hmono : ∀ t, (∀ i : Fin R.N, t < S.effTerm i.val) → ∀ i : Fin R.N, t < (S₂).effTerm i.val :=
      fun t h i => Int.lt_of_lt_of_le (h i) (wr_eff hsh hok i)
    by_cases hk : j = n
    · rw [hk, wr_cf_n hsh]
      rcases hok.cmono with he | ⟨-, e2, -⟩
      · rw [he]; exact (u2 n).imp id (Or.imp id (hmono _))
      · exact .inr (.inl e2)
    · rw [wr_cf_o hk]; exact (u2 j).imp id (Or.imp id (hmono _))
  · -- UndoBindOk, the announced writes
    obtain ⟨pm, pt, pvt, -, pc, plog⟩ := hok.pre
    by_cases hk : j = n
    · rw [hk, wr_undo_n hsh] at hj
      obtain rfl := Option.some.inj hj
      obtain ⟨h1, h2⟩ := hb3 n
      refine ⟨by rw [pt]; exact hb18.1 n, by rw [pt, pvt]; exact hb13 n,
        by rw [pt, hok.pconf]; exact (hb14 n).2, by rw [pc]; exact hcm0,
        by show p.commit ≤ (ch.length : Int); rw [pc]; omega, ?_, fun a ha hp ht hsrc => ?_,
        fun a ha hp ht hsrc hte => ?_⟩
      · show ch.take _ = ((((S₂).log[j.val]!).take p.keep.toNat ++ p.suffix)).take _
        rw [hk, wr_log_n hsh, plog, pc, rr_take_prefix hok.hchain (by omega), h2]
      · have ha' := wr_old hok ha hp
        rw [pt]; exact hb12 n a ha' ht (by rw [← hk]; exact hsrc)
      · have ha' := wr_old hok ha hp
        rw [hk] at hsrc
        rw [pt] at hte
        rw [hok.pconf, pc]; exact hb6 n a ha' ht hsrc hte
    · rw [wr_undo_o hk] at hj
      obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8⟩ := u3 j u hj hm
      have hsrcj : ∀ a, a ∈ M → a ∉ S.msgs → a.src = nameOf (nodeId j) → False := fun a ha hn hsrc => by
        obtain ⟨-, hs', -⟩ := hok.mnew a ha hn
        exact hk (name_inj (hsrc.symm.trans hs'))
      refine ⟨v1, v2, v3, v4, show u.commit ≤ (ch.length : Int) by omega, ?_, fun a ha hp ht hsrc => ?_,
        fun a ha hp ht hsrc => ?_⟩
      · show ch.take _ = _
        rw [wr_log_o hk, rr_take_prefix hok.hchain (by omega), v6]
      · by_cases hn : a ∈ S.msgs
        · exact v7 a hn hp ht hsrc
        · exact (hsrcj a ha hn hsrc).elim
      · by_cases hn : a ∈ S.msgs
        · exact v8 a hn hp ht hsrc
        · exact (hsrcj a ha hn hsrc).elim

theorem wr_sendable (hok : WriteOk R S G n L1 c cf M p ch tl q) {x : EvalM AppendFact}
    (h : (x >>= S.sendable) = .ok true) : (x >>= (S₂).sendable) = .ok true := by
  cases x with
  | error e => cases h
  | ok f =>
    exact rr_sendableIn_mono (fun _ h => h) (fun t l h => ⟨[], by rw [List.append_nil]; exact h⟩)
      hok.hchain hok.tlDom h

/-- An old fact is outside the node's new announced write. -/
theorem wr_ackOut (hs : Shape R S) (hok : WriteOk R S G n L1 c cf M p ch tl q) (j : Fin R.N) {a : Fact}
    (ha : a ∈ S.msgs) (h : AckOut S j a) : AckOut (S₂) j a := by
  intro u hu hm
  by_cases hj : j = n
  · rw [hj, wr_undo_n hs] at hu
    obtain rfl := Option.some.inj hu
    exact fun hp => ((hok.pmsgs a).mp hp).2 ha
  · rw [wr_undo_o hj] at hu; exact h u hu hm

theorem wr_ackInD (hs : Shape R S) (hok : WriteOk R S G n L1 c cf M p ch tl q) {j : Fin R.N} {d : Str}
    {t k : Int} (h : AckInD S j d t k) : AckInD (S₂) j d t k := by
  obtain ⟨a, ha, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨a, hok.msub a ha, h1, h2, h3, h4, h5, wr_ackOut hs hok j ha h6⟩

theorem wr_ackInX (hs : Shape R S) (hok : WriteOk R S G n L1 c cf M p ch tl q) {k j : Fin R.N}
    {t i : Int} (h : AckInX S k j t i) : AckInX (S₂) k j t i := by
  obtain ⟨a, ha, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨a, hok.msub a ha, h1, h2, h3, h4, h5, fun hne => wr_ackOut hs hok j ha (h6 hne)⟩

/-- **C4 at the new state.** -/
theorem wr_net (hs : AntSimD R dec S V net xnet) (hok : WriteOk R S G n L1 c cf M p ch tl q) :
    NetOkD R (S₂) net := by
  have hsh := hs.1
  have hb14 := hs.2.1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨n1, n2, n3, n4, n5, n6, n7⟩ := hs.2.2.1
  obtain ⟨-, -, -, -, pc, -⟩ := hok.pre
  refine ⟨fun m hm => ?_, fun m hm hty j hj => ?_, n3, fun m hm hty i hsrc hrole hct => ?_, n5, n6, n7⟩
  · obtain ⟨a1, ⟨i, e1, e2, e3⟩, j, hj, a3⟩ := n1 m hm
    refine ⟨a1, ⟨i, e1, e2.imp id (fun ⟨k, hk⟩ => ⟨k, Int.le_trans hk (wr_eff hsh hok k)⟩), e3⟩, j, hj,
      fun he => ?_⟩
    obtain ⟨b1, b2, b3, b4⟩ := a3 (Int.le_trans (wr_eff hsh hok j) he)
    exact ⟨fun ht => wr_sendable hok (b1 ht), fun ht => by
      obtain ⟨f, hf, hfm⟩ := b2 ht; exact ⟨f, hf, hok.msub f hfm⟩, fun ht => hok.msub _ (b3 ht),
      fun ht i hi => wr_ackInD hsh hok (b4 ht i hi)⟩
  · obtain ⟨h1, h2⟩ := n2 m hm hty j hj
    by_cases hk : j = n
    · rw [hk] at h1 h2 ⊢
      refine ⟨fun hle => ?_, fun u hu hmd hle => ?_⟩
      · rw [wr_cf_n hsh, wr_cm_n hsh]
        rcases h1 hle with ⟨e1, e2⟩ | e
        · rcases hok.cmono with he | ⟨f1, -, f3⟩
          · rw [he]; exact .inl ⟨e1, e2⟩
          · have := (hb14 n).2
            have hle' : S.currentTerm[n.val]! ≤ uint.Z m.term := hle
            exact .inl ⟨by omega, Int.le_trans e2 (f3 (by omega))⟩
        · exact .inr (Int.le_trans e (hok.cge))
      · rw [wr_undo_n hsh] at hu
        obtain rfl := Option.some.inj hu
        rw [hok.pconf, pc]
        exact h1 (by rw [← hok.pre.2.1]; exact hle)
    · rw [wr_cf_o hk, wr_cm_o hk, wr_undo_o hk]; exact ⟨h1, h2⟩
  · by_cases hk : i = n
    · rw [hk] at hrole hct ⊢
      obtain ⟨c0, h0, h1⟩ := n4 m hm hty n (by rw [← hk]; exact hsrc) hrole hct
      obtain ⟨c', h2, h3⟩ := hok.mcGe c0 h0
      exact ⟨c', h2, Int.le_trans h1 h3⟩
    · rw [wr_memCommit_o hk]; exact n4 m hm hty i hsrc hrole hct

theorem wr_xnet (hs : AntSimD R dec S V net xnet) (hok : WriteOk R S G n L1 c cf M p ch tl q) :
    XNetOkD R (S₂) xnet := fun x hx => by
  obtain ⟨i, hi⟩ := hs.2.2.2.1 x hx
  exact ⟨i, Int.le_trans hi (wr_eff hs.1 hok i)⟩

/-- **The other nodes' parts at the new state.** -/
theorem wr_node_other (hs : AntSimD R dec S V net xnet) (hok : WriteOk R S G n L1 c cf M p ch tl q)
    (ha : R.md.async = false) (hbat : R.drv.batch = false) {k : Fin R.N} (hk : k ≠ n) :
    NodeOkD R dec (S₂) net k (V k) := by
  have hsh := hs.1
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, -, d13, d14, d15, d16, d17, d18, d19, d20,
    d21, d22, -, d24, d25, d26⟩ := hs.2.2.2.2 k
  refine ⟨⟨d1.1, d1.2.1, by rw [wr_log_o hk]; exact d1.2.2.1, by rw [wr_cm_o hk]; exact d1.2.2.2⟩, d2, d3,
    ?_, ?_, d6, d7, d8, ?_, ?_, d11, fun h => absurd hbat (by rw [h]; decide), d13, fun x hx => ?_, d15,
    d16, d17, d18, d19, d20, d21, d22, fun h => absurd ha (by rw [h]; decide), d24, ?_, d26⟩
  · unfold UndoIs at d4 ⊢
    rw [wr_undo_o hk, wr_log_o hk]; exact d4
  · unfold QueueIs at d5 ⊢
    show (S.queue.set n.val q)[k.val]! = _
    rw [get!_set_ne _ _ (wr_ne hk)]; exact d5
  · intro hlk
    obtain ⟨l1, l2, l3, l4, l5⟩ := d9 hlk
    refine ⟨l1, l2, fun j i h1 h2 => wr_ackInX hsh hok (l3 j i h1 h2),
      fun j hj => (l4 j hj).imp id (wr_ackInX hsh hok), ?_⟩
    unfold LeaderConfOkD at l5 ⊢
    rw [wr_cf_o hk]; exact l5
  · intro hc
    obtain ⟨c1, c2⟩ := d10 hc
    exact ⟨fun j hj => granted_mono (s1 := S₂) (s := S) k.val rfl rfl hok.msub rfl (c1 j hj),
      fun h => by
        have e : (S₂).voteRequest k.val (S.currentTerm[k.val]!) = S.voteRequest k.val (S.currentTerm[k.val]!) := by
          unfold State.voteRequest State.lastTerm; rw [wr_log_o hk]; rfl
        show (S₂).voteRequest k.val (S.currentTerm[k.val]!) ∈ M
        rw [e]; exact hok.msub _ (c2 h)⟩
  · rcases d14 x hx with ⟨q1, q2, q3, q4⟩ | h
    · refine .inl ⟨q1, q2, q3, ?_⟩
      rcases q4 with ⟨t1, ⟨y1, y2, ⟨a, ha', a1⟩⟩ | y⟩ | y
      · exact .inl ⟨t1, .inl ⟨y1, y2, ⟨a, hok.msub a ha', a1⟩⟩⟩
      · exact .inl ⟨t1, .inr y⟩
      · exact .inr y
    · exact .inr h
  · intro hp
    obtain ⟨m1, m2, m3⟩ := d25 hp
    have hl := hok.hchain.length_le
    have hk' : uint.nat (V k).ps.commit ≤ S.chain.length := by word
    refine ⟨show uint.Z (V k).ps.commit ≤ (ch.length : Int) by omega, ?_, ?_⟩
    · show ch.take _ = _
      rw [rr_take_prefix hok.hchain hk']; exact m2
    · rcases m3 with h | ⟨x, hx, h1, h2⟩
      · exact .inl h
      · obtain ⟨x', hx', e1, e2⟩ := hok.tlDom x hx
        exact .inr ⟨x', hx', by omega, by omega⟩

/-- **The relation after a leader's write** (sync, unbatched): under `WriteOk`, the B2 relation and
`GlobalOk` hold at the binding's state after it, given the node's own part there. -/
theorem od_relD (hs : AntSimD R dec S V net xnet) (hgo : GlobalOk R S net G)
    (hok : WriteOk R S G n L1 c cf M p ch tl q) (ha : R.md.async = false) (hbat : R.drv.batch = false)
    {w : NodeView} (hw : NodeOkD R dec (S₂) net n w) :
    AntSimD R dec (S₂) (setV V n w) net xnet ∧ GlobalOk R (S₂) net G := by
  refine ⟨⟨wr_shape hs.1, wr_binding hs hok, wr_net hs hok, wr_xnet hs hok, fun k => ?_⟩,
    wr_global hgo hs.1 hok⟩
  by_cases hk : k = n
  · subst hk; rw [show setV V k w k = w by simp [setV]]; exact hw
  · rw [show setV V n w k = V k by simp [setV, hk]]; exact wr_node_other hs hok ha hbat hk

end main

end writeRel

end AntSim
end EtcdGrove
end Perennial
