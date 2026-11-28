/-
Lean-first (no Rocq counterpart).

# Parity B2: the relation after a `-parallel` leader's `mem` (`mem_relD`)

`Mem` (B 450-459) sets the binding's in-memory variables from `InMemory` (`memS`) and queues the
report; the disk variables (term, vote, log, commit, confirmation, facts, votes, undo record) stay.
`mem_relD`: under side conditions on `InMemory`'s result (`MemOk`: the node becomes a leader at its
written term; `leaders`, `ledLog`, `chain`, `termLen` only grow, as `ReadyOk`'s; the queued commit at
least the node's announced one and recorded in its term), the B2 relation and `GlobalOk` hold at the
new state for the other nodes, the binding and the network, given the node's own part (#33 parity B2,
Sim round 12).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.MemCtx

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntSim

open GMap go_etcd_io.raft.v3 AntCheck

section memRel
variable [GooseExts]

/-- The binding's state after a writing `mem` at node `n` (`Mem` with its item queued, `Step`'s `i`). -/
def memQ (S : State) (r : MemResult) (n : Nat) (it : QItem) (i : Int) : State :=
  { memS S r with queue := S.queue.set n (S.queue[n]! ++ [it]), i := i }

/-- The queued commit of the node is its item's (`MemCommit`, B 139). -/
theorem memQ_memCommit_self {S : State} {r : MemResult} {n : Nat} {it : QItem} {i : Int}
    (hn : n < S.queue.length) : (memQ S r n it i).memCommit n = need it.ev.commit := by
  unfold State.memCommit memQ
  simp only [get!_set_self _ hn, List.getLast?_append, List.getLast?_singleton, Option.some_or]

theorem memQ_memCommit_ne {S : State} {r : MemResult} {n k : Nat} {it : QItem} {i : Int} (hk : k ≠ n) :
    (memQ S r n it i).memCommit k = S.memCommit k := by
  unfold State.memCommit memQ
  simp only [get!_set_ne _ _ hk]; rfl

/-- **The side conditions of a `mem`** at node `n` with `InMemory`'s result `r` and queued commit `c`
(`ReadyOk`'s in-memory part): the node a leader at its written term, the leaders, leader logs,
`chain` and `termLen` grown as at a `ready`, the queued commit at least the announced one and
recorded in the term. -/
structure MemOk (R : RunCfg) (dec : CCDec) (S : State) (V : Fin R.N → NodeView) (G : RaftFacts)
    (n : Fin R.N) (r : MemResult) (c : Int) : Prop where
  hrole : r.role = S.role.set n.val leader
  hviol : r.viol = S.viol
  hmem : r.config = S.config ∧ r.confAt = S.confAt
  lsub : ∀ l ∈ S.leaders, l ∈ r.leaders
  lnew : ∀ l ∈ r.leaders, l ∉ S.leaders →
    l = { server := nameOf (nodeId n), term := S.currentTerm[n.val]! } ∧
      ∃ t, (nodeId n, t) ∈ G.leaders ∧ uint.Z t = S.currentTerm[n.val]!
  lself : { server := nameOf (nodeId n), term := S.currentTerm[n.val]! } ∈ r.leaders
  hll : r.ledLog = S.ledLog ∨ ∃ L, r.ledLog = S.ledLog.with (S.currentTerm[n.val]!) L ∧
    (∀ l, S.ledLog.get (S.currentTerm[n.val]!) = .ok l → l <+: L) ∧
    ∃ l ∈ G.logs, L = logOf l ∧ ∃ t l0, uint.Z t = S.currentTerm[n.val]! ∧ (t, l0) ∈ G.camps ∧ l0 <+: l
  llk : ∀ k : Fin R.N, k ≠ n → (V k).ps.role = .leader →
    r.ledLog.get (uint.Z (V k).ps.term) = S.ledLog.get (uint.Z (V k).ps.term)
  lconf : ∀ T, r.ledLog.has T = true → ∃ (l : List EntryM) (a : Nat) (cs : CCState),
    r.ledLog.get T = .ok (logOf l) ∧ r.ledAt.get T = .ok (a : Int) ∧ cfgFold dec R.c0 (l.take a) = some cs ∧
    r.ledConf.get T = .ok (confView R.N cs) ∧ (R.md.confChanges = false → EntsNormal l)
  hchain : S.chain <+: r.chain
  chainG : ∃ c' ≤ G.committed.length, r.chain = logOf (G.committed.take c')
  tlLen : ∀ q ∈ r.termLen, q.2 ≤ r.chain.length
  tlDom : ∀ q ∈ S.termLen, ∃ q' ∈ r.termLen, q'.1 = q.1 ∧ q.2 ≤ q'.2
  tlG : ∀ q ∈ r.termLen, 0 ≤ q.2 ∧ ∃ x, uint.Z x = q.1 ∧ (x, q.2.toNat) ∈ G.commits
  tlSort : r.termLen.Pairwise (fun a b => a.1 < b.1)
  tlMono : ∀ T, tlOld S.termLen T ≤ tlOld r.termLen T
  tlNew : ∀ T, tlOld S.termLen T < tlOld r.termLen T → T = S.currentTerm[n.val]! ∧
    ∀ k : Fin R.N, k ≠ n → S.role[k.val]! = leader → S.currentTerm[k.val]! ≠ T
  tlSelf : (termAt (S.log[n.val]!) c = S.currentTerm[n.val]! → c ≤ tlOld r.termLen (S.currentTerm[n.val]!)) ∧
    tlOld r.termLen (S.currentTerm[n.val]!) ≤ c
  cge : ∀ c0, S.memCommit n.val = .ok c0 → c0 ≤ c
  wasNF : S.role[n.val]! ≠ follower

section main
variable {R : RunCfg} {dec : CCDec} {S : State} {V : Fin R.N → NodeView} {net : List Msg}
  {xnet : List XMsg} {G : RaftFacts} {n : Fin R.N} {r : MemResult} {c : Int} {it : QItem} {i : Int}

theorem mq_role_o {k : Fin R.N} (hok : MemOk R dec S V G n r c) (hk : k ≠ n) :
    (memQ S r n.val it i).role[k.val]! = S.role[k.val]! := by
  show r.role[k.val]! = _
  rw [hok.hrole]; exact get!_set_ne _ _ (fun e => hk (Fin.ext e))

theorem mq_role_n (hok : MemOk R dec S V G n r c) (hn : n.val < S.role.length) :
    (memQ S r n.val it i).role[n.val]! = leader := by
  show r.role[n.val]! = _
  rw [hok.hrole]; exact get!_set_self _ hn

theorem mq_memCommit_o {k : Fin R.N} (hk : k ≠ n) :
    (memQ S r n.val it i).memCommit k.val = S.memCommit k.val :=
  memQ_memCommit_ne (fun e => hk (Fin.ext e))

/-- The leader logs only grow (by extension at the node's term). -/
theorem mq_llext (hok : MemOk R dec S V G n r c) :
    ∀ t l, S.ledLog.get t = .ok l → ∃ e, r.ledLog.get t = .ok (l ++ e) := by
  intro t l h
  rcases hok.hll with heq | ⟨L, heq, hpre, -⟩
  · exact ⟨[], by rw [heq, List.append_nil]; exact h⟩
  · rw [heq]
    by_cases hT : t = S.currentTerm[n.val]!
    · subst hT
      obtain ⟨e, he⟩ := hpre l h
      exact ⟨e, by rw [rr_get_with_self, he]⟩
    · exact ⟨[], by rw [rr_get_with_ne _ _ hT, List.append_nil]; exact h⟩

theorem mq_has (hok : MemOk R dec S V G n r c) {t : Int} (h : S.ledLog.has t = true) :
    r.ledLog.has t = true := by
  obtain ⟨l, hl⟩ := rr_get_of_has h
  obtain ⟨e, he⟩ := mq_llext hok t l hl
  exact TermFn.has_of_get he

theorem mq_sendable (hok : MemOk R dec S V G n r c) {f : AppendFact} (h : S.sendable f = .ok true) :
    (memQ S r n.val it i).sendable f = .ok true :=
  rr_sendableIn_mono hok.lsub (mq_llext hok) hok.hchain hok.tlDom h

theorem mq_take {k : Int} (hok : MemOk R dec S V G n r c) (hk : k ≤ S.chain.length) :
    r.chain.take k.toNat = S.chain.take k.toNat :=
  rr_take_prefix hok.hchain (by omega)

/-- **C3 at the new state.** -/
theorem mq_binding (hs : AntSimD R dec S V net xnet) (hok : MemOk R dec S V G n r c)
    (hit : it.ev.commit = some c) :
    BindingOkD R dec (memQ S r n.val it i) := by
  obtain ⟨⟨sh0, sh1, sh2, sh3, sh4, sh5, sh6, sh7, sh8, sh9, sh10, sh11, sh12, sh13, sh14⟩,
    ⟨hb, hu⟩, -, -, -⟩ := hs
  obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16,
    hb17, hb18⟩ := hb
  have hn6 : n.val < S.role.length := by rw [sh6]; exact n.isLt
  refine ⟨⟨by show r.viol = []; rw [hok.hviol]; exact hb1, hok.tlLen, ?_, ?_, ?_, hb6, ?_, ?_, hb9,
    hb10, hb11, hb12, hb13, ?_, ?_, hok.lconf, hok.tlSort, hb18⟩, ?_⟩
  · -- commits within chain
    intro k
    obtain ⟨h1, h2⟩ := hb3 k
    have hl := hok.hchain.length_le
    refine ⟨show S.commitIndex[k.val]! ≤ (r.chain.length : Int) by omega, ?_⟩
    show r.chain.take (S.commitIndex[k.val]!).toNat = (S.log[k.val]!).take _
    rw [mq_take hok h1, h2]; rfl
  · -- commits recorded
    intro k
    rcases hb4 k with h | ⟨q, hq, h1, h2⟩
    · exact .inl h
    · obtain ⟨q', hq', e1, e2⟩ := hok.tlDom q hq
      exact .inr ⟨q', hq', by show q'.1 ≤ S.currentTerm[k.val]!; omega, by
        show S.commitIndex[k.val]! ≤ q'.2; omega⟩
  · -- confirmations prefixes of leader logs
    intro k l hlg
    change r.ledLog.get (S.confirmed[k.val]!).term = .ok l at hlg
    show (S.confirmed[k.val]!).index ≤ (S.log[k.val]!).length ∧ (S.confirmed[k.val]!).index ≤ l.length ∧
      (S.log[k.val]!).take (S.confirmed[k.val]!).index.toNat = l.take (S.confirmed[k.val]!).index.toNat
    rcases hok.hll with heq | ⟨L, heq, hpre, -⟩
    · rw [heq] at hlg; exact hb5 k l hlg
    · by_cases hT : (S.confirmed[k.val]!).term = S.currentTerm[n.val]!
      · rw [heq, hT, rr_get_with_self] at hlg
        obtain rfl := Except.ok.inj hlg
        rcases (hb14 k).1 with h0 | hhas | hall
        · rw [h0]; simp
        · obtain ⟨l0, hl0⟩ := rr_get_of_has hhas
          have hp0 := hpre l0 (hT ▸ hl0)
          obtain ⟨o1, o2, o3⟩ := hb5 k l0 hl0
          have hlen := hp0.length_le
          exact ⟨o1, by omega, by rw [o3, rr_take_prefix hp0 (by omega)]⟩
        · have := hall n; omega
      · rw [heq, rr_get_with_ne _ _ hT] at hlg; exact hb5 k l hlg
  · -- leader logs of led terms
    intro p hp
    change p ∈ r.ledLog at hp
    have hold : ∀ p ∈ S.ledLog, ∃ l ∈ r.leaders, l.term = p.1 := fun p hp => by
      obtain ⟨l, hl, e⟩ := hb7 p hp; exact ⟨l, hok.lsub l hl, e⟩
    rcases hok.hll with heq | ⟨L, heq, -⟩
    · rw [heq] at hp; exact hold p hp
    · rw [heq] at hp
      rcases rr_mem_with hp with hp | rfl
      · exact hold p hp
      · exact ⟨_, hok.lself, rfl⟩
  · -- leaders' terms and roles
    intro k l hl hsv
    change l ∈ r.leaders at hl
    by_cases hk : k = n
    · subst hk
      have hrn : (memQ S r k.val it i).role[k.val]! ≠ candidate := by
        rw [mq_role_n hok hn6]; decide
      by_cases hm : l ∈ S.leaders
      · exact (hb8 k l hm hsv).imp id (fun h => ⟨h.1, hrn⟩)
      · obtain ⟨rfl, -⟩ := hok.lnew l hl hm
        exact .inr ⟨rfl, hrn⟩
    · rw [mq_role_o hok hk]
      by_cases hm : l ∈ S.leaders
      · exact hb8 k l hm hsv
      · obtain ⟨rfl, -⟩ := hok.lnew l hl hm
        exact absurd (name_inj hsv).symm hk
  · -- ConfirmedOk
    intro k
    obtain ⟨h1, h2⟩ := hb14 k
    exact ⟨h1.imp id (Or.imp (mq_has hok) id), h2⟩
  · -- TermLenOkM
    obtain ⟨t1, t2⟩ := hb15
    refine ⟨fun T hT => ?_, fun k hk => ?_⟩
    · change 0 < tlOld r.termLen T at hT
      by_cases hlt : tlOld S.termLen T < tlOld r.termLen T
      · obtain ⟨rfl, -⟩ := hok.tlNew T hlt
        exact .inl ⟨_, hok.lself, rfl⟩
      · rcases t1 T (by omega) with ⟨l, hl, e⟩ | h
        · exact .inl ⟨l, hok.lsub l hl, e⟩
        · exact .inr h
    · by_cases hkn : k = n
      · subst hkn
        have hn5 : k.val < S.queue.length := by rw [sh13]; exact k.isLt
        refine ⟨c, by rw [memQ_memCommit_self hn5, hit]; rfl, hok.tlSelf⟩
      · rw [mq_role_o hok hkn] at hk
        obtain ⟨c0, h0, h1, h2⟩ := t2 k hk
        have heq : tlOld r.termLen (S.currentTerm[k.val]!) = tlOld S.termLen (S.currentTerm[k.val]!) := by
          rcases Int.lt_or_eq_of_le (hok.tlMono (S.currentTerm[k.val]!)) with hlt | h
          · exact absurd rfl ((hok.tlNew _ hlt).2 k hkn hk)
          · exact h.symm
        exact ⟨c0, by rw [mq_memCommit_o hkn]; exact h0, by
          show termAt (S.log[k.val]!) c0 = S.currentTerm[k.val]! → c0 ≤ tlOld r.termLen (S.currentTerm[k.val]!)
          rw [heq]; exact h1, by show tlOld r.termLen (S.currentTerm[k.val]!) ≤ c0; rw [heq]; exact h2⟩
  · -- UndoBindOk
    obtain ⟨u1, u2, u3⟩ := hu
    refine ⟨fun T hT => ?_, fun j => (u2 j).imp id (Or.imp (mq_has hok) id), fun j u hj hm => ?_⟩
    · change 0 < tlOld r.termLen T at hT
      by_cases hlt : tlOld S.termLen T < tlOld r.termLen T
      · obtain ⟨rfl, -⟩ := hok.tlNew T hlt
        exact .inl ⟨_, hok.lself, rfl⟩
      · rcases u1 T (by omega) with ⟨l, hl, e⟩ | h
        · exact .inl ⟨l, hok.lsub l hl, e⟩
        · exact .inr h
    · obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8⟩ := u3 j u hj hm
      have hl := hok.hchain.length_le
      refine ⟨v1, v2, v3, v4, show u.commit ≤ (r.chain.length : Int) by omega, ?_, v7, v8⟩
      show r.chain.take _ = _
      rw [mq_take hok v5, v6]; rfl

theorem mq_sendable_bind (hok : MemOk R dec S V G n r c) {x : EvalM AppendFact}
    (h : (x >>= S.sendable) = .ok true) : (x >>= (memQ S r n.val it i).sendable) = .ok true := by
  cases x with
  | error e => cases h
  | ok f => exact mq_sendable hok h

/-- **C4 at the new state**: `Sendable` only grows; the node's queued commit is at least its
announced one (`LeadCommitMsgOkD`). -/
theorem mq_net (hs : AntSimD R dec S V net xnet) (hok : MemOk R dec S V G n r c)
    (hit : it.ev.commit = some c) : NetOkD R (memQ S r n.val it i) net := by
  obtain ⟨hsh, -, ⟨n1, n2, n3, n4, n5, n6, n7⟩, -, -⟩ := hs
  refine ⟨fun m hm => ?_, n2, n3, fun m hm hty k hsrc hrole hct => ?_, n5, n6, n7⟩
  · obtain ⟨a1, a2, j, hj, a3⟩ := n1 m hm
    exact ⟨a1, a2, j, hj, fun he => ⟨fun ht => mq_sendable_bind hok ((a3 he).1 ht), (a3 he).2.1,
      (a3 he).2.2.1, (a3 he).2.2.2⟩⟩
  · by_cases hkn : k = n
    · subst hkn
      have hn5 : k.val < S.queue.length := by rw [hsh.2.2.2.2.2.2.2.2.2.2.2.2.2.1]; exact k.isLt
      obtain ⟨c0, h0, h1⟩ := n4 m hm hty k hsrc hok.wasNF hct
      exact ⟨c, by rw [memQ_memCommit_self hn5, hit]; rfl, Int.le_trans h1 (hok.cge c0 h0)⟩
    · rw [mq_role_o hok hkn] at hrole
      rw [mq_memCommit_o hkn]; exact n4 m hm hty k hsrc hrole hct

/-- **The other nodes' parts at the new state.** -/
theorem mq_node_other (hs : AntSimD R dec S V net xnet) (hok : MemOk R dec S V G n r c)
    (ha : R.md.async = false) {k : Fin R.N} (hk : k ≠ n) :
    NodeOkD R dec (memQ S r n.val it i) net k (V k) := by
  have hne : k.val ≠ n.val := fun e => hk (Fin.ext e)
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, hL, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20,
    d21, d22, -, d24, d25⟩ := hs.2.2.2.2 k
  refine ⟨d1, ⟨by rw [mq_role_o hok hk]; exact d2.1, d2.2.1,
      by show r.config[k.val]! = _; rw [hok.hmem.1]; exact d2.2.2.1,
      by show r.confAt[k.val]! = _; rw [hok.hmem.2]; exact d2.2.2.2⟩, d3, d4, ?_, d6, d7, d8, ?_, d10,
    d11, d12, d13, d14, d15, d16, d17, d18, d19, d20, d21, d22, (fun h => by rw [ha] at h; cases h), d24, ?_⟩
  · unfold QueueIs at d5 ⊢
    show (S.queue.set n.val _)[k.val]! = _
    rw [get!_set_ne _ _ hne]; exact d5
  · intro hlk
    obtain ⟨l1, l2, l3, l4, l5⟩ := hL hlk
    exact ⟨List.contains_iff_mem.mpr (hok.lsub _ (List.contains_iff_mem.mp l1)),
      by show r.ledLog.get _ = _; rw [hok.llk k hk hlk]; exact l2, l3, l4, l5⟩
  · intro hp
    obtain ⟨m1, m2, m3⟩ := d25 hp
    have hl := hok.hchain.length_le
    have hk' : uint.nat (V k).ps.commit ≤ S.chain.length := by word
    refine ⟨show uint.Z (V k).ps.commit ≤ (r.chain.length : Int) by omega, ?_, ?_⟩
    · show r.chain.take _ = _
      rw [rr_take_prefix hok.hchain hk']; exact m2
    · rcases m3 with h | ⟨p, hp, h1, h2⟩
      · exact .inl h
      · obtain ⟨q', hq', e1, e2⟩ := hok.tlDom p hp
        exact .inr ⟨q', hq', by omega, by omega⟩

/-- **`GlobalOk` at the new state**: the new leader record and leader log certified. -/
theorem mq_global (hgo : GlobalOk R S net G) (hok : MemOk R dec S V G n r c) :
    GlobalOk R (memQ S r n.val it i) net G := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ := hgo
  refine ⟨fun l hl => ?_, g2, g3, fun q hq => ?_, hok.chainG, hok.tlG, g7, g8⟩
  · change l ∈ r.leaders at hl
    by_cases hm : l ∈ S.leaders
    · exact g1 l hm
    · obtain ⟨rfl, t, ht, he⟩ := hok.lnew l hl hm
      exact .inr ⟨nodeId n, t, ht, rfl, he.symm⟩
  · change q ∈ r.ledLog at hq
    rcases hok.hll with heq | ⟨L, heq, -, l, hl, hL, hcamp⟩
    · rw [heq] at hq; exact g4 q hq
    · rw [heq] at hq
      rcases rr_mem_with hq with hq | rfl
      · exact g4 q hq
      · exact .inr ⟨l, hl, hL, hcamp⟩

theorem mq_shape (hs : Shape R S) (hok : MemOk R dec S V G n r c) : Shape R (memQ S r n.val it i) := by
  obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14⟩ := hs
  refine ⟨s0, s1, s2, s3, s4, s5, ?_, s7, ?_, ?_, s10, s11, s12, ?_, s14⟩
  · show r.role.length = _; rw [hok.hrole, List.length_set]; exact s6
  · show r.config.length = _; rw [hok.hmem.1]; exact s8
  · show r.confAt.length = _; rw [hok.hmem.2]; exact s9
  · show (S.queue.set _ _).length = _; rw [List.length_set]; exact s13

/-- **The relation after a `mem`** (sync): under `MemOk`, the B2 relation and `GlobalOk` hold at the
binding's state after it, given the node's own part there. -/
theorem mem_relD (hs : AntSimD R dec S V net xnet) (hgo : GlobalOk R S net G)
    (hok : MemOk R dec S V G n r c) (hit : it.ev.commit = some c) (ha : R.md.async = false)
    {w : NodeView} (hw : NodeOkD R dec (memQ S r n.val it i) net n w) :
    AntSimD R dec (memQ S r n.val it i) (setV V n w) net xnet ∧ GlobalOk R (memQ S r n.val it i) net G := by
  refine ⟨⟨mq_shape hs.1 hok, mq_binding hs hok hit, mq_net hs hok hit, hs.2.2.2.1, fun k => ?_⟩,
    mq_global hgo hok⟩
  by_cases hk : k = n
  · subst hk; rw [show setV V k w k = w by simp [setV]]; exact hw
  · rw [show setV V n w k = V k by simp [setV, hk]]; exact mq_node_other hs hok ha hk

end main

end memRel

end AntSim
end EtcdGrove
end Perennial
