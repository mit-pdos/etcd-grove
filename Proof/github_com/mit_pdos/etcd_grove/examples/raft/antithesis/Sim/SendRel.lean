/-
Lean-first (no Rocq counterpart).

# The refinement to Antithesis's binding: the relation after a `send` (#33 S4, the invariant phase)

What `Send` (B 510-593) leaves is the state with the announced write taken back and, for a grant or
an acknowledgement, one more fact in `msgs` and possibly the node's `confirmed` moved (`sendS`).
`send_rel`: under side conditions on the new facts and confirmation (`SendOk`, which `Send.lean`
proves per message type), the relation holds of it, with the message on the network and the
node's unreported messages one fewer.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Logs

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntSim

open AntCheck

/-- What `Send` leaves (and `Step`'s `i`): the announced write taken back, the facts `M`, the
confirmations `C` (B 529, 541, 568-575, 580). -/
def sendS (S : State) (n : Nat) (M : List Fact) (C : List Confirmed) : State :=
  { S with undo := S.undo.set n none, msgs := M, confirmed := C, i := S.i + 1 }

theorem mem_lset_add {α : Type} [DecidableEq α] {s : List α} {x y : α} :
    y ∈ lset.add s x ↔ y ∈ s ∨ y = x := by
  unfold lset.add
  split
  · rename_i h
    have hx : x ∈ s := List.contains_iff_mem.mp h
    exact ⟨.inl, fun h' => h'.elim id (fun e => e ▸ hx)⟩
  · simp

theorem server_has {N : Nat} (j : Fin N) : SSet.has (namesL N) (nameOf (nodeId j)) = true := by
  unfold SSet.has
  rw [List.contains_iff_mem, ← server_get j]
  rw [getElem!_pos (namesL N) j.val (by rw [namesL_length]; exact j.isLt)]
  exact List.getElem_mem _

section rel
variable [GooseExts]

theorem nameOf_ne_nil {R : RunCfg} (j : Fin R.N) : nameOf (nodeId j) ≠ [] := by
  intro h
  exact nodeId_ne_zero j (nameOf_inj (h.trans nameOf_zero.symm))


theorem AckIn.mono {S S' : State} (h : ∀ f ∈ S.msgs, f ∈ S'.msgs) {src dst : Str} {t k : Int}
    (ha : AckIn S src dst t k) : AckIn S' src dst t k := by
  obtain ⟨a, ha, h1⟩ := ha; exact ⟨a, h _ ha, h1⟩

/-- The side conditions of a `send` of `q` at node `n` leaving the facts `M` and the confirmations
`C`: `M` only adds grants and acks of the node to a server, at most at its term, `C` moves only the
node's confirmation, which stays a prefix of its leader log and above the node's acks at its term
(C3), and either stays or moves to the node's term, in `ledLog`, not below it at the same term; the
message is between servers, of a type in scope and a term the node has; what C4 needs of it holds
after. -/
structure SendOk (R : RunCfg) (S : State) (n : Fin R.N) (q : Msg) (M : List Fact) (C : List Confirmed) :
    Prop where
  sub : ∀ f ∈ S.msgs, f ∈ M
  new : ∀ f ∈ M, f ∉ S.msgs → f.type ≠ go!"vote" ∧ f.src = nameOf (nodeId n) ∧
    ∃ j : Fin R.N, f.dst = nameOf (nodeId j)
  clen : C.length = R.N
  cother : ∀ k : Fin R.N, k ≠ n → C[k.val]! = S.confirmed[k.val]!
  conf : ∀ l, S.ledLog.get (C[n.val]!).term = .ok l →
    (C[n.val]!).index ≤ (S.log[n.val]!).length ∧ (C[n.val]!).index ≤ l.length ∧
    (S.log[n.val]!).take (C[n.val]!).index.toNat = l.take (C[n.val]!).index.toNat
  acks : ∀ a ∈ M, a.type = go!"ack" → a.src = nameOf (nodeId n) → a.term = S.currentTerm[n.val]! →
    ((C[n.val]!).term = a.term ∧ a.index ≤ (C[n.val]!).index) ∨ a.index ≤ S.commitIndex[n.val]!
  ty : q.ty = .vote ∨ q.ty = .voteResp ∨ q.ty = .app ∨ q.ty = .appResp ∨ q.ty = .heartbeat ∨
    q.ty = .heartbeatResp ∨ q.ty = .propose ∨ q.ty = .preVote ∨ q.ty = .preVoteResp ∨
    q.ty = .readIndex ∨ q.ty = .readIndexResp
  src : q.ty ≠ .readIndex → q.src = nodeId n ∧ (PreTermKeep q ∨ uint.Z q.term ≤ S.currentTerm[n.val]!)
  /-- a forwarded read request: at term `0`, from its source, a node -/
  fwd : q.ty = .readIndex → q.term = W64 0 ∧ ∃ i : Fin R.N, q.src = nodeId i
  pvo : PreVoterOk R q
  dst : ∃ j : Fin R.N, q.dst = nodeId j
  req : (q.ty = .app ∨ q.ty = .heartbeat) → (toAppendFact (msgOf q q.dst) >>= S.sendable) = .ok true
  vote : q.ty = .vote → ∃ f, voteFact (msgOf q q.dst) = .ok f ∧ f ∈ M
  grant : (q.ty = .voteResp ∧ q.reject = false) →
    ({ type := go!"grant", src := nameOf q.src, dst := nameOf q.dst, term := uint.Z q.term } : Fact) ∈ M
  ack : (q.ty = .appResp ∧ q.reject = false ∧ q.index ≠ W64 0) →
    AckIn (sendS S n.val M C) (nameOf q.src) (nameOf q.dst) (uint.Z q.term) (uint.Z q.index)
  ackt : ∀ a ∈ M, a ∉ S.msgs → a.type = go!"ack" → a.term ≤ S.currentTerm[n.val]!
  cmono : C[n.val]! = S.confirmed[n.val]! ∨
    ((C[n.val]!).term = S.currentTerm[n.val]! ∧ S.ledLog.has (C[n.val]!).term = true ∧
      ((S.confirmed[n.val]!).term = (C[n.val]!).term →
        (S.confirmed[n.val]!).index ≤ (C[n.val]!).index))
  hb : q.ty = .heartbeat → ∀ j : Fin R.N, q.dst = nodeId j → S.currentTerm[j.val]! ≤ uint.Z q.term →
    ((C[j.val]!).term = uint.Z q.term ∧ uint.Z q.commit ≤ (C[j.val]!).index) ∨
      uint.Z q.commit ≤ S.commitIndex[j.val]!
  lcm : (q.ty = .app ∨ q.ty = .heartbeat) → S.role[n.val]! ≠ follower →
    S.currentTerm[n.val]! = uint.Z q.term → uint.Z q.commit ≤ S.commitIndex[n.val]!

/-- A leader's confirmation after a `send` (`SendOk.cmono`: it stays, or moves up at the node's term). -/
theorem SendOk.leaderConf {R : RunCfg} {S : State} {n k : Fin R.N} {q : Msg} {M : List Fact}
    {C : List Confirmed} (hok : SendOk R S n q M C) {v : NodeView}
    (hct : S.currentTerm[k.val]! = uint.Z v.ps.term)
    (h : LeaderConfOk S k v) : LeaderConfOk (sendS S n.val M C) k v := by
  by_cases hk : k = n
  · subst hk
    change (C[k.val]!).term = uint.Z v.ps.term ∧ (v.r.full.length : Int) ≤ (C[k.val]!).index
    rcases hok.cmono with e | ⟨e1, -, e3⟩
    · rw [e]; exact h
    · have ht : (S.confirmed[k.val]!).term = (C[k.val]!).term := h.1.trans (hct.symm.trans e1.symm)
      exact ⟨e1.trans hct, Int.le_trans h.2 (e3 ht)⟩
  · change (C[k.val]!).term = uint.Z v.ps.term ∧ (v.r.full.length : Int) ≤ (C[k.val]!).index
    rw [hok.cother k hk]; exact h

/-- A node's facts after a `send` (its own: one unreported message fewer, the announced write
over), given the announced write's and the sync disk's facts of the new view. -/
theorem NodeOk.send {R : RunCfg} {dec : CCDec} {S : State} {net : List Msg} {k n : Fin R.N}
    {v : NodeView} {M : List Fact} {C : List Confirmed} {q : Msg} (hok : SendOk R S n q M C)
    (h : NodeOk R dec S net k v) (hdt : v.dur.term = v.ps.term) (p : List Msg) (hp : ∀ x ∈ p, x ∈ v.pend) (u : Option DurW) (b : Bool)
    (hu : UndoIs (sendS S n.val M C) k { v with pend := p, undo := u, made := b })
    (hsd : SyncDisk R { v with pend := p, undo := u, made := b }) :
    NodeOk R dec (sendS S n.val M C) (net ++ [q]) k { v with pend := p, undo := u, made := b } := by
  have hsub := hok.sub
  obtain ⟨d1, d2, _, _, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18⟩ := h
  have hack : ∀ {src dst : Str} {t k : Int}, AckIn S src dst t k → AckIn (sendS S n.val M C) src dst t k :=
    fun h => AckIn.mono hsub h
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8⟩ := d8
  refine ⟨d1, d2, hsd, hu, d5, d6, d7, ⟨f1, f2, f3, f4, f5, f6, fun x hx => f7 x (hp x hx), f8⟩, ?_, ?_,
    fun x hx => d11 x (hp x hx), d12, ?_, d14, ?_, d16, d17, d18⟩
  · intro hl
    obtain ⟨l1, l2, l3, l4, l5⟩ := d9 hl
    exact ⟨l1, l2, fun j k h1 h2 => hack (l3 j k h1 h2), fun j hj => (l4 j hj).imp id hack,
      hok.leaderConf (d1.1.trans (by rw [hdt])) l5⟩
  · intro hc
    obtain ⟨c1, c2⟩ := d10 hc
    exact ⟨fun j hj => granted_mono (s1 := sendS S n.val M C) (s := S) k.val rfl rfl hsub rfl (c1 j hj),
      hsub _ c2⟩
  · intro x hx
    obtain ⟨a1, a2, a3, ⟨a4, a5⟩ | a6⟩ := d13 x hx
    · exact ⟨a1, a2, a3, .inl ⟨a4, a5.imp (fun h => ⟨h.1, h.2.1, hack h.2.2⟩) id⟩⟩
    · exact ⟨a1, a2, a3, .inr a6⟩
  · intro m hm
    obtain ⟨h1, h2⟩ := d15 m hm
    exact ⟨List.mem_append_left _ h1, h2⟩

theorem SendOk.tyNet {R : RunCfg} {S : State} {n : Fin R.N} {q : Msg} {M : List Fact} {C : List Confirmed}
    (hok : SendOk R S n q M C) :
    q.ty = .vote ∨ q.ty = .voteResp ∨ q.ty = .app ∨ q.ty = .appResp ∨ q.ty = .heartbeat ∨
      q.ty = .heartbeatResp ∨ q.ty = .propose ∨ q.ty = .preVote ∨ q.ty = .preVoteResp ∨
      q.ty = .readIndex ∨ q.ty = .readIndexResp ∨ q.ty = .snap := by
  rcases hok.ty with h | h | h | h | h | h | h | h | h | h | h <;> simp [h]

/-- **The relation after a `send`**. -/
theorem send_rel {R : RunCfg} {dec : CCDec} {S : State} {V : Fin R.N → NodeView} {net : List Msg}
    {xnet : List XMsg} {G : RaftFacts} {n : Fin R.N} {q : Msg}
    {rest : List Msg} {M : List Fact} {C : List Confirmed}
    (hs : AntSim R dec S V net xnet) (hgo : GlobalOk R S net G) (hpend : (V n).pend = q :: rest)
    (hmf : MsgFacts G q) (hok : SendOk R S n q M C) (hshape : MsgShape q)
    (hdt : ∀ k, (V k).dur.term = (V k).ps.term) :
    AntSim R dec (sendS S n.val M C) (setV V n { V n with pend := rest, undo := none, made := true })
        (net ++ [q]) xnet ∧
      GlobalOk R (sendS S n.val M C) (net ++ [q]) G := by
  obtain ⟨hsh, hb, hn, hxn, hno⟩ := hs
  obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17⟩ := hb
  have hsub := hok.sub
  have hack : ∀ {src dst : Str} {t k : Int}, AckIn S src dst t k → AckIn (sendS S n.val M C) src dst t k :=
    fun h => AckIn.mono hsub h
  have hmask : MsgMask R q := (hno n).facts.pendMask q (by rw [hpend]; exact List.mem_cons_self)
  obtain ⟨sh0, sh1, sh2, sh3, sh4, sh5, sh6, sh7, sh8, sh9, sh10, sh11, sh12, sh13, sh14⟩ := hsh
  refine ⟨⟨⟨sh0, sh1, sh2, sh3, sh4, sh5, sh6, sh7, sh8, sh9, hok.clen, by simpa [sendS] using sh11,
    sh12, sh13, sh14⟩, ?_, ?_, hxn, ?_⟩, ?_⟩
  · -- BindingOk
    refine ⟨hb1, hb2, hb3, hb4, ?_, ?_, hb7, hb8, ?_, hb10, hb11, ?_, hb13, ?_, hb15, hb16, hb17.1,
      hb17.2.1, fun f hf ht => (Classical.em (f ∈ S.msgs)).elim (fun hm => hb17.2.2 f hm ht)
        (fun hm => absurd ht (hok.new f hf hm).1)⟩
    · intro k l hl
      by_cases hk : k = n
      · subst hk; exact hok.conf l hl
      · change S.ledLog.get (C[k.val]!).term = .ok l at hl
        change (C[k.val]!).index ≤ (S.log[k.val]!).length ∧ (C[k.val]!).index ≤ l.length ∧
          (S.log[k.val]!).take (C[k.val]!).index.toNat = l.take (C[k.val]!).index.toNat
        rw [hok.cother k hk] at hl ⊢
        exact hb5 k l hl
    · intro k a ha ht hsa hta
      by_cases hk : k = n
      · subst hk; exact hok.acks a ha ht hsa hta
      · change ((C[k.val]!).term = a.term ∧ a.index ≤ (C[k.val]!).index) ∨ a.index ≤ S.commitIndex[k.val]!
        by_cases hm : a ∈ S.msgs
        · rw [hok.cother k hk]; exact hb6 k a hm ht hsa hta
        · exact absurd (name_inj ((hok.new a ha hm).2.1.symm.trans hsa)).symm hk
    · intro f hf ht
      by_cases hm : f ∈ S.msgs
      · exact hb9 f hm ht
      · obtain ⟨_, h1, j, h2⟩ := hok.new f hf hm
        exact ⟨⟨n, h1⟩, j, h2⟩
    · intro k a ha ht hsa
      by_cases hm : a ∈ S.msgs
      · exact hb12 k a hm ht hsa
      · have hkn : k = n := (name_inj ((hok.new a ha hm).2.1.symm.trans hsa)).symm
        subst hkn; exact hok.ackt a ha hm ht
    · intro k
      by_cases hk : k = n
      · subst hk
        change ((C[k.val]!).index = 0 ∨ S.ledLog.has (C[k.val]!).term = true ∨
          ∀ i : Fin R.N, (C[k.val]!).term < S.currentTerm[i.val]!) ∧ (C[k.val]!).term ≤ S.currentTerm[k.val]!
        rcases hok.cmono with e | ⟨e1, e2, -⟩
        · rw [e]; exact hb14 k
        · exact ⟨.inr (.inl e2), Int.le_of_eq e1⟩
      · change ((C[k.val]!).index = 0 ∨ S.ledLog.has (C[k.val]!).term = true ∨
          ∀ i : Fin R.N, (C[k.val]!).term < S.currentTerm[i.val]!) ∧ (C[k.val]!).term ≤ S.currentTerm[k.val]!
        rw [hok.cother k hk]; exact hb14 k
  · -- NetOk
    refine ⟨fun m hm => ?_, ?_, fun m hm => ?_, fun m hm hty i hsrc hro hct => ?_, fun m hm => ?_,
      fun m hm => ?_⟩
    · rcases List.mem_append.mp hm with hm | hm
      · obtain ⟨hty, hsrc, j, hdst, hj⟩ := hn.1 m hm
        refine ⟨hty, hsrc, j, hdst, fun hle => ?_⟩
        obtain ⟨h1, h2, h3, h4⟩ := hj hle
        refine ⟨h1, fun ht => ?_, fun ht => hsub _ (h3 ht), fun ht => hack (h4 ht)⟩
        obtain ⟨f, hf, hfm⟩ := h2 ht
        exact ⟨f, hf, hsub f hfm⟩
      · rw [List.mem_singleton] at hm
        subst hm
        obtain ⟨j, hj⟩ := hok.dst
        refine ⟨hok.tyNet, ?_, j, hj, fun _ => ⟨hok.req, hok.vote, hok.grant, hok.ack⟩⟩
        by_cases hri : m.ty = .readIndex
        · obtain ⟨h0, i, hi⟩ := hok.fwd hri
          refine ⟨i, hi, .inr ?_⟩
          change uint.Z m.term ≤ S.currentTerm[i.val]!
          rw [h0, (hno i).disk.1]
          have : 0 ≤ uint.Z (V i).dur.term := by word
          simpa using this
        · exact ⟨n, (hok.src hri).1, (hok.src hri).2⟩
    · intro m hm hty j hdst hle
      change ((C[j.val]!).term = uint.Z m.term ∧ uint.Z m.commit ≤ (C[j.val]!).index) ∨
        uint.Z m.commit ≤ S.commitIndex[j.val]!
      rcases List.mem_append.mp hm with hm | hm
      · have hold := hn.2.1 m hm hty j hdst hle
        by_cases hjn : j = n
        · subst hjn
          rcases hok.cmono with e | ⟨e1, -, e3⟩
          · rw [e]; exact hold
          · rcases hold with ⟨o1, o2⟩ | o
            · have hle' := (hb14 j).2
              have hle0 : S.currentTerm[j.val]! ≤ uint.Z m.term := hle
              have ht : (S.confirmed[j.val]!).term = (C[j.val]!).term := by
                rw [e1]; omega
              exact .inl ⟨ht.symm.trans o1, Int.le_trans o2 (e3 ht)⟩
            · exact .inr o
        · rw [hok.cother j hjn]; exact hold
      · rw [List.mem_singleton] at hm
        subst hm
        exact hok.hb hty j hdst hle
    · rcases List.mem_append.mp hm with hm | hm
      · exact hn.2.2.1 m hm
      · rw [List.mem_singleton] at hm; subst hm; exact hshape
    · rcases List.mem_append.mp hm with hm | hm
      · exact hn.2.2.2.1 m hm hty i hsrc hro hct
      · rw [List.mem_singleton] at hm
        subst hm
        have hi : i = n := nodeId_inj (hsrc.symm.trans (hok.src (by rcases hty with h | h <;> rw [h] <;> decide)).1)
        subst hi
        exact hok.lcm hty hro hct
    · rcases List.mem_append.mp hm with hm | hm
      · exact hn.2.2.2.2.1 m hm
      · rw [List.mem_singleton] at hm; subst hm; exact hmask
    · rcases List.mem_append.mp hm with hm | hm
      · exact hn.2.2.2.2.2 m hm
      · rw [List.mem_singleton] at hm; subst hm
        exact hok.pvo
  · -- NodeOk
    intro k
    by_cases hk : k = n
    · subst hk
      simp only [setV, ite_true]
      refine NodeOk.send hok (hno k) (hdt k) rest (fun x hx => by rw [hpend]; exact List.mem_cons_of_mem _ hx)
        none true ⟨?_, ?_⟩ (fun a b c d => ⟨((hno k).sync a b c d).1, ((hno k).sync a b c d).2.1,
          fun h => absurd rfl h⟩)
      · change ((S.undo.set k.val none)[k.val]!).isNone = true ↔ (none : Option DurW) = none
        rw [get!_set_self _ (by rw [sh11]; exact k.isLt)]; simp
      · intro p hp
        change (S.undo.set k.val none)[k.val]! = some p at hp
        rw [get!_set_self _ (by rw [sh11]; exact k.isLt)] at hp; cases hp
    · simp only [setV, hk, ite_false]
      have hne : k.val ≠ n.val := fun h => hk (Fin.ext h)
      have hu : UndoIs (sendS S n.val M C) k (V k) := by
        unfold UndoIs
        rw [show (sendS S n.val M C).undo[k.val]! = S.undo[k.val]! from get!_set_ne _ _ hne]
        exact (hno k).undo
      exact NodeOk.send (v := V k) hok (hno k) (hdt k) (V k).pend (fun x hx => hx) (V k).undo (V k).made hu
        (hno k).sync
  · -- GlobalOk
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ := hgo
    refine ⟨g1, g2, g3, g4, g5, g6, fun m hm ht => ?_, g8, g9⟩
    rcases List.mem_append.mp hm with hm | hm
    · exact g7 m hm ht
    · rw [List.mem_singleton] at hm; subst hm; exact hmf.1 ht

end rel

end AntSim
end EtcdGrove
end Perennial
