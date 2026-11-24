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

theorem nameOf_ne_nil : ∀ j : Fin 3, nameOf (nodeId j) ≠ [] := by
  decide +kernel

theorem server_has : ∀ j : Fin 3, SSet.has (namesL 3) (nameOf (nodeId j)) = true := by
  decide +kernel

section rel
variable [GooseExts]

theorem AckIn.mono {S S' : State} (h : ∀ f ∈ S.msgs, f ∈ S'.msgs) {src dst : Str} {t k : Int}
    (ha : AckIn S src dst t k) : AckIn S' src dst t k := by
  obtain ⟨a, ha, h1⟩ := ha; exact ⟨a, h _ ha, h1⟩

/-- The side conditions of a `send` of `q` at node `n` leaving the facts `M` and the confirmations
`C`: `M` only adds grants and acks of the node to a server, at most at its term, `C` moves only the
node's confirmation, which stays a prefix of its leader log and above the node's acks at its term
(C3), and either stays or moves to the node's term, in `ledLog`, not below it at the same term; the
message is between servers, of a type in scope and a term the node has; what C4 needs of it holds
after. -/
structure SendOk (S : State) (n : Fin 3) (q : Msg) (M : List Fact) (C : List Confirmed) : Prop where
  sub : ∀ f ∈ S.msgs, f ∈ M
  new : ∀ f ∈ M, f ∉ S.msgs → f.type ≠ go!"vote" ∧ f.src = nameOf (nodeId n) ∧
    ∃ j : Fin 3, f.dst = nameOf (nodeId j)
  clen : C.length = 3
  cother : ∀ k : Fin 3, k ≠ n → C[k.val]! = S.confirmed[k.val]!
  conf : ∀ l, S.ledLog.get (C[n.val]!).term = .ok l →
    (C[n.val]!).index ≤ (S.log[n.val]!).length ∧ (C[n.val]!).index ≤ l.length ∧
    (S.log[n.val]!).take (C[n.val]!).index.toNat = l.take (C[n.val]!).index.toNat
  acks : ∀ a ∈ M, a.type = go!"ack" → a.src = nameOf (nodeId n) → a.term = S.currentTerm[n.val]! →
    ((C[n.val]!).term = a.term ∧ a.index ≤ (C[n.val]!).index) ∨ a.index ≤ S.commitIndex[n.val]!
  ty : q.ty = .vote ∨ q.ty = .voteResp ∨ q.ty = .app ∨ q.ty = .appResp ∨ q.ty = .heartbeat ∨
    q.ty = .heartbeatResp ∨ q.ty = .propose
  src : q.src = nodeId n ∧ uint.Z q.term ≤ S.currentTerm[n.val]!
  dst : ∃ j : Fin 3, q.dst = nodeId j
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
  hb : q.ty = .heartbeat → ∀ j : Fin 3, q.dst = nodeId j → S.currentTerm[j.val]! ≤ uint.Z q.term →
    ((C[j.val]!).term = uint.Z q.term ∧ uint.Z q.commit ≤ (C[j.val]!).index) ∨
      uint.Z q.commit ≤ S.commitIndex[j.val]!

/-- A leader's confirmation after a `send` (`SendOk.cmono`: it stays, or moves up at the node's term). -/
theorem SendOk.leaderConf {S : State} {n k : Fin 3} {q : Msg} {M : List Fact} {C : List Confirmed}
    (hok : SendOk S n q M C) {v : NodeView} (hct : S.currentTerm[k.val]! = uint.Z v.ps.term)
    (h : LeaderConfOk S k v) : LeaderConfOk (sendS S n.val M C) k v := by
  by_cases hk : k = n
  · subst hk
    change (C[k.val]!).term = uint.Z v.ps.term ∧ (v.ps.log.length : Int) ≤ (C[k.val]!).index
    rcases hok.cmono with e | ⟨e1, -, e3⟩
    · rw [e]; exact h
    · have ht : (S.confirmed[k.val]!).term = (C[k.val]!).term := h.1.trans (hct.symm.trans e1.symm)
      exact ⟨e1.trans hct, Int.le_trans h.2 (e3 ht)⟩
  · change (C[k.val]!).term = uint.Z v.ps.term ∧ (v.ps.log.length : Int) ≤ (C[k.val]!).index
    rw [hok.cother k hk]; exact h

/-- A node's facts after a `send` (its own: one unreported message fewer). -/
theorem NodeOk.send {S : State} {net : List Msg} {k n : Fin 3} {v : NodeView} {M : List Fact}
    {C : List Confirmed} {q : Msg} (hok : SendOk S n q M C) (h : NodeOk S net k v) (p : List Msg)
    (hp : ∀ x ∈ p, x ∈ v.pend) : NodeOk (sendS S n.val M C) (net ++ [q]) k { v with pend := p } := by
  have hsub := hok.sub
  obtain ⟨hd, hL, hC, hP, hQ, hT, hca, hlo⟩ := h
  have hack : ∀ {src dst : Str} {t k : Int}, AckIn S src dst t k → AckIn (sendS S n.val M C) src dst t k :=
    fun h => AckIn.mono hsub h
  refine ⟨hd, ?_, ?_, fun x hx => hP x (hp x hx), ?_, hT, ?_, hlo⟩
  · intro hl
    obtain ⟨l1, l2, l3, l4, l5⟩ := hL hl
    exact ⟨l1, l2, fun j k h1 h2 => hack (l3 j k h1 h2), fun j hj => (l4 j hj).imp id hack,
      hok.leaderConf hd.1 l5⟩
  · intro hc
    obtain ⟨c1, c2⟩ := hC hc
    exact ⟨fun j hj => granted_mono (s1 := sendS S n.val M C) (s := S) k.val rfl rfl hsub rfl (c1 j hj),
      hsub _ c2⟩
  · intro x hx
    obtain ⟨a1, a2, a3, a4, a5⟩ := hQ x hx
    exact ⟨a1, a2, a3, a4, a5.imp (fun h => ⟨h.1, hack h.2⟩) id⟩
  · intro m hm
    obtain ⟨h1, h2⟩ := hca m hm
    exact ⟨List.mem_append_left _ h1, h2⟩

/-- **The relation after a `send`**. -/
theorem send_rel {S : State} {V : Fin 3 → NodeView} {net : List Msg} {G : RaftFacts} {n : Fin 3} {q : Msg}
    {rest : List Msg} {M : List Fact} {C : List Confirmed}
    (hs : AntSim S V net) (hgo : GlobalOk S net G) (hpend : (V n).pend = q :: rest) (hmf : MsgFacts G q)
    (hok : SendOk S n q M C) (hshape : MsgShape q) :
    AntSim (sendS S n.val M C) (setV V n { V n with pend := rest }) (net ++ [q]) ∧
      GlobalOk (sendS S n.val M C) (net ++ [q]) G := by
  obtain ⟨hsh, hb, hn, hno⟩ := hs
  obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16⟩ := hb
  have hsub := hok.sub
  have hack : ∀ {src dst : Str} {t k : Int}, AckIn S src dst t k → AckIn (sendS S n.val M C) src dst t k :=
    fun h => AckIn.mono hsub h
  obtain ⟨sh0, sh1, sh2, sh3, sh4, sh5, sh6, sh7, sh8, sh9, sh10, sh11, sh12, sh13, sh14⟩ := hsh
  refine ⟨⟨⟨sh0, sh1, sh2, sh3, sh4, sh5, sh6, sh7, sh8, sh9, hok.clen, by simpa [sendS] using sh11,
    sh12, sh13, sh14⟩, ?_, ?_, ?_⟩, ?_⟩
  · -- BindingOk
    refine ⟨hb1, hb2, ?_, hb4, hb5, hb6, ?_, ?_, hb9, hb10, ?_, hb12, hb13, ?_, hb15, ?_⟩
    · intro j p hp
      by_cases hj : j = n
      · subst hj
        change (S.undo.set j.val none)[j.val]! = some p at hp
        rw [get!_set_self _ (by rw [sh11]; exact j.isLt)] at hp; cases hp
      · change (S.undo.set n.val none)[j.val]! = some p at hp
        rw [get!_set_ne _ _ (fun h => hj (Fin.ext h))] at hp
        exact hb3 j p hp
    · intro k l hl
      by_cases hk : k = n
      · subst hk; exact hok.conf l hl
      · change S.ledLog.get (C[k.val]!).term = .ok l at hl
        change (C[k.val]!).index ≤ (S.log[k.val]!).length ∧ (C[k.val]!).index ≤ l.length ∧
          (S.log[k.val]!).take (C[k.val]!).index.toNat = l.take (C[k.val]!).index.toNat
        rw [hok.cother k hk] at hl ⊢
        exact hb7 k l hl
    · intro k a ha ht hsa hta
      by_cases hk : k = n
      · subst hk; exact hok.acks a ha ht hsa hta
      · change ((C[k.val]!).term = a.term ∧ a.index ≤ (C[k.val]!).index) ∨ a.index ≤ S.commitIndex[k.val]!
        by_cases hm : a ∈ S.msgs
        · rw [hok.cother k hk]; exact hb8 k a hm ht hsa hta
        · exact absurd (name_inj ((hok.new a ha hm).2.1.symm.trans hsa)).symm hk
    · intro f hf ht
      by_cases hm : f ∈ S.msgs
      · exact hb11 f hm ht
      · obtain ⟨_, h1, j, h2⟩ := hok.new f hf hm
        exact ⟨⟨n, h1⟩, j, h2⟩
    · intro k a ha ht hsa
      by_cases hm : a ∈ S.msgs
      · exact hb14 k a hm ht hsa
      · have hkn : k = n := (name_inj ((hok.new a ha hm).2.1.symm.trans hsa)).symm
        subst hkn; exact hok.ackt a ha hm ht
    · intro k
      by_cases hk : k = n
      · subst hk
        change ((C[k.val]!).index = 0 ∨ S.ledLog.has (C[k.val]!).term = true ∨
          ∀ i : Fin 3, (C[k.val]!).term < S.currentTerm[i.val]!) ∧ (C[k.val]!).term ≤ S.currentTerm[k.val]!
        rcases hok.cmono with e | ⟨e1, e2, -⟩
        · rw [e]; exact hb16 k
        · exact ⟨.inr (.inl e2), Int.le_of_eq e1⟩
      · change ((C[k.val]!).index = 0 ∨ S.ledLog.has (C[k.val]!).term = true ∨
          ∀ i : Fin 3, (C[k.val]!).term < S.currentTerm[i.val]!) ∧ (C[k.val]!).term ≤ S.currentTerm[k.val]!
        rw [hok.cother k hk]; exact hb16 k
  · -- NetOk
    refine ⟨fun m hm => ?_, ?_, fun m hm => ?_⟩
    rotate_left
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
            · have hle' := (hb16 j).2
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
      · exact hn.2.2 m hm
      · rw [List.mem_singleton] at hm; subst hm; exact hshape
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨hty, hsrc, j, hdst, hj⟩ := hn.1 m hm
      refine ⟨hty, hsrc, j, hdst, fun hle => ?_⟩
      obtain ⟨h1, h2, h3, h4⟩ := hj hle
      refine ⟨h1, fun ht => ?_, fun ht => hsub _ (h3 ht), fun ht => hack (h4 ht)⟩
      obtain ⟨f, hf, hfm⟩ := h2 ht
      exact ⟨f, hf, hsub f hfm⟩
    · rw [List.mem_singleton] at hm
      subst hm
      obtain ⟨j, hj⟩ := hok.dst
      exact ⟨hok.ty, ⟨n, hok.src⟩, j, hj, fun _ => ⟨hok.req, hok.vote, hok.grant, hok.ack⟩⟩
  · -- NodeOk
    intro k
    by_cases hk : k = n
    · subst hk
      simp only [setV, ite_true]
      exact NodeOk.send hok (hno k) rest (fun x hx => by rw [hpend]; exact List.mem_cons_of_mem _ hx)
    · simp only [setV, hk, ite_false]
      exact NodeOk.send (v := V k) hok (hno k) (V k).pend (fun x hx => hx)
  · -- GlobalOk
    obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := hgo
    refine ⟨g1, g2, g3, g4, g5, g6, fun m hm ht => ?_⟩
    rcases List.mem_append.mp hm with hm | hm
    · exact g7 m hm ht
    · rw [List.mem_singleton] at hm; subst hm; exact hmf.1 ht

end rel

end AntSim
end EtcdGrove
end Perennial
