/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Proto2P/Model.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit I (stage 2 proofs): the model's ghost fields (`nReqs`, `used`) along a replica's run, and
the invariant's budget and key facts derived from them (`reqBudget_of`, `fresh_not_used`).
-/
module

public import Dsverify.Proof.gryff.Proto2P.Ops
import Dsverify.Proof.gryff.PureT.Ghost

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.p2

open model kahn pure

/-- **(Model fact; hub request R-I-1, `notes/hub-requests2.md`; proved by unit A2.)** A step changes the ghost fields
only at a client request: `nReqs` grows by one and `used` gains the request's key. -/
theorem stepR_ghost {k : Fin 3} {s s' : RState} {e : Ev} {o : List Out}
    (h : stepR k s e = .ok (s', o)) :
    s'.nReqs = s.nReqs + (if e.clientReq.isSome then 1 else 0) ∧
      ∀ key ∈ s'.used, key ∈ s.used ∨ ∃ i, e.clientReq = some (key.1, key.2, i) := by
  -- R-I-1: unit A2's `pure.tot.stepR_ghost` (`GryffProof/PureT/Ghost.lean`)
  exact pure.tot.stepR_ghost h

theorem gStep_ok_inv {k : Fin 3} {s s' : RState} {e : Ev} {o : List Out}
    (h : gNet.step k s e = some (s', o)) : stepR k s e = .ok (s', o) := by
  change (stepR k s e).toOption = some (s', o) at h
  revert h
  cases stepR k s e with
  | error _ => intro h; cases h
  | ok r => intro h; cases h; rfl

/-- Along a run: `nReqs` counts the client requests, `used` holds only their keys. -/
theorem runFrom_ghost (k : Fin 3) :
    ∀ (es : List Ev) (s : RState) (s' : RState) (o : List Out),
      runFrom gNet k s es = some (s', o) →
      s'.nReqs = s.nReqs + (es.filter (fun e => e.clientReq.isSome)).length ∧
      ∀ key ∈ s'.used, key ∈ s.used ∨ ∃ e ∈ es, ∃ i, e.clientReq = some (key.1, key.2, i)
  | [], s, s', o, h => by
    simp only [runFrom, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ⟨by simp, fun key hk => Or.inl hk⟩
  | e :: es, s, s', o, h => by
    simp only [runFrom] at h
    rcases hs : gNet.step k s e with _ | ⟨s1, o1⟩
    · rw [hs] at h; cases h
    · rw [hs] at h
      simp only at h
      rcases hr : runFrom gNet k s1 es with _ | ⟨s2, o2⟩
      · rw [hr] at h; cases h
      · rw [hr] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        obtain ⟨h1, h2⟩ := stepR_ghost (gStep_ok_inv hs)
        obtain ⟨h3, h4⟩ := runFrom_ghost k es s1 _ o2 hr
        refine ⟨?_, ?_⟩
        · rw [h3, h1, List.filter_cons]
          cases e.clientReq.isSome <;> simp <;> omega
        · intro key hk
          rcases h4 key hk with hk | ⟨e', he', i, hi⟩
          · rcases h2 key hk with hk | ⟨i, hi⟩
            · exact Or.inl hk
            · exact Or.inr ⟨e, List.mem_cons_self .., i, hi⟩
          · exact Or.inr ⟨e', List.mem_cons_of_mem _ he', i, hi⟩

theorem runP_ghost {k : Fin 3} {es : List Ev} {s : RState} {o : List Out}
    (h : runP gNet k es = some (s, o)) :
    s.nReqs = (es.filter (fun e => e.clientReq.isSome)).length ∧
      ∀ key ∈ s.used, ∃ e ∈ es, ∃ i, e.clientReq = some (key.1, key.2, i) := by
  obtain ⟨h1, h2⟩ := runFrom_ghost k es _ s o h
  have hi1 : (gNet.init k).nReqs = 0 := by show (RState.init k.val).nReqs = 0; rfl
  have hi2 : (gNet.init k).used = [] := by show (RState.init k.val).used = []; rfl
  refine ⟨by rw [h1, hi1, Nat.zero_add], fun key hk => ?_⟩
  rcases h2 key hk with hk | hk
  · rw [hi2] at hk; exact absurd hk (List.not_mem_nil)
  · exact hk

/-! ## Facts derived from the invariant's -/

/-- The ids of a history's operations at replica `r` are distinct (well-behaved clients). -/
theorem ops_ids_nodup {l : List Label} (hwb : WB l) (P : Op → Bool) :
    (((ops l).filter P).map Op.idZ).Nodup := by
  have hp := (ops_pairwise l).filter P
  apply List.pairwise_map.2
  refine List.Pairwise.imp_of_mem ?_ hp
  intro a b ha hb hab heq
  have ha' := (List.mem_filter.1 ha).1
  have hb' := (List.mem_filter.1 hb).1
  unfold Op.idZ at heq
  simp only [Prod.mk.injEq] at heq
  have := hwb.1 a ha' b hb' (sintZ_inj heq.1) (sintZ_inj heq.2)
  omega

/-- A key handled at replica `k` in `l` is an operation of `l` at `k`. -/
theorem used_ops {l : List Label} {k : Fin 3} {key : w32 × w32} {s : RState} {o : List Out}
    (hr : runP gNet k (projR l k) = some (s, o)) (hk : key ∈ s.used) :
    ∃ op ∈ ops l, op.r = k ∧ op.cid = key.1 ∧ op.rid = key.2 := by
  obtain ⟨-, h2⟩ := runP_ghost hr
  obtain ⟨e, he, i, hi⟩ := h2 key hk
  -- the event `e` at replica `k` is some label of `l`
  have : ∀ (n : Nat) (l : List Label), l.length = n → e ∈ projR l k →
      e.clientReq = some (key.1, key.2, i) →
      ∃ op ∈ ops l, op.r = k ∧ op.cid = key.1 ∧ op.rid = key.2 := by
    intro n
    induction n with
    | zero => intro l hl; rw [List.length_eq_zero_iff] at hl; subst hl; intro h; exact absurd h List.not_mem_nil
    | succ n ih =>
      intro l hl hm hc
      have hne : l ≠ [] := by intro e; subst e; cases hl
      obtain ⟨l0, x, rfl⟩ : ∃ l0 x, l = l0 ++ [x] :=
        ⟨_, _, (List.dropLast_concat_getLast hne).symm⟩
      obtain ⟨k', e'⟩ := x
      rw [proj_snoc, List.mem_append] at hm
      rcases hm with hm | hm
      · obtain ⟨op, hop, h⟩ := ih l0 (by simp at hl; omega) hm hc
        exact ⟨op, ops_mono hop, h⟩
      · by_cases hk' : k = k'
        · subst hk'
          simp only [↓reduceIte, List.mem_singleton] at hm
          subst hm
          obtain ⟨op, hop, h1, h2, -, -, h3⟩ := newOp_of_clientReq (l := l0) (k := k) hc
          exact ⟨op, mem_ops_snoc.2 (Or.inr hop), h3, h1, h2⟩
        · simp [hk'] at hm
  exact this _ l rfl he hi

/-- **The budget at a request token's replica** (D14): the replica's handled requests are
distinct registered operations other than the token's, and at most 24 are registered. -/
theorem reqBudget_of {l : List Label} {k : Fin 3} {s : RState} {o : List Out}
    {info : GMap proto.OpId OpInfo} {id : proto.OpId}
    (hr : runP gNet k (projR l k) = some (s, o)) (hwb : WB l)
    (hreg : ∀ op ∈ ops l, (info.lookup op.idZ).isSome)
    (hid : (info.lookup id).isSome) (hfresh : ∀ op ∈ ops l, op.idZ ≠ id)
    (hbud : ∃ unit : proto.OpId → Nat,
      (∀ id, (info.lookup id).isSome → unit id < 24) ∧
      ∀ id1 id2, (info.lookup id1).isSome → (info.lookup id2).isSome → unit id1 = unit id2 →
        id1 = id2) :
    s.nReqs < 24 := by
  obtain ⟨unit, hu1, hu2⟩ := hbud
  obtain ⟨h1, -⟩ := runP_ghost hr
  rw [h1, ← ops_filter_length k _ l rfl]
  let A := ((ops l).filter (fun op => decide (op.r = k))).map Op.idZ
  have hA : A.Nodup := ops_ids_nodup hwb _
  have hL : (id :: A).Nodup := by
    rw [List.nodup_cons]
    refine ⟨?_, hA⟩
    intro hm
    obtain ⟨op, hop, he⟩ := List.mem_map.1 hm
    exact hfresh op (List.mem_filter.1 hop).1 he
  have hreg' : ∀ x ∈ id :: A, (info.lookup x).isSome := by
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hid
    · obtain ⟨op, hop, rfl⟩ := List.mem_map.1 hx
      exact hreg op (List.mem_filter.1 hop).1
  have hU : ((id :: A).map unit).Nodup := by
    apply List.pairwise_map.2
    refine List.Pairwise.imp_of_mem ?_ hL
    intro a b ha hb hab heq
    exact hab (hu2 a b (hreg' a ha) (hreg' b hb) heq)
  have hsub : (id :: A).map unit ⊆ List.range 24 := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact List.mem_range.2 (hu1 y (hreg' y hy))
  have := (List.subperm_of_subset hU hsub).length_le
  simp only [List.length_map, List.length_cons, List.length_range] at this
  have hlen : A.length = ((ops l).filter (fun op => decide (op.r = k))).length := List.length_map ..
  omega

end Perennial.gryff.p2
