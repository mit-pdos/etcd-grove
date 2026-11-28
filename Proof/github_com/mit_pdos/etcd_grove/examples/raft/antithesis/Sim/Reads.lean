/-
Lean-first (no Rocq counterpart).

# The refinement to Antithesis's binding: `readreq` and `read` (#33 parity B1)

`readreq` (`ReadAsked`, B 657-661): the binding appends the context with the chain's length as its
floor, which is within the committed log's length known now (C5: `chain` a prefix of `G.committed`),
keeping the last `MaxReads` (B 660); the view's `reads` (`ReadsIs`) follow it.

`read` (`ReadGiven`, B 663-667): the binding drops every request of the context and finds it stale if
one has a floor above the index; each floor is within the view's (`ReadsIs`), which the premise
bounds by the index. Both lists drop the same requests (their contexts agree, in order).

`ReadsIs` is read through `RRel`, the two lists element by element.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Recv

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Perennial
namespace EtcdGrove
namespace AntSim

open AntCheck

section reads
variable [GooseExts]

/-! ## The reads, element by element -/

/-- The binding's reads and the view's, element by element: the same context, the binding's floor
within the view's. -/
inductive RRel : List ReadRec → List (Str × Nat) → Prop
  | nil : RRel [] []
  | cons {x : ReadRec} {y : Str × Nat} {a : List ReadRec} {b : List (Str × Nat)} :
      x.ctx = y.1 → x.floor ≤ (y.2 : Int) → RRel a b → RRel (x :: a) (y :: b)

theorem RRel.toIs {a : List ReadRec} {b : List (Str × Nat)} (h : RRel a b) :
    a.map (·.ctx) = b.map (·.1) ∧
      ∀ (k : Nat) (x : ReadRec) (y : Str × Nat), a[k]? = some x → b[k]? = some y → x.floor ≤ (y.2 : Int) := by
  induction h with
  | nil => exact ⟨rfl, fun k x y hx _ => by simp at hx⟩
  | cons hc hf _ ih =>
    refine ⟨by simp only [List.map_cons, hc, ih.1], fun k x y hx hy => ?_⟩
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hy
      subst hx; subst hy; exact hf
    | succ k =>
      simp only [List.getElem?_cons_succ] at hx hy
      exact ih.2 k x y hx hy

theorem RRel.ofIs : ∀ {a : List ReadRec} {b : List (Str × Nat)},
    a.map (·.ctx) = b.map (·.1) →
    (∀ (k : Nat) (x : ReadRec) (y : Str × Nat), a[k]? = some x → b[k]? = some y → x.floor ≤ (y.2 : Int)) →
    RRel a b
  | [], [], _, _ => .nil
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | x :: a, y :: b, h1, h2 => by
    simp only [List.map_cons, List.cons.injEq] at h1
    refine .cons h1.1 (h2 0 x y rfl rfl) (RRel.ofIs h1.2 (fun k x' y' hx hy => h2 (k + 1) x' y' ?_ ?_))
    · simpa using hx
    · simpa using hy

theorem ReadsIs.rrel {S : State} {N : Nat} {n : Fin N} {v : NodeView} (h : ReadsIs S n v) :
    RRel (S.reads[n.val]!) v.reads :=
  RRel.ofIs h.1 h.2

theorem RRel.readsIs {S : State} {N : Nat} {n : Fin N} {v : NodeView} (h : RRel (S.reads[n.val]!) v.reads) :
    ReadsIs S n v :=
  h.toIs

theorem RRel.length {a : List ReadRec} {b : List (Str × Nat)} (h : RRel a b) : a.length = b.length := by
  induction h with
  | nil => rfl
  | cons _ _ _ ih => simp [ih]

theorem RRel.append {a : List ReadRec} {b : List (Str × Nat)} (h : RRel a b) {x : ReadRec}
    {y : Str × Nat} (hc : x.ctx = y.1) (hf : x.floor ≤ (y.2 : Int)) : RRel (a ++ [x]) (b ++ [y]) := by
  induction h with
  | nil => exact .cons hc hf .nil
  | cons h1 h2 _ ih => exact .cons h1 h2 ih

theorem RRel.drop1 {a : List ReadRec} {b : List (Str × Nat)} (h : RRel a b) : RRel (a.drop 1) (b.drop 1) := by
  cases h with
  | nil => exact .nil
  | cons _ _ h => simpa using h

theorem RRel.filter {a : List ReadRec} {b : List (Str × Nat)} (h : RRel a b) (c : Str) :
    RRel (a.filter (fun r => r.ctx != c)) (b.filter (fun p => decide (p.1 ≠ c))) := by
  induction h with
  | nil => exact .nil
  | @cons x y _ _ h1 h2 _ ih =>
    by_cases hx : x.ctx = c
    · have hy : y.1 = c := h1 ▸ hx
      simp only [List.filter_cons, hx, hy, bne_self_eq_false, ne_eq, not_true_eq_false, decide_false,
        Bool.false_eq_true, ite_false]
      exact ih
    · have hy : y.1 ≠ c := h1 ▸ hx
      have hb : (x.ctx != c) = true := bne_iff_ne.mpr hx
      simp only [List.filter_cons, hb, hy, ne_eq, not_false_eq_true, decide_true, ite_true]
      exact .cons h1 h2 ih


theorem RRel.trunc {a : List ReadRec} {b : List (Str × Nat)} (h : RRel a b) :
    RRel (readsTrunc a) (readsTrunc b) := by
  unfold readsTrunc
  rw [h.length]
  split
  · exact h.drop1
  · exact h

/-! ## The binding's steps -/

theorem filterM_pure_x {α : Type} (xs : List α) (p : α → Bool) :
    filterM xs (fun x => (Except.ok (p x) : EvalM Bool)) = .ok (xs.filter p) := by
  unfold filterM
  suffices h : ∀ acc : List α, xs.foldlM (fun out x => do if (← (Except.ok (p x) : EvalM Bool)) then pure (out ++ [x]) else pure out) acc = .ok (acc ++ xs.filter p) by simpa using h []
  induction xs with
  | nil => intro acc; simp; rfl
  | cons x xs ih =>
    intro acc
    rw [List.foldlM_cons]
    have e : ((do if (← (Except.ok (p x) : EvalM Bool)) then pure (acc ++ [x]) else pure acc) : EvalM (List α)) =
        .ok (if p x then acc ++ [x] else acc) := by cases p x <;> rfl
    rw [e, eok_bind, ih]
    cases hx : p x <;> simp [List.filter_cons, hx]

theorem anyM_false_x {α : Type} : ∀ (xs : List α) (f : α → EvalM Bool),
    (∀ x ∈ xs, f x = .ok false) → anyM xs f = .ok false
  | [], _, _ => rfl
  | x :: xs, f, h => by
    change (do if (← f x) then pure true else anyM xs f) = _
    rw [h x List.mem_cons_self, eok_bind]
    exact anyM_false_x xs f (fun y hy => h y (List.mem_cons_of_mem _ hy))

/-- What `ReadAsked` leaves (and `Step`'s `i`). -/
def askS (S : State) (n : Nat) (c : Str) : State :=
  { S with reads := S.reads.set n (readsTrunc (S.reads[n]! ++ [{ ctx := c, floor := S.chain.length }])),
           i := S.i + 1 }

/-- What `ReadGiven` leaves, no request stale (and `Step`'s `i`). -/
def givenS (S : State) (n : Nat) (c : Str) : State :=
  { S with reads := S.reads.set n ((S.reads[n]!).filter (fun r => r.ctx != c)), i := S.i + 1 }

theorem readreq_eq {R : RunCfg} {S : State} (n : Fin R.N) (c : Str) (hc : S.cfg = R.cfg) :
    S.step (evReadReq (nodeId n) c) = .ok (some (askS S n.val c)) := by
  unfold State.step
  simp (config := { decide := true }) only [evReadReq, idx_name hc, State.bind, State.readAsked, eok_bind,
    epure, ite_true, ite_false, need, Bool.false_eq_true]
  rfl

theorem read_eq {R : RunCfg} {S : State} (n : Fin R.N) (c : Str) (i : w64) (hc : S.cfg = R.cfg)
    (hst : ∀ r ∈ S.reads[n.val]!, r.ctx = c → r.floor ≤ uint.Z i) :
    S.step (evRead (nodeId n) c i) = .ok (some (givenS S n.val c)) := by
  unfold State.step
  simp (config := { decide := true }) only [evRead, idx_name hc, State.bind, State.readGiven, eok_bind,
    epure, ite_true, ite_false, need, Bool.false_eq_true]
  rw [filterM_pure_x, eok_bind, anyM_false_x]
  · rfl
  · intro r hr
    by_cases hx : r.ctx = c
    · have := hst r hr hx
      simp only [hx, beq_self_eq_true, andM_true]
      exact congrArg Except.ok (decide_eq_false (by omega))
    · have hb : (r.ctx == c) = false := beq_eq_false_iff_ne.mpr hx
      simp only [hb]
      rfl

/-! ## The statements -/

/-- **`readreq`** (B 657-661), for the runs a mask below `mskB1` admits; the view keeps the binding's
last `MaxReads` requests (`readsAsk`). -/
theorem antSim_readreq_in (msk : SimMask) (_hmsk : msk ≤ mskB1) :
    ∀ (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → NodeView) (net : List Msg)
      (xnet : List XMsg) (evs : List AntCheck.Event) (G : RaftFacts) (n : Fin R.N) (ctx : List w8),
      InMask msk R net xnet →
      SimPre R dec S V net xnet evs G → (V n).Idle →
      SimStep R dec evs G (evReadReq (nodeId n) ctx)
        (setV V n { V n with reads := readsAsk (V n).reads (ctx, G.committed.length) }) net xnet := by
  intro R dec S V net xnet evs G n ctx _ ⟨hp, hs, hl, hgo⟩ _
  obtain ⟨S1, hgc, hs1, hgo1⟩ := antSim_gc R dec S V net xnet G hs hl hgo
  obtain ⟨hsh, hb, hn, hxn, hno⟩ := hs1
  have hc : S1.cfg = R.cfg := hsh.1
  have hstep := readreq_eq n ctx hc
  have hch : (S1.chain.length : Int) ≤ (G.committed.length : Int) := by
    obtain ⟨c, hcl, he⟩ := hgo1.2.2.2.2.1
    rw [he]
    have : (logOf (G.committed.take c)).length = (G.committed.take c).length := List.length_map _
    rw [this, List.length_take]; omega
  obtain ⟨sh0, sh1, sh2, sh3, sh4, sh5, sh6, sh7, sh8, sh9, sh10, sh11, sh12, sh13, sh14⟩ := hsh
  have hrel : AntSim R dec (askS S1 n.val ctx)
      (setV V n { V n with reads := readsAsk (V n).reads (ctx, G.committed.length) }) net xnet := by
    refine ⟨⟨sh0, sh1, sh2, sh3, sh4, sh5, sh6, sh7, sh8, sh9, sh10, sh11, sh12, sh13,
      by simpa [askS] using sh14⟩, hb, hn, hxn, fun k => ?_⟩
    obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18⟩ := hno k
    by_cases hk : k = n
    · subst hk
      simp only [setV, ite_true]
      refine ⟨d1, d2, d3, d4, d5, ?_, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18⟩
      apply RRel.readsIs
      change RRel ((S1.reads.set k.val _)[k.val]!) _
      rw [get!_set_self _ (by rw [sh14]; exact k.isLt)]
      exact (d6.rrel.append rfl hch).trunc
    · simp only [setV, hk, ite_false]
      have hne : k.val ≠ n.val := fun h => hk (Fin.ext h)
      refine ⟨d1, d2, d3, d4, d5, ?_, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18⟩
      unfold ReadsIs
      rw [show (askS S1 n.val ctx).reads[k.val]! = S1.reads[k.val]! from get!_set_ne _ _ hne]
      exact d6
  have hgo2 : GlobalOk R (askS S1 n.val ctx) net G := hgo1
  exact ⟨_, Prefix.snoc hp hgc hstep (violated_nil hb.1 hl hgo2), hrel, hgo2⟩

/-- **`read`** (B 663-667), for the runs a mask below `mskB1` admits. -/
theorem antSim_read_in (msk : SimMask) (_hmsk : msk ≤ mskB1) :
    ∀ (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → NodeView) (net : List Msg)
      (xnet : List XMsg) (evs : List AntCheck.Event) (G : RaftFacts) (n : Fin R.N) (rs : ReadStateM)
      (rest : List ReadStateM),
      InMask msk R net xnet →
      SimPre R dec S V net xnet evs G → (V n).rpend = rs :: rest → Told (V n) →
      (∀ f, (rs.RequestCtx', f) ∈ (V n).reads → f ≤ uint.nat rs.Index') →
      SimStep R dec evs G (evRead (nodeId n) rs.RequestCtx' rs.Index')
        (setV V n { V n with rpend := rest,
                             reads := (V n).reads.filter (fun p => decide (p.1 ≠ rs.RequestCtx')) })
        net xnet := by
  intro R dec S V net xnet evs G n rs rest _ ⟨hp, hs, hl, hgo⟩ _ _ hfl
  obtain ⟨S1, hgc, hs1, hgo1⟩ := antSim_gc R dec S V net xnet G hs hl hgo
  obtain ⟨hsh, hb, hn, hxn, hno⟩ := hs1
  have hc : S1.cfg = R.cfg := hsh.1
  have hrr := (hno n).reads.rrel
  have hst : ∀ r ∈ S1.reads[n.val]!, r.ctx = rs.RequestCtx' → r.floor ≤ uint.Z rs.Index' := by
    have key : ∀ (a : List ReadRec) (b : List (Str × Nat)), RRel a b →
        (∀ y ∈ b, y.1 = rs.RequestCtx' → (y.2 : Int) ≤ uint.Z rs.Index') →
        ∀ r ∈ a, r.ctx = rs.RequestCtx' → r.floor ≤ uint.Z rs.Index' := by
      intro a b h
      induction h with
      | nil => intro _ r hr; simp at hr
      | @cons x y _ _ h1 h2 _ ih =>
        intro hy r hr hrc
        rcases List.mem_cons.mp hr with e | hr
        · subst e
          have := hy y List.mem_cons_self (h1 ▸ hrc)
          omega
        · exact ih (fun y' hy' => hy y' (List.mem_cons_of_mem _ hy')) r hr hrc
    refine key _ _ hrr (fun y hy hyc => ?_)
    have hy' : (rs.RequestCtx', y.2) ∈ (V n).reads := by rw [← hyc]; exact hy
    have := hfl y.2 hy'
    have e : ((uint.nat rs.Index' : Nat) : Int) = uint.Z rs.Index' := by word
    omega
  have hstep := read_eq n rs.RequestCtx' rs.Index' hc hst
  obtain ⟨sh0, sh1, sh2, sh3, sh4, sh5, sh6, sh7, sh8, sh9, sh10, sh11, sh12, sh13, sh14⟩ := hsh
  have hrel : AntSim R dec (givenS S1 n.val rs.RequestCtx')
      (setV V n { V n with rpend := rest,
                           reads := (V n).reads.filter (fun p => decide (p.1 ≠ rs.RequestCtx')) }) net xnet := by
    refine ⟨⟨sh0, sh1, sh2, sh3, sh4, sh5, sh6, sh7, sh8, sh9, sh10, sh11, sh12, sh13,
      by simpa [givenS] using sh14⟩, hb, hn, hxn, fun k => ?_⟩
    obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18⟩ := hno k
    by_cases hk : k = n
    · subst hk
      simp only [setV, ite_true]
      refine ⟨d1, d2, d3, d4, d5, ?_, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18⟩
      apply RRel.readsIs
      change RRel ((S1.reads.set k.val _)[k.val]!) _
      rw [get!_set_self _ (by rw [sh14]; exact k.isLt)]
      exact hrr.filter _
    · simp only [setV, hk, ite_false]
      have hne : k.val ≠ n.val := fun h => hk (Fin.ext h)
      refine ⟨d1, d2, d3, d4, d5, ?_, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18⟩
      unfold ReadsIs
      rw [show (givenS S1 n.val rs.RequestCtx').reads[k.val]! = S1.reads[k.val]! from get!_set_ne _ _ hne]
      exact d6
  have hgo2 : GlobalOk R (givenS S1 n.val rs.RequestCtx') net G := hgo1
  exact ⟨_, Prefix.snoc hp hgc hstep (violated_nil hb.1 hl hgo2), hrel, hgo2⟩

end reads

end AntSim
end EtcdGrove
end Perennial
