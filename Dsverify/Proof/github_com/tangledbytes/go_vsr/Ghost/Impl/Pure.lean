/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Ghost/Impl/Pure.lean (lab master 915f964; notes/dsv-vr.md).

The ghost layer's implementation, pure part: countability of the model's types (the ghost maps'
keys and values), and the pure lemmas on the linearized log the ghost laws use (reply strings are
stable as the log grows, the store's values are non-empty, the key-value model's step, the status
of a registered request).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Model.Basic
public import Perennial.Std.Countable

@[expose] public section

noncomputable section

namespace VsrGhost.Impl

open Perennial VsrModel

abbrev KvInI := KvInput GoString GoString
abbrev KvOutI := KvOutput GoString

/-- `VsrGhost.outOfReply` (restated: the ghost layer's frozen file imports this one). -/
def outOfReplyI : KvInI → GoString → KvOutI
  | .put _ _, _ => .done
  | .get _, res => .got (if res = [] then none else some res)

/-! ## Countability -/

@[reducible] def entryCountable : Pos.Countable Entry :=
  countableOfLeftInverse (fun e : Entry => (e.op, e.cid, e.req)) (fun p => ⟨p.1, p.2.1, p.2.2⟩)
    (fun _ => rfl)

attribute [local instance] entryCountable

@[reducible] def statusCountable : Pos.Countable Status :=
  countableOfLeftInverse
    (fun s : Status => match s with | .normal => (0 : Nat) | .viewChange => 1 | .stateTransfer => 2)
    (fun n => match n with | 0 => .normal | 1 => .viewChange | _ => .stateTransfer)
    (fun s => by cases s <;> rfl)

attribute [local instance] statusCountable

@[reducible] def repCountable : Pos.Countable Rep :=
  countableOfLeftInverse (fun p : Rep => (p.view, p.status, p.log, p.lnv))
    (fun q => ⟨q.1, q.2.1, q.2.2.1, q.2.2.2⟩) (fun _ => rfl)

open GenTree in
def msgTree : Msg → GenTree
  | .request a b c => .node 0 [of a, of b, of c]
  | .reply a b c d => .node 1 [of a, of b, of c, of d]
  | .prepare a b c e d => .node 2 [of a, of b, of c, of e, of d]
  | .prepareOK a b c => .node 3 [of a, of b, of c]
  | .commit a b c => .node 4 [of a, of b, of c]
  | .startViewChange a b => .node 5 [of a, of b]
  | .doViewChange d => .node 6 [of d.view, of d.log, of d.lnv, of d.commit, of d.rid]
  | .startView a b c l d => .node 7 [of a, of b, of c, of l, of d]
  | .getState a b c => .node 8 [of a, of b, of c]
  | .newState a l b c d => .node 9 [of a, of l, of b, of c, of d]
  | .heartbeat => .node 10 []

open GenTree in
def treeMsg : GenTree → Msg
  | .node 0 [a, b, c] => .request (decLeaf a) (decLeaf b) (decLeaf c)
  | .node 1 [a, b, c, d] => .reply (decLeaf a) (decLeaf b) (decLeaf c) (decLeaf d)
  | .node 2 [a, b, c, e, d] => .prepare (decLeaf a) (decLeaf b) (decLeaf c) (decLeaf e) (decLeaf d)
  | .node 3 [a, b, c] => .prepareOK (decLeaf a) (decLeaf b) (decLeaf c)
  | .node 4 [a, b, c] => .commit (decLeaf a) (decLeaf b) (decLeaf c)
  | .node 5 [a, b] => .startViewChange (decLeaf a) (decLeaf b)
  | .node 6 [a, b, c, d, e] =>
      .doViewChange ⟨decLeaf a, decLeaf b, decLeaf c, decLeaf d, decLeaf e⟩
  | .node 7 [a, b, c, l, d] => .startView (decLeaf a) (decLeaf b) (decLeaf c) (decLeaf l) (decLeaf d)
  | .node 8 [a, b, c] => .getState (decLeaf a) (decLeaf b) (decLeaf c)
  | .node 9 [a, l, b, c, d] => .newState (decLeaf a) (decLeaf l) (decLeaf b) (decLeaf c) (decLeaf d)
  | _ => .heartbeat

theorem treeMsg_msgTree (m : Msg) : treeMsg (msgTree m) = m := by
  cases m <;> simp [msgTree, treeMsg]

def factTree : Fact → GenTree
  | .msg m => .node 0 [msgTree m]
  | .committedBy v l => .node 1 [GenTree.of v, GenTree.of l]
  | .linPrefix l => .node 2 [GenTree.of l]
  | .size n => .node 3 [GenTree.of n]

def treeFact : GenTree → Fact
  | .node 0 [t] => .msg (treeMsg t)
  | .node 1 [a, b] => .committedBy (GenTree.decLeaf a) (GenTree.decLeaf b)
  | .node 2 [a] => .linPrefix (GenTree.decLeaf a)
  | .node 3 [a] => .size (GenTree.decLeaf a)
  | _ => .linPrefix []

theorem treeFact_factTree (f : Fact) : treeFact (factTree f) = f := by
  cases f <;> simp [factTree, treeFact, treeMsg_msgTree]

@[reducible] def factCountable : Pos.Countable Fact :=
  countableOfLeftInverse factTree treeFact treeFact_factTree

@[reducible] def factDecEq : DecidableEq Fact := fun a b =>
  letI := factCountable
  decidable_of_iff (Pos.Countable.encode a = Pos.Countable.encode b) Pos.encode_eq_iff

@[reducible] def kvInCountable : Pos.Countable KvInI :=
  countableOfLeftInverse
    (fun i : KvInI => match i with
      | .get k => (Sum.inl k : GoString ⊕ (GoString × GoString))
      | .put k v => .inr (k, v))
    (fun x => match x with | .inl k => .get k | .inr p => .put p.1 p.2)
    (fun i => by cases i <;> rfl)

/-! ## The linearized log -/

theorem outOf_prefix {l1 l2 : List Entry} (h : l1 <+: l2) {i : Nat} (hi : i < l1.length) :
    outOf l2 i = outOf l1 i := by
  obtain ⟨t, rfl⟩ := h
  simp only [outOf, List.getElem?_append_left hi, List.take_append_of_le_length (Nat.le_of_lt hi)]

theorem prefix_getElem? {l1 l2 : List Entry} (h : l1 <+: l2) {i : Nat} {e : Entry}
    (hi : l1[i]? = some e) : l2[i]? = some e := by
  obtain ⟨t, rfl⟩ := h
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hi).1, hi]

theorem storeOf_append (l : List Entry) (e : Entry) :
    storeOf (l ++ [e]) = (handle (storeOf l) e.op).1 := by
  simp [storeOf, List.foldl_append]

theorem handle_encOp_ok (m : Store) (i : KvInI) (hi : InputOk i) :
    handle m (encOp i) = svcStep m i := by
  exact handle_encOp m i (by
    cases i with
    | get k => exact hi.1
    | put k v => exact ⟨hi.1.1, hi.2.2.1⟩)

/-- Every value of the store is non-empty. -/
def StoreOk (m : Store) : Prop := ∀ k v, m k = some v → v ≠ []

theorem storeOk_svcStep (m : Store) (i : KvInI) (hi : InputOk i) (hm : StoreOk m) :
    StoreOk (svcStep m i).1 := by
  cases i with
  | get k => exact hm
  | put k v =>
    intro k' v' h
    simp only [svcStep] at h
    split at h
    · cases h; exact hi.2.1
    · exact hm _ _ h

theorem storeOk_foldl (l : List Entry) (hl : ∀ e ∈ l, ∃ i, InputOk i ∧ e.op = encOp i)
    (m : Store) (hm : StoreOk m) :
    StoreOk (l.foldl (fun m e => (handle m e.op).1) m) := by
  induction l generalizing m with
  | nil => exact hm
  | cons e l ih =>
    simp only [List.foldl_cons]
    apply ih (fun e' he' => hl e' (List.mem_cons_of_mem _ he'))
    obtain ⟨i, hi, hop⟩ := hl e List.mem_cons_self
    rw [hop, handle_encOp_ok m i hi]
    exact storeOk_svcStep m i hi hm

theorem storeOk_inv (s : Sys) (h : Inv s) : StoreOk (absState s) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hreg, hok, -⟩ := h
  apply storeOk_foldl
  · intro e he
    obtain ⟨i, hi, hop⟩ := hreg e he
    exact ⟨i, (hok _ _ _ hi).1, hop⟩
  · intro k v h; cases h

/-- The key-value model's step is the service's, on a store whose values are non-empty. -/
theorem kv_step_svc (σ : Store) (i : KvInI) (hσ : StoreOk σ) :
    kvStep σ i (svcStep σ i).1 (outOfReplyI i (svcStep σ i).2) := by
  cases i with
  | get k =>
    refine ⟨rfl, ?_⟩
    simp only [svcStep, outOfReplyI]
    by_cases hk : σ k = none
    · simp [hk]
    · obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hk
      simp [hv, hσ k v hv]
  | put k v => exact ⟨rfl, rfl⟩

theorem nodupReq_idx {l : List Entry} (h : NoDupReq l) {i j : Nat} {e e' : Entry}
    (hi : l[i]? = some e) (hj : l[j]? = some e') (hc : e.cid = e'.cid) (hr : e.req = e'.req) :
    i = j := by
  have hi' : i < l.length := (List.getElem?_eq_some_iff.mp hi).1
  have hj' : j < l.length := (List.getElem?_eq_some_iff.mp hj).1
  have hei : l[i] = e := (List.getElem?_eq_some_iff.mp hi).2
  have hej : l[j] = e' := (List.getElem?_eq_some_iff.mp hj).2
  exact (List.Nodup.getElem_inj h (hi := by simpa using hi') (hj := by simpa using hj')).mp
    (by simp [hei, hej, hc, hr])

/-- The status of registered request `(c, n)` against the linearized log: pending (not in it), or
done with reply string `r` (its entry's reply). -/
def StatusOk (lin : List Entry) (c n : Nat) : Option GoString → Prop
  | none => ∀ e ∈ lin, ¬ (e.cid = c ∧ e.req = n)
  | some r => ∃ j e, lin[j]? = some e ∧ e.cid = c ∧ e.req = n ∧ outOf lin j = r

theorem statusOk_some_mono {lin lin' : List Entry} (h : lin <+: lin') {c n : Nat} {r : GoString}
    (hs : StatusOk lin c n (some r)) : StatusOk lin' c n (some r) := by
  obtain ⟨j, e, hj, hc, hn, ho⟩ := hs
  have hjl : j < lin.length := (List.getElem?_eq_some_iff.mp hj).1
  refine ⟨j, e, ?_, hc, hn, ?_⟩
  · obtain ⟨t, rfl⟩ := h; rw [List.getElem?_append_left hjl, hj]
  · rw [outOf_prefix h hjl, ho]

theorem statusOk_snoc {lin : List Entry} {e : Entry} {c n : Nat} (hne : ¬ (e.cid = c ∧ e.req = n))
    (st : Option GoString) (hs : StatusOk lin c n st) : StatusOk (lin ++ [e]) c n st := by
  cases st with
  | none =>
    intro e' he'
    rcases List.mem_append.mp he' with h | h
    · exact hs e' h
    · simp at h; subst h; exact hne
  | some r => exact statusOk_some_mono (List.prefix_append _ _) hs

theorem statusOk_new (lin : List Entry) (e : Entry) :
    StatusOk (lin ++ [e]) e.cid e.req (some (outOf (lin ++ [e]) lin.length)) :=
  ⟨lin.length, e, by simp, rfl, rfl, rfl⟩

/-- A reply's validity pins the status: done, with the reply's string. -/
theorem statusOk_reply {lin : List Entry} (hnd : NoDupReq lin) {c n : Nat} {res : GoString}
    (hv : ∃ j e, lin[j]? = some e ∧ e.cid = c ∧ e.req = n ∧ outOf lin j = res)
    (st : Option GoString) (hs : StatusOk lin c n st) : st = some res := by
  obtain ⟨j, e, hj, hc, hn, ho⟩ := hv
  cases st with
  | none =>
    exact absurd ⟨hc, hn⟩ (hs e (List.mem_of_getElem? hj))
  | some r =>
    obtain ⟨j', e', hj', hc', hn', ho'⟩ := hs
    have := nodupReq_idx hnd hj hj' (hc.trans hc'.symm) (hn.trans hn'.symm)
    subst this
    rw [← ho, ← ho']

@[simp] theorem stepRegister_lin (s : Sys) (c n : Nat) (i : KvInI) :
    (stepRegister s c n i).lin = s.lin := rfl

@[simp] theorem stepRegister_reps (s : Sys) (c n : Nat) (i : KvInI) :
    (stepRegister s c n i).reps = s.reps := rfl

theorem stepLin_reg (s : Sys) (l : List Entry) (k : Nat) : (stepLin s l k).reg = s.reg := by
  unfold stepLin; split <;> rfl

theorem stepLin_reps (s : Sys) (l : List Entry) (k : Nat) : (stepLin s l k).reps = s.reps := by
  unfold stepLin; split <;> rfl

theorem stepLin_same (s : Sys) (l : List Entry) (k : Nat) (h : ¬ s.lin.length < k) :
    stepLin s l k = s := by
  unfold stepLin; simp [h]

end VsrGhost.Impl
