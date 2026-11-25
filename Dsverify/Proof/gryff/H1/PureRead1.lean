/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H1/PureRead1.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit H1: pure facts for `HandleRead1Reply` (the model's `stepRead1Reply` by phases).
-/
module

public import Dsverify.Proof.gryff.H1.PureStart

@[expose] public section

namespace Perennial.gryff.replica2

open Perennial.gryff.model

/-- A new max tag (`read.maxValTag == nil || vt.T.GreaterThan(read.maxValTag.T)`). -/
def r1New (read : ReadOp) (m : Read1ReplyM) : Bool :=
  match read.maxValTag with
  | none => true
  | some mx => m.vt.t.gt mx.t

/-- The read op after the max-tag update (`numRead1Replies++`, the new max). -/
def r1A (s : RState) (read : ReadOp) (m : Read1ReplyM) : ReadOp :=
  if r1New read m then
    { read with numRead1Replies := read.numRead1Replies + 1, maxValTag := some m.vt,
                readsWithMaxTag := 1, replicasWithMaxTag := [s.id] }
  else { read with numRead1Replies := read.numRead1Replies + 1 }

/-- The state after the max-tag update (the proxy's overwrite). -/
def r1S (s : RState) (read : ReadOp) (m : Read1ReplyM) : RState :=
  if r1New read m then s.overwrite m.vt.v m.vt.t else s

/-- The read op after counting a reply with the max tag. -/
def r1B (s : RState) (read : ReadOp) (m : Read1ReplyM) : ReadOp :=
  if some m.vt.t = (r1A s read m).maxValTag.map (·.t) then
    { r1A s read m with readsWithMaxTag := (r1A s read m).readsWithMaxTag + 1,
                        replicasWithMaxTag := (r1A s read m).replicasWithMaxTag ++ [m.replicaId] }
  else r1A s read m

/-- The read op once its value is determined. -/
def r1C (b : ReadOp) : ReadOp :=
  if !b.determinedReadVal then { b with readValTag := b.maxValTag, determinedReadVal := true } else b

/-- The replicas a Read2 goes to. -/
def r2Reps (c : ReadOp) : List w32 :=
  ([0, 1, 2] : List w32).filter (fun i => !(c.replicasWithMaxTag.contains i))

/-- The state with the read op `r` stored back. -/
def r1Put (s : RState) (read : ReadOp) (m : Read1ReplyM) (r : ReadOp) : RState :=
  { r1S s read m with rops := (r1S s read m).rops.put (shiftInts m.requestId m.clientId) r }

/-- The state with the read op (number `n`) completed. -/
def r1Del (s : RState) (read : ReadOp) (m : Read1ReplyM) (n : w32) : RState :=
  { r1S s read m with ongoingReqs := (r1S s read m).ongoingReqs.del n,
                      rops := (r1S s read m).rops.del (shiftInts m.requestId m.clientId) }

theorem r1B_ne (s : RState) (read : ReadOp) (m : Read1ReplyM) (x : ValTag)
    (h : (r1A s read m).maxValTag = some x) (hn : m.vt.t ≠ x.t) : r1B s read m = r1A s read m := by
  unfold r1B
  rw [h, if_neg]
  intro h'; exact hn (Option.some.inj h')

theorem r1B_eq (s : RState) (read : ReadOp) (m : Read1ReplyM) (x : ValTag)
    (h : (r1A s read m).maxValTag = some x) (he : m.vt.t = x.t) :
    (r1B s read m).readsWithMaxTag = (r1A s read m).readsWithMaxTag + 1 ∧
      (r1B s read m).replicasWithMaxTag = (r1A s read m).replicasWithMaxTag ++ [m.replicaId] := by
  unfold r1B
  rw [h, if_pos (by rw [he]; rfl)]
  exact ⟨rfl, rfl⟩

/-- The fields `r1B` keeps from `r1A`. -/
theorem r1B_same (s : RState) (read : ReadOp) (m : Read1ReplyM) :
    (r1B s read m).requestId = (r1A s read m).requestId ∧
    (r1B s read m).clientId = (r1A s read m).clientId ∧ (r1B s read m).n = (r1A s read m).n ∧
    (r1B s read m).maxValTag = (r1A s read m).maxValTag ∧
    (r1B s read m).readValTag = (r1A s read m).readValTag ∧
    (r1B s read m).numRead1Replies = (r1A s read m).numRead1Replies ∧
    (r1B s read m).numRead2Replies = (r1A s read m).numRead2Replies ∧
    (r1B s read m).sentRead2Round = (r1A s read m).sentRead2Round ∧
    (r1B s read m).determinedReadVal = (r1A s read m).determinedReadVal := by
  unfold r1B
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem r1A_ids (s : RState) (read : ReadOp) (m : Read1ReplyM) :
    (r1A s read m).requestId = read.requestId ∧ (r1A s read m).clientId = read.clientId ∧
    (r1A s read m).n = read.n ∧ (r1A s read m).readValTag = read.readValTag ∧
    (r1A s read m).numRead2Replies = read.numRead2Replies ∧
    (r1A s read m).sentRead2Round = read.sentRead2Round ∧
    (r1A s read m).determinedReadVal = read.determinedReadVal ∧
    (r1A s read m).numRead1Replies = read.numRead1Replies + 1 := by
  unfold r1A
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The fields `r1C` keeps. -/
theorem r1C_same (b : ReadOp) :
    (r1C b).requestId = b.requestId ∧ (r1C b).clientId = b.clientId ∧ (r1C b).n = b.n ∧
    (r1C b).maxValTag = b.maxValTag ∧ (r1C b).numRead1Replies = b.numRead1Replies ∧
    (r1C b).numRead2Replies = b.numRead2Replies ∧ (r1C b).readsWithMaxTag = b.readsWithMaxTag ∧
    (r1C b).sentRead2Round = b.sentRead2Round ∧
    (r1C b).replicasWithMaxTag = b.replicasWithMaxTag := by
  unfold r1C
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem r1C_t (b : ReadOp) (h : b.determinedReadVal = true) : r1C b = b := by
  simp [r1C, h]

theorem r1C_f (b : ReadOp) (h : b.determinedReadVal = false) :
    (r1C b).readValTag = b.maxValTag ∧ (r1C b).determinedReadVal = true := by
  simp [r1C, h]

/-- The replicas `HandleRead1Reply`'s loop has collected after `i`: those below `i` not in `L`. -/
def r2After (L : List w32) (iv : w32) : List w32 :=
  (([W32 0, W32 1, W32 2] : List w32).take (sint.nat iv)).filter (fun x => !(L.contains x))

theorem r2After_succ (L : List w32) (iv : w32) (h0 : 0 ≤ sint.Z iv) (h3 : sint.Z iv < 3) :
    r2After L (iv + W32 1) = r2After L iv ++ (if L.contains iv then [] else [iv]) := by
  unfold r2After
  rw [take3_succ iv h0 h3, List.filter_append]
  by_cases h : iv ∈ L <;> simp [h, List.filter]

theorem r2After_three (L : List w32) :
    r2After L (W32 3) = ([0, 1, 2] : List w32).filter (fun i => !(L.contains i)) := rfl

theorem ct_step (L : List w32) (j : Nat) (kk iv : w32) (h : L[j]? = some kk) (hne : iv ≠ kk)
    (hc : (L.take j).contains iv = false) : (L.take (j + 1)).contains iv = false := by
  have hc' : iv ∉ L.take j := by simpa using hc
  rw [List.take_add_one, h]
  simp [hc', hne]

theorem ct_end (L : List w32) (j : Nat) (iv : w32) (h : L.length ≤ j)
    (hc : (L.take j).contains iv = false) : L.contains iv = false := by
  rwa [List.take_of_length_le h] at hc

theorem ct_hit (L : List w32) (j : Nat) (iv : w32) (h : L[j]? = some iv) : L.contains iv = true := by
  have := List.mem_of_getElem? h
  simpa using this

/-- The read op when its Read2s are sent (`numRead2Replies` set), and after (`sentRead2Round`). -/
def r2Y (c : ReadOp) : ReadOp := { c with numRead2Replies := 3 - BitVec.ofNat 64 (r2Reps c).length }

def r2Z (c : ReadOp) : ReadOp := { r2Y c with sentRead2Round := true }

theorem stepRead1Reply_inv (k : Fin 3) (s s' : RState) (m : Read1ReplyM) (outs : List Out)
    (h : stepR k s (.msg (.read1Reply m)) = .ok (s', outs)) :
    (s.rops.get? (shiftInts m.requestId m.clientId) = none ∧ s' = s ∧ outs = []) ∨
    ∃ read, s.rops.get? (shiftInts m.requestId m.clientId) = some read ∧
      ((sge (r1B s read m).numRead1Replies (NHALF + 1) = false ∧
          s' = r1Put s read m (r1B s read m) ∧ outs = []) ∨
       (sge (r1B s read m).numRead1Replies (NHALF + 1) = true ∧
        ((sge (r1C (r1B s read m)).readsWithMaxTag (NHALF + 1) = true ∧
            ∃ rv, (r1C (r1B s read m)).readValTag = some rv ∧
            s' = r1Del s read m (r1C (r1B s read m)).n ∧
            outs = [.ext (.readReply (r1C (r1B s read m)).clientId
              (r1C (r1B s read m)).requestId rv.v 1)]) ∨
         (sge (r1C (r1B s read m)).readsWithMaxTag (NHALF + 1) = false ∧
            (r1C (r1B s read m)).sentRead2Round = true ∧
            s' = r1Put s read m (r1C (r1B s read m)) ∧ outs = []) ∨
         (sge (r1C (r1B s read m)).readsWithMaxTag (NHALF + 1) = false ∧
            (r1C (r1B s read m)).sentRead2Round = false ∧
            ∃ rv, (r1C (r1B s read m)).readValTag = some rv ∧
            sendsTo (r2Reps (r1C (r1B s read m)))
              (.read2 ⟨(r1C (r1B s read m)).requestId, (r1C (r1B s read m)).clientId, 0, rv,
                s.id⟩) = some outs ∧
            s' = r1Put s read m { r1C (r1B s read m) with
                numRead2Replies := 3 - BitVec.ofNat 64 (r2Reps (r1C (r1B s read m))).length,
                sentRead2Round := true })))) := by
  simp only [stepR, stepRead1Reply, bind, Except.bind, pure, Except.pure, never, disabled, dead,
    FailM.failNever, FailM.failDisabled, FailM.failDead] at h
  rcases Option.eq_none_or_eq_some (s.rops.get? (shiftInts m.requestId m.clientId)) with hg | ⟨read, hg⟩
  · left
    simp only [hg, Except.ok.injEq, Prod.mk.injEq] at h
    exact ⟨hg, h.1.symm, h.2.symm⟩
  right
  refine ⟨read, hg, ?_⟩
  simp only [hg] at h
  have hov : ∀ v t, (s.overwrite v t).id = s.id := by
    intro v t; unfold RState.overwrite; split <;> rfl
  simp only [hov] at h
  simp only [r1Put, r1Del, r1C, r1B, r1A, r1S, r1New, r2Reps, sendsTo]
  repeat' (first | (simp only [↓reduceIte, if_true, if_false, Bool.true_eq_false, ite_true, ite_false] at h) | split at h)
  all_goals (try (first
    | (cases h; done)
    | (simp only [Except.ok.injEq, Prod.mk.injEq] at h
       obtain ⟨rfl, rfl⟩ := h
       simp_all; done)))


end Perennial.gryff.replica2
