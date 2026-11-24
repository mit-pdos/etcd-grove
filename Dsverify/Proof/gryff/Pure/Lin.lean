/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Pure/Lin.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Linearization (stage 2, unit L; `notes/stage2-proof.md` §L, `notes/stage2-plan.md` §1, §5): the
statements. The definitions (operations, places, the frontier, `lin`, `WB`) are in
`GryffProof/Pure/LinDefs.lean` (split from this file, unchanged, so that unit L's proof modules in
`GryffProof/PureL/` can import them).
-/
module

public import Dsverify.Proof.gryff.Pure.LinDefs
public import Dsverify.Proof.gryff.PureL.F4
public import Dsverify.Proof.gryff.PureL.F2
public import Dsverify.Proof.gryff.PureLb.F3
public import Dsverify.Proof.gryff.PureLc.F1

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure

open model kahn proto dsverify_lab.harness

/-! ## The theorems -/

section
variable {l1 l2 : List Label} {c : Cfg gNet}

/-- **(F1) Replay**: replaying `lin (l1 ++ l2) k`'s inputs from 0 with the register gives each
operation's output in the run and ends at the frontier's value. -/
theorem lin_replay (h : GRun (Cfg.init gNet) (l1 ++ l2) c) (hwb : WB l1) {k : Nat}
    (hk : k ≤ l1.length) :
    replayOk (0 : w64) ((lin (l1 ++ l2) k).map fun o => (o.inp, opOut (l1 ++ l2) o))
      (frontVal (l1 ++ l2) k) :=
  -- unit L-c: `PureLc/F1.lean` (the abstract replay `PureLc/Replay.lean` from L1, L3 and producer
  -- uniqueness; the remaining internal sorries are in `PureLc/Facts.lean`, see notes/unit-Lc.md)
  lin_replay_run h hwb hk

/-- **(F2) Monotonicity**: the linearization at a cut is a prefix of the one at a later cut. -/
theorem lin_prefix (h : GRun (Cfg.init gNet) (l1 ++ l2) c) (hwb : WB l1) {k k' : Nat}
    (hkk : k ≤ k') (hk : k' ≤ l1.length) :
    lin (l1 ++ l2) k <+: lin (l1 ++ l2) k' :=
  lin_prefix_run h hkk

/-- **(F3) Replies**: a reply output at label `n` of `l1` is to an operation created earlier at the
same replica with the reply's key and kind, linearized at cut `n + 1` with the reply's output. -/
theorem lin_reply (h : GRun (Cfg.init gNet) (l1 ++ l2) c) (hwb : WB l1) {n : Nat}
    (hn : n < l1.length) {x : Ext} (hx : x ∈ extsAt (l1 ++ l2) n) :
    ∃ o ∈ ops (l1 ++ l2), o.g < n ∧ ((l1 ++ l2)[n]?).map Prod.fst = some o.r ∧
      (o.cid, o.rid) = x.key ∧ x.fits o.inp ∧ o ∈ lin (l1 ++ l2) (n + 1) ∧
      opOut (l1 ++ l2) o = x.out :=
  -- unit L-b (`PureLb/F3.lean`): reply ownership, L2 for reads, writes and RMWs (the RMW side
  -- by the executed accounting, `PureLb/ExInv.lean`, `PureLb/RmwL2.lean`).
  lin_reply_run h (by rw [List.length_append]; omega) hx

/-- An operation is replied to at most once within `l1`. -/
theorem reply_once (h : GRun (Cfg.init gNet) (l1 ++ l2) c) (hwb : WB l1) {o : Op}
    (ho : o ∈ ops (l1 ++ l2)) {n n' : Nat} (hn : n < l1.length) (hn' : n' < l1.length)
    (r1 : RepliesTo (l1 ++ l2) n o) (r2 : RepliesTo (l1 ++ l2) n' o) : n = n' :=
  -- unit L-b (`PureLb/F3.lean`, `PureLb/Once.lean`): reads/writes' records are deleted by their
  -- reply and never re-created; an RMW's instance is replied to once (`PureLb/RmwL2.lean`).
  reply_once_run h ho r1 r2

end

/-! ## (F4) What the linearization depends on -/

/-- Places depend only on the replicas' projections (and the operation's position, key and input:
not on its creation index `g`). -/
theorem place_congr {l l' : List Label} (hp : ∀ r, projR l r = projR l' r) (o : Op) :
    place l o = place l' o := by
  simp only [place, writePlace, rmwPlace, rmwInst, readPlace, readReply, hp]

/-- Outputs depend only on the replicas' projections. -/
theorem opOut_congr {l l' : List Label} (hp : ∀ r, projR l r = projR l' r) (o : Op) :
    opOut l o = opOut l' o := by
  simp only [opOut, readReply, hp]

/-- **(F4)** `lin l k` depends only on the first `k` labels and the places of the operations created
within them. -/
theorem lin_congr {l l' : List Label} {k : Nat} (hk : l.take k = l'.take k)
    (hpl : ∀ o ∈ ops l, o.g < k → place l o = place l' o) : lin l k = lin l' k := by
  have hpl' : ∀ o ∈ ops (l.take k), place l o = place l' o := by
    intro o ho
    rw [← ops_take, List.mem_filter] at ho
    exact hpl o ho.1 (by simpa using ho.2)
  unfold lin
  rw [lin_filter, lin_filter, ← hk, front_congr hk]
  have hf : (ops (l.take k)).filter (fun o => placeLe l o (front l' k)) =
      (ops (l.take k)).filter (fun o => placeLe l' o (front l' k)) := by
    apply List.filter_congr; intro o ho; simp only [placeLe, hpl' o ho]
  rw [hf]
  have hsub : ∀ o ∈ (ops (l.take k)).filter (fun o => placeLe l' o (front l' k)), o ∈ ops l := by
    intro o ho
    have := (List.mem_filter.1 ho).1
    rw [← ops_take, List.mem_filter] at this; exact this.1
  apply pureL.mergeSort_congr (opLe_trans l) (opLe_total l) (opLe_trans l') (opLe_total l')
  · intro a ha b hb
    have ha' := hpl' a (List.mem_filter.1 ha).1
    have hb' := hpl' b (List.mem_filter.1 hb).1
    simp only [opLe, ha', hb']
  · intro a ha b hb h1 h2
    have ha' := hpl' a (List.mem_filter.1 ha).1
    have hb' := hpl' b (List.mem_filter.1 hb).1
    apply opLe_antisymm (hsub a ha) (hsub b hb)
    · simp only [opLe, ha', hb'] at h1 ⊢; exact h1
    · simp only [opLe, ha', hb'] at h2 ⊢; exact h2

/-- (F4) for the Iris invariant: two runs with the same projections (both end at the closure)
and the same first `k` labels have the same linearization at `k`, with the same outputs. -/
theorem lin_congr_proj {l l' : List Label} {k : Nat} (hk : l.take k = l'.take k)
    (hp : ∀ r, projR l r = projR l' r) :
    lin l k = lin l' k ∧ front l k = front l' k ∧ frontVal l k = frontVal l' k ∧
      ∀ o, opOut l o = opOut l' o :=
  ⟨lin_congr hk (fun o _ _ => place_congr hp o), front_congr hk, frontVal_congr hk,
    opOut_congr hp⟩

end Perennial.gryff.pure
