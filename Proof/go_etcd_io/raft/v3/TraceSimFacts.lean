/-
Lean-first (no Rocq counterpart). Trace-check's S5, Draft (2026-11-09): the simulation invariant's
per-server facts (`notes/trace-validation-sim.md`, "The invariants", route (a): for every server `j`,
the persistent raft facts `σ.s j` stands for) and the specification's invariants derived from them.

- `srvFacts γ C j v`: server `v` (node `j`'s in `σ`) is raft's log `es` read by `logAbs` (the
  bootstrap the `|C|` configuration entries), with `es`'s records (`logRecs`), its committed prefix
  committed (`isCommitted`), and, a leader, raft's leader of its term (`isLeader`); its numbers in
  range.
- `allFacts γ C σ`: every voter's.

Derived so far: `MoreThanOneLeaderInv` (from `isLeader_unique`).
-/
module

public import Proof.go_etcd_io.raft.v3.TraceSimInv
public import Proof.go_etcd_io.raft.v3.Protocol.Ghost

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceSim

section pure
variable [GooseExts]

theorem mem_confAbs_inv (C : List w64) (x : Etcdraft.ID) (h : x ∈ confAbs C) : ∃ w ∈ C, x = idAbs w := by
  unfold confAbs at h; rw [setIds_mk_mem, List.mem_map] at h
  obtain ⟨w, hw, e⟩ := h; exact ⟨w, hw, e.symm⟩

theorem logAbs_take (C : List w64) (bl f : Nat) (l : List EntryM) (n : Nat) :
    (logAbs C bl f l).take n = logAbs C bl f (l.take n) := by
  unfold logAbs
  apply List.ext_getElem?
  intro k
  simp only [List.getElem?_take, List.getElem?_mapIdx]
  split <;> simp_all

theorem logAbs_prefix (C : List w64) (bl f : Nat) (l1 l2 : List EntryM) (h : l1 <+: l2) :
    logAbs C bl f l1 <+: logAbs C bl f l2 := by
  obtain ⟨r, rfl⟩ := h
  refine ⟨(logAbs C bl f (l1 ++ r)).drop l1.length, ?_⟩
  have : logAbs C bl f l1 = (logAbs C bl f (l1 ++ r)).take l1.length := by
    rw [logAbs_take, List.take_left' rfl]
  rw [this, List.take_append_drop]

theorem isPrefix_of_prefix (s t : List Etcdraft.Entry) (h : s <+: t) : Etcdraft.isPrefix s t = true := by
  unfold Etcdraft.isPrefix
  obtain ⟨r, rfl⟩ := h
  simp

end pure

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **A server's facts**: node `j`'s server `v` in the simulation's state. -/
def srvFacts (γ : RaftNames) (C : List w64) (j : w64) (v : Etcdraft.Server) : IProp GF :=
  iprop(∃ es : List EntryM,
    ⌜v.log = logAbs C C.length 1 es ∧ BootTerms C.length 1 es ∧
      0 ≤ v.commitIndex ∧ v.commitIndex ≤ es.length ∧ 0 ≤ v.currentTerm ∧ v.currentTerm < 2 ^ 63⌝ ∗
    logRecs γ ⟨W64 0, W64 0⟩ es ∗ isCommitted γ (es.take v.commitIndex.toNat) ∗
    (if v.state = Etcdraft.leader then isLeader γ j (W64 v.currentTerm) else iprop(True)))

instance srvFacts_persistent (γ : RaftNames) (C : List w64) (j : w64) (v : Etcdraft.Server) :
    Persistent (srvFacts (GF := GF) γ C j v) := by
  unfold srvFacts; split <;> infer_instance

/-- **Every voter's facts** in state `σ`. -/
def allFacts (γ : RaftNames) (C : List w64) (σ : Etcdraft.State) : IProp GF :=
  iprop(□ ∀ j, ⌜j ∈ C⌝ → srvFacts γ C j (σ.s (idAbs j)))

instance allFacts_persistent (γ : RaftNames) (C : List w64) (σ : Etcdraft.State) :
    Persistent (allFacts (GF := GF) γ C σ) := by
  unfold allFacts; infer_instance

/-- A leader's term's word. -/
theorem w64_of_int_inj (a b : Int) (ha : 0 ≤ a) (ha' : a < 2 ^ 63) (hb : 0 ≤ b) (hb' : b < 2 ^ 63)
    (h : W64 a = W64 b) : a = b := by
  have h1 : uint.Z (W64 a) = a := by word
  have h2 : uint.Z (W64 b) = b := by word
  rw [← h1, ← h2, h]

/-- **`MoreThanOneLeaderInv` from the facts** (`isLeader_unique`). -/
theorem allFacts_oneLeader (γ : RaftNames) (C : List w64) (σ : Etcdraft.State)
    (hsrv : σ.server = confAbs C) :
    allFacts (GF := GF) γ C σ ⊢ ⌜σ.moreThanOneLeaderInv = true⌝ := by
  iintro #H
  iunfold allFacts at H
  by_cases hc : σ.moreThanOneLeaderInv = true
  · ipureintro; exact hc
  -- a pair of distinct leaders of one term
  have : ∃ i ∈ C, ∃ j ∈ C, (σ.s (idAbs i)).currentTerm = (σ.s (idAbs j)).currentTerm ∧
      (σ.s (idAbs i)).state = Etcdraft.leader ∧ (σ.s (idAbs j)).state = Etcdraft.leader ∧ i ≠ j := by
    unfold Etcdraft.State.moreThanOneLeaderInv at hc
    rw [hsrv, List.all_eq_true] at hc
    simp only [Classical.not_forall, List.all_eq_true] at hc
    obtain ⟨x, hx, hc⟩ := hc
    obtain ⟨y, hy, hc⟩ := hc
    obtain ⟨i, hi, rfl⟩ := mem_confAbs_inv C x hx
    obtain ⟨j, hj, rfl⟩ := mem_confAbs_inv C y hy
    refine ⟨i, hi, j, hj, ?_⟩
    by_cases h1 : (σ.s (idAbs i)).currentTerm = (σ.s (idAbs j)).currentTerm
    · by_cases h2 : (σ.s (idAbs i)).state = Etcdraft.leader
      · by_cases h3 : (σ.s (idAbs j)).state = Etcdraft.leader
        · refine ⟨h1, h2, h3, fun e => hc ?_⟩
          subst e; simp
        · exact absurd (by simp [h3]) hc
      · exact absurd (by simp [h2]) hc
    · exact absurd (by simp [h1]) hc
  obtain ⟨i, hi, j, hj, ht, hli, hlj, hne⟩ := this
  ihave Hfi := H $$ %i %hi
  ihave Hfj := H $$ %j %hj
  iunfold srvFacts at Hfi Hfj
  icases Hfi with ⟨%esi, %Hpi, -, -, Hli⟩
  icases Hfj with ⟨%esj, %Hpj, -, -, Hlj⟩
  simp only [hli, hlj, ite_true]
  rw [ht]
  icases isLeader_unique γ i j _ $$ Hli Hlj with %He
  exact absurd He hne

/-- A server's committed prefix, from its facts' log. -/
theorem committedL_abs (C : List w64) (σ : Etcdraft.State) (i : Etcdraft.ID) (es : List EntryM)
    (hlog : (σ.s i).log = logAbs C C.length 1 es) :
    committedL σ i = logAbs C C.length 1 (es.take (σ.s i).commitIndex.toNat) := by
  unfold committedL; rw [hlog, logAbs_take]

/-- **`LogInv`'s facts** (`isCommitted_agree`): any two voters' committed prefixes are prefixes one of
the other. -/
theorem allFacts_logInv (γ : RaftNames) (C : List w64) (σ : Etcdraft.State)
    (hsrv : σ.server = confAbs C) :
    allFacts (GF := GF) γ C σ ⊢ ⌜∀ i ∈ σ.server, ∀ j ∈ σ.server,
      (or (Etcdraft.isPrefix (committedL σ i) (committedL σ j))
        (Etcdraft.isPrefix (committedL σ j) (committedL σ i))) = true⌝ := by
  iintro #H
  iunfold allFacts at H
  by_cases hc : ∀ i ∈ σ.server, ∀ j ∈ σ.server,
      (or (Etcdraft.isPrefix (committedL σ i) (committedL σ j))
        (Etcdraft.isPrefix (committedL σ j) (committedL σ i))) = true
  · ipureintro; exact hc
  simp only [Classical.not_forall] at hc
  obtain ⟨x, hx, y, hy, hc⟩ := hc
  rw [hsrv] at hx hy
  obtain ⟨i, hi, rfl⟩ := mem_confAbs_inv C x hx
  obtain ⟨j, hj, rfl⟩ := mem_confAbs_inv C y hy
  ihave Hfi := H $$ %i %hi
  ihave Hfj := H $$ %j %hj
  iunfold srvFacts at Hfi Hfj
  icases Hfi with ⟨%esi, %Hpi, -, Hci, -⟩
  icases Hfj with ⟨%esj, %Hpj, -, Hcj, -⟩
  icases isCommitted_agree γ _ _ $$ Hci Hcj with %Hag
  exfalso
  apply hc
  rw [committedL_abs C σ _ esi Hpi.1, committedL_abs C σ _ esj Hpj.1]
  rcases Hag with h | h
  · simp [isPrefix_of_prefix _ _ (logAbs_prefix C C.length 1 _ _ h)]
  · simp [isPrefix_of_prefix _ _ (logAbs_prefix C C.length 1 _ _ h)]

end ghost

end EtcdGrove
end Perennial
