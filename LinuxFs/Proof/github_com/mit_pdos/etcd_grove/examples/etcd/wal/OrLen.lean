/- Lean-first (no Rocq counterpart).

**The oracle's encoded length** (W4c U5). `tEncodeOracle o` writes every number as eight bytes
(`tU64`), so its length depends only on the oracle's shape (the number of candidates, of operations, of
entries, of pending opens), never on the values: not on a hard state's, a mark's or a bound's. Hence
`tOrSmall` of an oracle a member operation stores holds for every hard state the operation may choose
(`opTerm`'s vote, `opCommit`'s commit) once it holds for one, and it follows from **room** in the current
oracle (`tOrRoom o n`: `n` more bytes keep it within `durable.Write`'s 1 GiB): appending a save of `k`
entries costs `56 + 32 k` bytes (`tEncodeOracle_saveO1`); moving the mark (`tSynced`) or `lastHS` costs
nothing.

Also: an oracle within 1 GiB has every candidate history shorter than `2^62` (each operation is at least
56 bytes), the bound `tCheckWf` asks (`tOrSmall_hist_lt`), so `tCheckWf` is kept by a save
(`tCheckWf_saveO`).
-/
module

public import LinuxFs.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.SavePure
public import LinuxFs.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.Check

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI

section pure
variable [GooseExts]

/-- An operation's encoded length (`tOpBytes`). -/
def tOpLen (o : TOp) : Nat := 56 + 32 * o.ents.length

/-- **Room for `n` more bytes**: the oracle's encoding grown by `n` stays within 1 GiB. -/
def tOrRoom (o : TOracle) (n : Nat) : Prop := (tEncodeOracle o).length + n ≤ 0x40000000

theorem tEntBytes_length (e : TEnt) : (tEntBytes e).length = 32 := by
  simp [tEntBytes, tU64_length]

theorem flatMap_const_length {α β : Type} (f : α → List β) (k : Nat) (hf : ∀ a, (f a).length = k)
    (l : List α) : (l.flatMap f).length = k * l.length := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, hf, ih, Nat.mul_succ]; omega

theorem tOpBytes_length (o : TOp) : (tOpBytes o).length = tOpLen o := by
  simp only [tOpBytes, tOpLen, List.length_append, tU64_length, tHsBytes_length,
    flatMap_const_length tEntBytes 32 tEntBytes_length]

theorem tOpsBytes_length (h : List TOp) : (tOpsBytes h).length = 8 + (h.map tOpLen).sum := by
  simp only [tOpsBytes, List.length_append, tU64_length, List.length_flatMap]
  congr 1
  congr 1
  apply List.map_congr_left
  intro o _; exact tOpBytes_length o

theorem tOpsBytes_snoc (h : List TOp) (op : TOp) :
    (tOpsBytes (h ++ [op])).length = (tOpsBytes h).length + tOpLen op := by
  rw [tOpsBytes_length, tOpsBytes_length]; simp; omega

/-- The encoding's length, with `since`'s part and the rest apart: the rest does not mention
`since`, `synced` or `lastHS`. -/
def tOrRest (o : TOracle) : Nat :=
  16 + (o.cands.flatMap (fun c => tOpsBytes c.h ++ tU64 c.unl ++ tU64 c.pur)).length + 8 + 24 + 8 +
    8 * o.opens.length

theorem tEncodeOracle_length (o : TOracle) :
    (tEncodeOracle o).length = tOrRest o + (tOpsBytes o.since).length := by
  simp only [tEncodeOracle, tOrRest, List.length_append, tU64_length, tHsBytes_length,
    flatMap_const_length tU64 8 tU64_length]
  omega

/-- **Appending a save costs `56 + 32 |es|` bytes, whatever its hard state.** -/
theorem tEncodeOracle_saveO1 (o : TOracle) (h : THs) (es : List TEnt) :
    (tEncodeOracle (tSaveO1 o h es)).length = (tEncodeOracle o).length + (56 + 32 * es.length) := by
  rw [tEncodeOracle_length, tEncodeOracle_length]
  have hr : tOrRest (tSaveO1 o h es) = tOrRest o := rfl
  rw [hr]
  show _ + (tOpsBytes (o.since ++ [tSaveOp h es])).length = _
  rw [tOpsBytes_snoc]; simp [tOpLen, tSaveOp]; omega

/-- Moving the mark costs nothing. -/
theorem tEncodeOracle_synced (o : TOracle) :
    (tEncodeOracle (tSynced o)).length = (tEncodeOracle o).length := by
  rw [tEncodeOracle_length, tEncodeOracle_length]; rfl

/-- Changing `lastHS` costs nothing. -/
theorem tEncodeOracle_lastHS (o : TOracle) (p : THs) :
    (tEncodeOracle { o with lastHS := p }).length = (tEncodeOracle o).length := by
  rw [tEncodeOracle_length, tEncodeOracle_length]; rfl

/-- **The save's stored oracles do not depend on the hard state's values**, for `tOrSmall`. -/
theorem tOrSmall_saveO1_iff (o : TOracle) (h h' : THs) (es : List TEnt) :
    tOrSmall (tSaveO1 o h es) ↔ tOrSmall (tSaveO1 o h' es) := by
  unfold tOrSmall; rw [tEncodeOracle_saveO1, tEncodeOracle_saveO1]

/-- **Room gives `save`'s two size premises**, for every hard state. -/
theorem tOrRoom_save {o : TOracle} {es : List TEnt} {n : Nat} (hr : tOrRoom o n)
    (hn : 56 + 32 * es.length ≤ n) (h : THs) :
    tOrSmall (tSaveO1 o h es) ∧ tOrSmall (tSynced (tSaveO1 o h es)) := by
  unfold tOrRoom at hr
  unfold tOrSmall
  rw [tEncodeOracle_synced, tEncodeOracle_saveO1]
  omega

/-- The oracle after a whole `save` is at most `56 + 32 |es|` bytes longer. -/
theorem tEncodeOracle_saveO_le (o : TOracle) (h : THs) (es : List TEnt) :
    (tEncodeOracle (tSaveO o h es)).length ≤ (tEncodeOracle o).length + (56 + 32 * es.length) := by
  unfold tSaveO
  split
  · omega
  · rw [tEncodeOracle_lastHS]
    split
    · rw [tEncodeOracle_synced, tEncodeOracle_saveO1]; exact Nat.le_refl _
    · rw [tEncodeOracle_saveO1]; exact Nat.le_refl _

/-- **Room is used up by a save's bytes.** -/
theorem tOrRoom_saveO {o : TOracle} {es : List TEnt} {n : Nat}
    (hr : tOrRoom o (n + (56 + 32 * es.length))) (h : THs) : tOrRoom (tSaveO o h es) n := by
  unfold tOrRoom at *
  have := tEncodeOracle_saveO_le o h es
  omega

theorem tOrRoom_mono {o : TOracle} {n n' : Nat} (hr : tOrRoom o n) (h : n' ≤ n) : tOrRoom o n' := by
  unfold tOrRoom at *; omega

theorem tOpLen_ge (o : TOp) : 56 ≤ tOpLen o := by unfold tOpLen; omega

theorem sum_map_ge {α : Type} (f : α → Nat) (k : Nat) (hf : ∀ a, k ≤ f a) (l : List α) :
    k * l.length ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_succ]; have := hf a; omega

theorem tOpsBytes_length_ge (h : List TOp) : 56 * h.length ≤ (tOpsBytes h).length := by
  rw [tOpsBytes_length]; have := sum_map_ge tOpLen 56 tOpLen_ge h; omega

theorem length_le_flatMap_of_mem {α β : Type} (f : α → List β) {l : List α} {a : α} (ha : a ∈ l) :
    (f a).length ≤ (l.flatMap f).length := by
  induction l with
  | nil => cases ha
  | cons b l ih =>
    rw [List.flatMap_cons, List.length_append]
    rcases List.mem_cons.1 ha with rfl | ha
    · omega
    · have := ih ha; omega

/-- **An oracle within 1 GiB has every candidate history shorter than `2^62`.** -/
theorem tOrSmall_hist_lt {o : TOracle} (hs : tOrSmall o) {cd : TCand} (hc : cd ∈ o.cands) :
    (tCandHist o cd).length < 2 ^ 62 := by
  unfold tOrSmall at hs
  rw [tEncodeOracle_length] at hs
  have h1 := length_le_flatMap_of_mem (fun c => tOpsBytes c.h ++ tU64 c.unl ++ tU64 c.pur) hc
  have h2 := tOpsBytes_length_ge cd.h
  have h3 := tOpsBytes_length_ge o.since
  simp only [List.length_append] at h1
  unfold tOrRest at hs
  unfold tCandHist
  simp only [List.length_append]
  omega

theorem tOrSmall_since_lt {o : TOracle} (hs : tOrSmall o) : o.since.length < 2 ^ 62 := by
  unfold tOrSmall at hs
  rw [tEncodeOracle_length] at hs
  have := tOpsBytes_length_ge o.since
  omega

/-- **A save's append keeps `tCheckWf`**, its oracle within 1 GiB. -/
theorem tCheckWf_saveO1 {o : TOracle} (hw : tCheckWf o) (h : THs) (es : List TEnt)
    (hes : ∀ x ∈ es, tEntWf x) (ht : uint.nat h.term' < 2 ^ 63) (hs : tOrSmall (tSaveO1 o h es)) :
    tCheckWf (tSaveO1 o h es) := by
  refine ⟨?_, fun cd hcd => ⟨?_, tOrSmall_hist_lt hs hcd⟩⟩
  · show uint.nat o.synced ≤ (o.since ++ [tSaveOp h es]).length
    simp only [List.length_append, List.length_singleton]; have := hw.1; omega
  · rw [tSaveO1_hist o cd h es]
    exact tHistWf_snoc (hw.2 cd hcd).1 (tSaveOp_wf h es hes ht)

/-- **A save keeps `tCheckWf`**, its oracle within 1 GiB. -/
theorem tCheckWf_saveO {o : TOracle} (hw : tCheckWf o) (h : THs) (es : List TEnt)
    (hes : ∀ x ∈ es, tEntWf x) (ht : uint.nat h.term' < 2 ^ 63) (hs : tOrSmall (tSaveO o h es)) :
    tCheckWf (tSaveO o h es) := by
  obtain ⟨hw1, hw2⟩ := hw
  have hcands : (tSaveO o h es).cands = o.cands := by
    unfold tSaveO; split
    · rfl
    · split <;> rfl
  refine ⟨?_, ?_⟩
  · unfold tSaveO
    split
    · exact hw1
    · have hl := tOrSmall_since_lt hs
      unfold tSaveO at hl
      rw [if_neg (by assumption)] at hl
      split
      · rename_i _ hm
        simp only [hm, ↓reduceIte] at hl
        show uint.nat (W64 (o.since ++ [tSaveOp h es]).length) ≤ (o.since ++ [tSaveOp h es]).length
        rw [uint_nat_W64_of_lt' _ (by simp only [tSynced, tSaveO1] at hl; omega)]
        exact Nat.le_refl _
      · show uint.nat o.synced ≤ (o.since ++ [tSaveOp h es]).length
        simp; omega
  · intro cd hcd
    rw [hcands] at hcd
    refine ⟨?_, tOrSmall_hist_lt hs (by rw [hcands]; exact hcd)⟩
    have hhist : tCandHist (tSaveO o h es) cd = tCandHist o cd ∨
        tCandHist (tSaveO o h es) cd = tCandHist o cd ++ [tSaveOp h es] := by
      unfold tSaveO; split
      · exact Or.inl rfl
      · right; split
        · exact tSaveO1_hist o cd h es
        · exact tSaveO1_hist o cd h es
    rcases hhist with hh | hh <;> rw [hh]
    · exact (hw2 cd hcd).1
    · exact tHistWf_snoc (hw2 cd hcd).1 (tSaveOp_wf h es hes ht)

end pure

end etcd_wal
end EtcdGrove
end Perennial
