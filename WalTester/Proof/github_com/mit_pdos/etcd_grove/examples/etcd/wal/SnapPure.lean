/- Lean-first (no Rocq counterpart).

**`member.saveSnap`'s pure vocabulary** (W4c U5): the operation the tester appends
(`tSnapOp idx term`: `walOp{snap: true, idx, term}`, a zero hard state and no entries), the oracle after
the append (`tSnapO1`, the first store) and after the whole call (`tSnapO`: `SaveSnapshot` syncs, so the
mark moves to the end). Its size (56 bytes, `tEncodeOracle_snapO1`) and `tCheckWf` across it and across a
mark's move (`tCheckWf_snapO`, `tCheckWf_synced`).
-/
module

public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.OrLen

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI

section pure
variable [GooseExts]

/-- `walOp{snap: true, idx: idx, term: term}`. -/
def tSnapOp (idx term : w64) : TOp := ⟨true, tHs0, [], idx, term⟩

/-- The oracle with the snapshot appended to `since` (what `saveSnap` stores first). -/
def tSnapO1 (o : TOracle) (idx term : w64) : TOracle :=
  { o with since := o.since ++ [tSnapOp idx term] }

/-- **The oracle after `saveSnap(idx, term)`** (wal.go): the append, then the mark at the end. -/
def tSnapO (o : TOracle) (idx term : w64) : TOracle := tSynced (tSnapO1 o idx term)

theorem tEncodeOracle_snapO1 (o : TOracle) (idx term : w64) :
    (tEncodeOracle (tSnapO1 o idx term)).length = (tEncodeOracle o).length + 56 := by
  rw [tEncodeOracle_length, tEncodeOracle_length]
  have hr : tOrRest (tSnapO1 o idx term) = tOrRest o := rfl
  rw [hr]
  show _ + (tOpsBytes (o.since ++ [tSnapOp idx term])).length = _
  rw [tOpsBytes_snoc]; simp [tOpLen, tSnapOp]; omega

theorem tEncodeOracle_snapO (o : TOracle) (idx term : w64) :
    (tEncodeOracle (tSnapO o idx term)).length = (tEncodeOracle o).length + 56 := by
  unfold tSnapO; rw [tEncodeOracle_synced, tEncodeOracle_snapO1]

/-- **Room gives `saveSnap`'s size premise.** -/
theorem tOrRoom_snap {o : TOracle} {n : Nat} (hr : tOrRoom o n) (hn : 56 ≤ n) (idx term : w64) :
    tOrSmall (tSnapO1 o idx term) := by
  unfold tOrRoom at hr; unfold tOrSmall; rw [tEncodeOracle_snapO1]; omega

/-- Room is used up by the snapshot's bytes. -/
theorem tOrRoom_snapO {o : TOracle} {n : Nat} (hr : tOrRoom o (n + 56)) (idx term : w64) :
    tOrRoom (tSnapO o idx term) n := by
  unfold tOrRoom at *; rw [tEncodeOracle_snapO]; omega

theorem tSnapOp_wf {idx term : w64} (hi : uint.nat idx < 2 ^ 63) (ht : uint.nat term < 2 ^ 63) :
    tOpWf (tSnapOp idx term) :=
  ⟨fun _ => ⟨hi, ht⟩, ⟨fun h => by simp [tSnapOp] at h, fun h => by simp [tSnapOp] at h⟩⟩

/-- **A mark's move keeps `tCheckWf`.** -/
theorem tCheckWf_synced {o : TOracle} (hw : tCheckWf o) (hl : o.since.length < 2 ^ 64) :
    tCheckWf (tSynced o) := by
  obtain ⟨-, hw2⟩ := hw
  refine ⟨?_, fun cd hcd => hw2 cd hcd⟩
  show uint.nat (W64 o.since.length) ≤ o.since.length
  rw [uint_nat_W64_of_lt' _ hl]; exact Nat.le_refl _

/-- **A snapshot keeps `tCheckWf`**, its oracle within 1 GiB. -/
theorem tCheckWf_snapO {o : TOracle} (hw : tCheckWf o) {idx term : w64} (hi : uint.nat idx < 2 ^ 63)
    (ht : uint.nat term < 2 ^ 63) (hs : tOrSmall (tSnapO1 o idx term)) : tCheckWf (tSnapO o idx term) := by
  have hl := tOrSmall_since_lt hs
  refine tCheckWf_synced ⟨?_, fun cd hcd => ⟨?_, tOrSmall_hist_lt hs hcd⟩⟩ (by omega)
  · show uint.nat o.synced ≤ (o.since ++ [tSnapOp idx term]).length
    simp only [List.length_append, List.length_singleton]; have := hw.1; omega
  · show tHistWf (cd.h ++ (o.since ++ [tSnapOp idx term]))
    rw [← List.append_assoc]
    exact tHistWf_snoc (hw.2 cd hcd).1 (tSnapOp_wf hi ht)

theorem tSnapO_lastHS (o : TOracle) (idx term : w64) : (tSnapO o idx term).lastHS = o.lastHS := rfl

end pure

end etcd_wal
end EtcdGrove
end Perennial
