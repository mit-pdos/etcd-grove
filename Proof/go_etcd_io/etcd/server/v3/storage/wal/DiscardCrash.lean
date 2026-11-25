/- Lean-first (no Rocq counterpart).
# `Discard`'s window across a crash (P6b, mit-pdos/etcd-grove#50; P5's condition 1 on `wal.Discard.spec`)

Between `Discard`'s two updates (`AU₁` at the rename, `AU₂` at the parent's fsync) the client holds the WAL at
`dir` **unnamed** at incarnation `ic + 1` (`walDiskAtI dir (ic + 1) { d with named := false }`). A crash then
either loses it (the rename was durable: no WAL at `dir`) or keeps it (the rename was not), and a blank WAL
(`walBlank`, what `Unsaved`'s `true` gives) stays blank: `walDiskAt_crash_blank_keep`, as
`walDiskAt_crash_any_keep0` (`Crash.lean`, the `_keep` lemmas) with the crash image's blankness
(`walImg_blank`). A separate module, beside `Crash.lean` (which does not import `UnsavedDefs`, where
`walBlank` is).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.Crash
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.UnsavedDefs

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section pure
variable [GooseExts]

/-- **Every crash image of a blank history is blank** (with no operation synced: any image). -/
theorem walImg_blank {H I : List (WalOpG WalEnt)} {n : Nat} (hI : walImg H n I)
    (hb : walBlank (H.map WalOpG.toM)) : walBlank (I.map WalOpG.toM) := by
  obtain ⟨j, -, -, hI⟩ := hI
  rcases hI with rfl | ⟨h, es, k, hj, -, rfl⟩
  · rw [List.map_take]; exact walBlank_take hb j
  · intro o ho
    rw [List.map_append, List.mem_append] at ho
    rcases ho with ho | ho
    · rw [List.map_take] at ho; exact walBlank_take hb j o ho
    · have hm : (WalOpG.save h es).toM ∈ H.map WalOpG.toM :=
        List.mem_map_of_mem (List.mem_of_getElem? hj)
      have h0 := hb _ hm
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at ho
      subst ho
      simp only [WalOpG.toM, walOpBlank, List.map_eq_nil_iff] at h0 ⊢
      refine ⟨by rw [h0.1]; simp, ?_⟩
      simp [hsEmptyP]

end pure

section crash
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF]
variable (W W' : WalGS GF)

/-- **A blank WAL across a crash, at any incarnation** (`Discard`'s window: the WAL unnamed at `ic + 1`):
the new generation has no WAL at `dir` (only if the WAL was unnamed), or the WAL cut to a crash image,
blank again. -/
theorem walDiskAt_crash_blank_keep (dir : GoString) (i : Nat) (d : WalDur)
    (hb : walBlank (d.H.map WalOpG.toM)) :
    ⊢@{IProp GF} walCrashWal W W' -∗
      walDiskAtI (W := W) dir i d -∗
      walDiskAtI (W := W) dir i d ∗ ((walAbsentI (W := W') dir 0 ∗ ⌜d.named = false⌝) ∨
        ∃ (I : List (WalOpG WalEnt)) (k : Nat),
          ⌜walImg d.H 0 I ∧ walBlank (I.map WalOpG.toM) ∧ k ≤ min d.pur I.length⌝ ∗
          walDiskAtI (W := W') dir 0
            { d with H := I, cut := k, unl := min d.unl I.length, pur := min d.pur I.length }) := by
  iintro Hcs Hd
  icases walDiskAt_crash_any_keep0 W W' dir i d $$ Hcs Hd with ⟨Hd, Hc⟩
  iframe Hd
  icases Hc with (Ha | ⟨%I, %k, ⟨%hI, %hk⟩, Hd'⟩)
  · ileft; iexact Ha
  · iright
    iexists I, k
    iframe Hd'
    ipureintro; exact ⟨hI, walImg_blank hI hb, hk⟩

end crash

end WalFs
end EtcdGrove
end Perennial

end
