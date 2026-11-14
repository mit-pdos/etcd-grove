/- Lean-first (no Rocq counterpart).

# The append's commit: the invariant's pure part (W6 of `notes/wal-fsext-plan.md`, "W6 implementation log")

`Save`'s and `SaveSnapshot`'s update commits right after `w.mu.Lock()`, before any record is encoded:
the WAL's history gains the operation `o` (`walAppS s dir d o`), the layouts stay. The invariant's pure
conjuncts at the new state:

* `walsOk_append`: the static relation (`walAbsD_snoc`, F-Z from the tail record and the new records'
  fit) and the crash condition (`crashOk_snoc`: no cut pending, so no alternative layout);
* `dirKeysOk_append`, `absentNone_append`, `dirsAvoid_append`: unchanged but for the history;
* `tailBound_snoc`: the record boundary is a prefix of the tail's records, which only grow;
* `absLe_append`, `walKeysInArea_append`, `walDurLe_append`: the ghost state's facts.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.TailSyncPure

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Fs WalEnc

section pure
variable [GooseExts]

/-- **The WAL state after `dir`'s append of `o`** (`d` its WAL before). -/
def walAppS (s : AbsDiskState) (dir : GoString) (d : WalDur) (o : WalOpG WalEnt) : AbsDiskState :=
  { s with wal := <[dir := { d with H := d.H ++ [o] }]> s.wal }

theorem walAppS_lookup_ne (s : AbsDiskState) (dir : GoString) (d : WalDur) (o : WalOpG WalEnt)
    {k : GoString} (h : k ≠ dir) : (walAppS s dir d o).wal !! k = s.wal !! k :=
  GMap.lookup_insert_ne _ _ (Ne.symm h)

theorem walAppS_lookup (s : AbsDiskState) (dir : GoString) (d : WalDur) (o : WalOpG WalEnt) :
    (walAppS s dir d o).wal !! dir = some { d with H := d.H ++ [o] } :=
  GMap.lookup_insert _ _ _

/-- The last list of a list ending in `L`, at its length. -/
theorem getD_append_last {α : Type} (A : List (List α)) (L : List α) (k : Nat) (hk : A.length = k) :
    (A ++ [L]).getD k [] = L := by
  subst hk; simp

/-- **The record boundary after an appended operation**: the tail's records only grow. -/
theorem tailBound_snoc {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay}
    (o : WalOpG WalEnt) (hc : ∀ b ∈ lay.cuts, b ≤ d.H.length) (h : TailBound C Mr d lay) :
    TailBound C Mr { d with H := d.H ++ [o] } lay := by
  obtain ⟨A, L, X, hA, h1, h2, -, -⟩ := segRecs_snoc_op C Mr d lay.cuts o hc
  obtain ⟨jE, hj, hf⟩ := h
  rw [h1, getD_append_last A L _ hA] at hj hf
  refine ⟨jE, ?_, ?_⟩
  · rw [h2, getD_append_last A _ _ hA, List.length_append]; omega
  · rw [h2, getD_append_last A _ _ hA, List.take_append_of_le_length hj]; exact hf

theorem walDurLe_append {d0 d : WalDur} (o : WalOpG WalEnt) (h : walDurLe d0 d) :
    walDurLe { d0 with H := d0.H ++ [o] } { d with H := d.H ++ [o] } := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := h
  exact ⟨by simp [a1], a2, a3, a4, a5, a6, a7, a8⟩

theorem absLe_append {s : AbsDiskState} {dir : GoString} {d : WalDur} (o : WalOpG WalEnt)
    (hd : s.wal !! dir = some d) : absLe s (walAppS s dir d o) := by
  refine ⟨rfl, fun _ h => h, fun k d1 hk => ?_⟩
  by_cases e : k = dir
  · subst e
    rw [hd] at hk; cases hk
    exact ⟨_, walAppS_lookup s k d o, Nat.le_refl _, by simp, id⟩
  · exact ⟨d1, by rw [walAppS_lookup_ne s dir d o e]; exact hk, Nat.le_refl _, Nat.le_refl _, id⟩

theorem walKeysInArea_append {s : AbsDiskState} {dir : GoString} {d : WalDur} (o : WalOpG WalEnt)
    (hd : s.wal !! dir = some d) (h : walKeysInArea s) : walKeysInArea (walAppS s dir d o) := by
  intro k d1 hk
  by_cases e : k = dir
  · subst e; exact h k d hd
  · rw [walAppS_lookup_ne s dir d o e] at hk; exact h k d1 hk

/-- **The WALs after `dir`'s append** (no cut pending: the crash condition without alternative). -/
theorem walsOk_append {C : WalCodec} {Mr : WalMarshal} {R : Roots} {jr : Ino}
    {s : AbsDiskState} {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat} {dir : GoString}
    {d : WalDur} {lay : WalLay} (o : WalOpG WalEnt)
    (hW : WalsOk C Mr R jr s Ls cl n) (hd : s.wal !! dir = some d) (hl : Ls !! dir = some lay)
    (hZ : TailZeros lay)
    (hfit : RecsFit C (recsOfSegs C Mr d.metadata
      (segsOf (histM { d with H := d.H ++ [o] }) lay.cuts)))
    (hok : CrashOk C Mr d lay cl n) :
    WalsOk C Mr R jr (walAppS s dir d o) Ls cl n := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hW
  refine ⟨fun dir' d' hd' => ?_, fun dir' hn => ?_, h3, h4, fun dir' nm hin hn => ?_, h6⟩
  · by_cases e : dir' = dir
    · subst e
      rw [walAppS_lookup] at hd'; cases hd'
      obtain ⟨lay1, nm, hj, hl1, hA, hjr, hnm, hc, habs, -⟩ := h1 dir' d hd
      have e : lay1 = lay := by rw [hl] at hl1; exact (Option.some.inj hl1).symm
      subst e
      exact ⟨lay1, nm, hj, hl1, hA, hjr, hnm, hc, walAbsD_snoc o habs (fun _ => hZ) hfit,
        crashOkW_of_crashOk (crashOk_snoc o hok)⟩
    · rw [walAppS_lookup_ne s dir d o e] at hd'
      exact h1 dir' d' hd'
  · have e : dir' ≠ dir := by rintro rfl; rw [walAppS_lookup] at hn; cases hn
    rw [walAppS_lookup_ne s dir d o e] at hn
    exact h2 dir' hn
  · have e : dir' ≠ dir := by rintro rfl; rw [walAppS_lookup] at hn; cases hn
    rw [walAppS_lookup_ne s dir d o e] at hn
    exact h5 dir' nm hin hn

/-- **The directory keys after `dir`'s append** (any pending cut). -/
theorem dirKeysOk_append {C : WalCodec} {Mr : WalMarshal} {jr : Ino}
    {s : AbsDiskState} {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat}
    {K : GMap GoString (Ino × List GoString)} {c : Option GoString} {dir : GoString}
    {d : WalDur} (o : WalOpG WalEnt) (hd : s.wal !! dir = some d)
    (h : DirKeysOk C Mr jr s Ls cl n K c) :
    DirKeysOk C Mr jr (walAppS s dir d o) Ls cl n K c := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, fun dir' d' lay' hd' hl' hc => ?_, h3⟩
  by_cases e : dir' = dir
  · subst e
    rw [walAppS_lookup] at hd'; cases hd'
    exact crashOkA_snoc o (h2 dir' d lay' hd hl' hc)
  · rw [walAppS_lookup_ne s dir d o e] at hd'
    exact h2 dir' d' lay' hd' hl' hc

theorem absentNone_append {s : AbsDiskState} {jr : Ino} {cl : List Claim} {n : Nat}
    {dir : GoString} {d : WalDur} (o : WalOpG WalEnt) (h : AbsentNone s jr cl n) :
    AbsentNone (walAppS s dir d o) jr cl n := by
  intro dir' nm hin hn
  have e : dir' ≠ dir := by rintro rfl; rw [walAppS_lookup] at hn; cases hn
  rw [walAppS_lookup_ne s dir d o e] at hn
  exact h dir' nm hin hn

theorem dirsAvoid_append {R : Roots} {s : AbsDiskState} {jr : Ino} {dir : GoString} {d : WalDur}
    (o : WalOpG WalEnt) (h : DirsAvoid R jr s) : DirsAvoid R jr (walAppS s dir d o) := h

end pure

end WalFs
end EtcdGrove
end Perennial

end
