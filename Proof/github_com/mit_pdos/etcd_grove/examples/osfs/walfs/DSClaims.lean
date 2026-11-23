/-
**Spike** (`notes/fs-interp-state-determined.md`, §5): `dirswap`'s crash facts (`SafeH`, `MonoH`,
stated over whole histories and `TreeCrashed`) restated over the shared view's claims, to check that
they need no reshaping.

The region is the claim on `wal`/`wal.tmp` of the root `j` and, once `wal` can name a directory `J`,
the claim on `J`'s `seg`. The facts quantify over every kept set `K` closed under the region's
`Follows` (`RegionCut`), the set a crash's `RegionCrashed` hands out, and read each name through
`NamesH.valAfter`. So no prefix argument (`regionCrashed_seq`) is needed here: a step that keeps the
rename keeps every entry its call followed, `seg`'s create among them.

What changes against today: the facts live on the two claims, not on the whole history, so a step
that writes neither `wal` nor the tracked `seg` (the removes of the old `wal.tmp`, `mkdir`, the
create of the new `seg`) leaves them as they are (`dinv_log_other`); the rename is the one step
that changes them (`dinv_rename`); a crash concludes `SafeT` of the tree left (`dinv_crash`); a
new generation's fresh claims start them (`dinv_init`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.walfs.DirSwap
public import GooseLang.Ext.Fs.TreeSharedCoh

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace osfs_walfs
namespace DS

open Fs DSBase

/-! ## Kept sets of a region -/

/-- A kept set closed under the region's `Follows`: `RegionCrashed`'s first clause. -/
def RegionCut (cl : List Claim) (K : Nat → Prop) : Prop :=
  ∀ c ∈ cl, ∀ c' ∈ cl, ∀ x e E y e' E', (x, e, E) ∈ c.2.2.ents → (y, e', E') ∈ c'.2.2.ents →
    K x → y < e.start → K y

theorem regionCut_of_crashed {cl : List Claim} {n : Nat} {m' : Tree} (h : RegionCrashed cl n m') :
    ∃ K, RegionCut cl K ∧ ∀ c ∈ cl, ∀ b, c.2.1.Mem b → m'.entry c.1 b = c.2.2.valAfter c.1 K b :=
  let ⟨K, hc, _, hv⟩ := h; ⟨K, hc, hv⟩

/-- An entry neither kept nor writing `b` leaves `b`'s value after a crash as it was. -/
theorem valAfter_log_skip (h : NamesH) (j : Ino) (K : Nat → Prop) (b : GoString) (x : Nat)
    (e : LogEntry) (c : Ents) (hn : ¬ (K x ∧ e.op.Writes j b)) :
    (h.log x e c).valAfter j K b = h.valAfter j K b := by
  classical
  unfold NamesH.valAfter NamesH.log
  simp only [List.filter_append, List.filter_cons, List.filter_nil]
  rw [if_neg (by simpa using hn), List.append_nil]

theorem valAfter_log_last (h : NamesH) (j : Ino) (K : Nat → Prop) (b : GoString) (x : Nat)
    (e : LogEntry) (c : Ents) (hK : K x) (hw : e.op.Writes j b) :
    (h.log x e c).valAfter j K b = c !! b := by
  classical
  unfold NamesH.valAfter NamesH.log
  simp only [List.filter_append, List.filter_cons, List.filter_nil]
  rw [if_pos (by simp [hK, hw])]
  simp

/-- A fresh claim (nothing logged): every crash leaves its names as the tree it began with. -/
theorem valAfter_init (m : Tree) (j : Ino) (N : NameSet) (K : Nat → Prop) (b : GoString)
    (hb : N.Mem b) : (NamesH.init m j N).valAfter j K b = m.entry j b := by
  unfold NamesH.valAfter NamesH.init
  simp only [List.filter_nil, List.getLast?_nil]
  rw [restrictN_lookup N _ b hb, entsOf_lookup]

/-! ## The region and its facts -/

def wN : NameSet := .only [walB, wtB]
def sN : NameSet := .only [segB]

theorem wN_wal : wN.Mem walB := by simp [wN, NameSet.Mem]
theorem sN_seg : sN.Mem segB := by simp [sN, NameSet.Mem]

/-- The region: `wal`/`wal.tmp` of `j`, and the tracked `seg`, if any. -/
def regionOf (j : Ino) (hw : NamesH) : Option (Ino × NamesH) → List Claim
  | none => [(j, wN, hw)]
  | some (J, hs) => [(j, wN, hw), (J, sN, hs)]

/-- **`SafeT` of every crash keeping `K`**, read through the claims. -/
def DSafeK (j : Ino) (ko : Option Ino) (hw : NamesH) (hsO : Option (Ino × NamesH))
    (K : Nat → Prop) : Prop :=
  (∀ i, hw.valAfter j K walB ≠ some (.file i)) ∧
  (∀ J, hw.valAfter j K walB = some (.dir J) →
    ∃ k hs, hsO = some (J, hs) ∧ ko = some k ∧ hs.valAfter J K segB = some (.file k))

/-- **`MonoH` of every crash keeping `K`**: `wal`, once there, as now. (Its `seg` half is in
`DSafeK`, which tracks `seg` exactly once `wal` can be a directory.) -/
def DMonoK (j : Ino) (hw : NamesH) (K : Nat → Prop) : Prop :=
  hw.valAfter j K walB ≠ none → hw.valAfter j K walB = hw.cur !! walB

/-- **The invariant's facts**, over every kept set closed in the region. -/
def DInv (j : Ino) (ko : Option Ino) (hw : NamesH) (hsO : Option (Ino × NamesH)) : Prop :=
  ∀ K, RegionCut (regionOf j hw hsO) K → DSafeK j ko hw hsO K ∧ DMonoK j hw K

/-- A crash of the region leaves a `SafeT` tree. -/
theorem dinv_crash {j : Ino} {ko : Option Ino} {hw : NamesH} {hsO : Option (Ino × NamesH)}
    {n : Nat} {m' : Tree} (h : DInv j ko hw hsO) (hc : RegionCrashed (regionOf j hw hsO) n m') :
    SafeT j ko m' := by
  obtain ⟨K, hK, hv⟩ := regionCut_of_crashed hc
  have hwal : m'.entry j walB = hw.valAfter j K walB :=
    hv (j, wN, hw) (by cases hsO <;> simp [regionOf]) walB wN_wal
  obtain ⟨⟨h1, h2⟩, -⟩ := h K hK
  refine ⟨fun i => by rw [hwal]; exact h1 i, fun J hJ => ?_⟩
  rw [hwal] at hJ
  obtain ⟨k, hs, rfl, hk, hseg⟩ := h2 J hJ
  refine ⟨k, hk, ?_⟩
  rw [hv (J, sN, hs) (by simp [regionOf]) segB sN_seg]
  exact hseg

/-- A new generation's fresh claims, on a `SafeT` tree, start the facts. -/
theorem dinv_init {j : Ino} {ko : Option Ino} {m : Tree} (h : SafeT j ko m) :
    DInv j ko (NamesH.init m j wN)
      (match m.entry j walB with
       | some (.dir J) => some (J, NamesH.init m J sN)
       | _ => none) := by
  intro K _
  have hw : (NamesH.init m j wN).valAfter j K walB = m.entry j walB := valAfter_init _ _ _ _ _ wN_wal
  refine ⟨⟨fun i => by rw [hw]; exact h.1 i, fun J hJ => ?_⟩, fun _ => ?_⟩
  · rw [hw] at hJ
    obtain ⟨k, hk, hs⟩ := h.2 J hJ
    refine ⟨k, _, by rw [hJ], hk, ?_⟩
    rw [valAfter_init _ _ _ _ _ sN_seg]; exact hs
  · rw [hw]; unfold NamesH.init; rw [restrictN_lookup _ _ _ wN_wal, entsOf_lookup]

/-- A kept set closed in a region whose first claim logged one more entry is closed in the region
before it. -/
theorem regionCut_log {j : Ino} {hw : NamesH} {hsO : Option (Ino × NamesH)} {x : Nat}
    {e : LogEntry} {c : Ents} {K : Nat → Prop}
    (hK : RegionCut (regionOf j (hw.log x e c) hsO) K) : RegionCut (regionOf j hw hsO) K := by
  have sub : ∀ cc ∈ regionOf j hw hsO, ∃ cc' ∈ regionOf j (hw.log x e c) hsO,
      cc'.1 = cc.1 ∧ ∀ xe ∈ cc.2.2.ents, xe ∈ cc'.2.2.ents := by
    intro cc hcc
    cases hsO with
    | none =>
      simp only [regionOf, List.mem_singleton] at hcc; subst hcc
      exact ⟨(j, wN, hw.log x e c), by simp [regionOf], rfl, fun xe hxe => by simp [NamesH.log, hxe]⟩
    | some p =>
      simp only [regionOf, List.mem_cons, List.mem_nil_iff, or_false] at hcc
      rcases hcc with rfl | rfl
      · exact ⟨(j, wN, hw.log x e c), by simp [regionOf], rfl, fun xe hxe => by simp [NamesH.log, hxe]⟩
      · exact ⟨(p.1, sN, p.2), by simp [regionOf], rfl, fun xe hxe => hxe⟩
  intro c1 hc1 c2 hc2 x' e' E' y e'' E'' hx hy hKx hlt
  obtain ⟨d1, hd1, -, hs1⟩ := sub c1 hc1
  obtain ⟨d2, hd2, -, hs2⟩ := sub c2 hc2
  exact hK d1 hd1 d2 hd2 x' e' E' y e'' E'' (hs1 _ hx) (hs2 _ hy) hKx hlt

/-- **A step writing `wal.tmp` only** (`mkdir`, `rmdir` of `wal.tmp`): the facts stay. -/
theorem dinv_log_other {j : Ino} {ko : Option Ino} {hw : NamesH} {hsO : Option (Ino × NamesH)}
    (h : DInv j ko hw hsO) (x : Nat) (e : LogEntry) (c : Ents) (hnw : ¬ e.op.Writes j walB)
    (hc : c !! walB = hw.cur !! walB) : DInv j ko (hw.log x e c) hsO := by
  intro K hK
  have hv : (hw.log x e c).valAfter j K walB = hw.valAfter j K walB :=
    valAfter_log_skip _ _ _ _ _ _ _ (fun h => hnw h.2)
  obtain ⟨⟨h1, h2⟩, h3⟩ := h K (regionCut_log hK)
  refine ⟨⟨fun i => by rw [hv]; exact h1 i, fun J hJ => h2 J (by rw [← hv]; exact hJ)⟩, ?_⟩
  intro hne
  rw [hv] at hne ⊢
  rw [h3 hne]; simp only [NamesH.log]; exact hc.symm

/-- **The rename of `wal.tmp` (the directory `J`, whose `seg` is the key's file) onto the absent
`wal`**: the facts hold with `J`'s claim tracked. Every entry of `J`'s claim is below the rename's
call's start (`hs.next ≤ e.start`, from `osNames_next` and `CallBegin`), so a crash keeping the
rename keeps them, and leaves `seg` as now (`HistCoh`). -/
theorem dinv_rename {j J k : Ino} {ko : Option Ino} {hw hs : NamesH} (h : DInv j ko hw none)
    (hnone : hw.cur !! walB = none) (x : Nat) (e : LogEntry) (c : Ents)
    (hwr : e.op.Writes j walB) (hc : c !! walB = some (.dir J))
    (hcoh : HistCoh hs J sN) (hseg : hs.cur !! segB = some (.file k)) (hst : hs.next ≤ e.start) :
    DInv j (some k) (hw.log x e c) (some (J, hs)) := by
  intro K hK
  by_cases hKx : K x
  · have hv : (hw.log x e c).valAfter j K walB = some (.dir J) := by
      rw [valAfter_log_last _ _ _ _ _ _ _ hKx hwr, hc]
    have hall : ∀ xe ∈ hs.ents, K xe.1 := by
      intro xe hxe
      exact hK (j, wN, hw.log x e c) (by simp [regionOf]) (J, sN, hs) (by simp [regionOf])
        x e c xe.1 xe.2.1 xe.2.2 (by simp [NamesH.log]) (by simpa using hxe) hKx
        (Nat.lt_of_lt_of_le (hcoh.1 xe hxe) hst)
    refine ⟨⟨fun i => by rw [hv]; simp, fun J' hJ' => ?_⟩, fun _ => ?_⟩
    · rw [hv] at hJ'; cases hJ'
      exact ⟨k, hs, rfl, rfl, by rw [hcoh.2 K hall segB sN_seg, hseg]⟩
    · rw [hv]; simp only [NamesH.log]; exact hc.symm
  · have hv : (hw.log x e c).valAfter j K walB = hw.valAfter j K walB :=
      valAfter_log_skip _ _ _ _ _ _ _ (fun h => hKx h.1)
    have hK0 : RegionCut (regionOf j hw none) K := by
      intro c1 hc1 c2 hc2 x' e' E' y e'' E'' hx hy hKx' hlt
      simp only [regionOf, List.mem_singleton] at hc1 hc2; subst hc1 hc2
      exact hK (j, wN, hw.log x e c) (by simp [regionOf]) (j, wN, hw.log x e c)
        (by simp [regionOf]) x' e' E' y e'' E'' (by simp [NamesH.log, hx])
        (by simp [NamesH.log, hy]) hKx' hlt
    have hnone' : hw.valAfter j K walB = none := by
      by_cases hn : hw.valAfter j K walB = none
      · exact hn
      · exact absurd ((h K hK0).2 hn) (by rw [hnone]; exact hn)
    refine ⟨⟨fun i => by rw [hv, hnone']; simp, fun J' hJ' => ?_⟩, fun hne => ?_⟩
    · rw [hv, hnone'] at hJ'; cases hJ'
    · rw [hv, hnone'] at hne; exact absurd rfl hne

/-- With `wal` absent from every crash, the key does not matter (`ds_deposit`). -/
theorem dinv_rekey {j : Ino} {ko : Option Ino} {hw : NamesH} (h : DInv j ko hw none)
    (hnone : hw.cur !! walB = none) (ko' : Option Ino) : DInv j ko' hw none := by
  intro K hK
  obtain ⟨-, h3⟩ := h K hK
  have hn : hw.valAfter j K walB = none := by
    by_cases hn : hw.valAfter j K walB = none
    · exact hn
    · exact absurd (h3 hn) (by rw [hnone]; exact hn)
  exact ⟨⟨fun i => by rw [hn]; simp, fun J hJ => by rw [hn] at hJ; cases hJ⟩, fun h => absurd hn h⟩

end DS
end osfs_walfs
end EtcdGrove
end Perennial

end
