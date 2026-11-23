/-
**`dirswap`'s crash facts and invariant over the shared view's claims**
(`notes/fs-interp-state-determined.md`, §7.1).

The region is the claim on `wal` of the root `j` and, once `wal` can name a directory `J`, the claim
on `J`'s `seg`. The facts (`DInv`) quantify over every kept set `K` closed under the region's
`Follows` (`RegionCut`), the set a crash's `RegionCrashed` hands out, and read each name through
`NamesH.valAfter`. So no prefix argument (`regionCrashed_seq`) is needed: a step that keeps the
rename keeps every entry its call followed, `seg`'s create among them.

The claim on `wal` is keyed `.only [wal]` (`wO`) until `Create` merges it with the claim on
`wal.tmp` for the rename (`wN`, `wp_osRenameDirS` writes both names of one claim). The facts are
stated over its restriction to `wal` (`NamesH.restrict … wO`), which the merge keeps. A crash
concludes `SafeT` of the tree left (`dinv_crash`, through `regionCrashed_restrict`); a new
generation's fresh claims start the facts (`dinv_init`); the rename onto the absent `wal` is the one
step that changes them (`dinv_rename`); with `wal` absent the key may change (`dinv_rekey`).

The invariant (`dsInv`) holds half of the claim on `wal` (and, once tracked, of `J`'s `seg`), a
ghost variable recording the key, whether the claim is merged and both claims' histories, the facts,
and the invariant's half of the key's file (`keyRes`). The program holds the other halves
(`dsOwn`): every claim and every ghost value is the same on both sides, so opening the invariant
needs no agreement lemma beyond `ghostVar_agree`.
-/
module

public import GooseLang.Ext.Fs.TreeShared
public import GooseLang.Ext.Fs.TreeSharedCoh
public import GooseLang.Ext.Fs.CrashRegion
public import Perennial.Ghost.GhostVar
public import Perennial.Std.Namespaces

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace osfs_walfs

namespace DSBase

open Fs

/-- The data of a committed segment (`newData`). -/
def dataC : List w8 := [W8 0xde, W8 0xad, W8 0xbe, W8 0xef, W8 0x01, W8 0x23, W8 0x45, W8 0x67]

end DSBase

namespace DS

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs DSBase

/-! ## The names -/

def walB : GoString := go!"wal"
def wtB : GoString := go!"wal.tmp"
def segB : GoString := go!"seg"

theorem walB_ok : NameOk walB := by decide
theorem wtB_ok : NameOk wtB := by decide
theorem segB_ok : NameOk segB := by decide
theorem wt_ne_wal : wtB ≠ walB := by decide
theorem seg_ne_wal : segB ≠ walB := by decide
theorem seg_ne_wt : segB ≠ wtB := by decide

/-! ## What every crash must be -/

/-- **The tree a boot may find**, in the directory `j`: `wal` no file; if `wal` is a directory, its
`seg` the file of the key `ko`. -/
def SafeT (j : Ino) (ko : Option Ino) (m : Tree) : Prop :=
  (∀ i, m.entry j walB ≠ some (.file i)) ∧
  (∀ J, m.entry j walB = some (.dir J) → ∃ k, ko = some k ∧ m.entry J segB = some (.file k))

theorem safeT_none {j : Ino} {ko : Option Ino} {m : Tree} (h : m.entry j walB = none) :
    SafeT j ko m :=
  ⟨fun i => by rw [h]; simp, fun J hJ => by rw [h] at hJ; cases hJ⟩

/-- With the key's file named nowhere, the key `none` will do. -/
theorem safeT_unnamed {j k : Ino} {m : Tree} (h : SafeT j (some k) m) (hn : ¬ Named m k) :
    SafeT j none m := by
  refine ⟨h.1, fun J hJ => ?_⟩
  obtain ⟨k', hk', hs⟩ := h.2 J hJ
  cases hk'
  exact absurd ⟨J, segB, hs⟩ hn

/-- What a crash may leave of the segment's file: no file, or the data at 0. -/
def DataGood (fo : Option OsFile) : Prop :=
  ∀ f, fo = some f → 8 ≤ f.size ∧ ∀ b < 8, f.contents[b]? = dataC[b]?

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

/-! ## Restricting a claim's history -/

/-- A claim's history restricted to some of its names reads them as it does. -/
theorem valAfter_restrict (h : NamesH) (j : Ino) (M : NameSet) (K : Nat → Prop) (b : GoString)
    (hb : M.Mem b) : (h.restrict j M).valAfter j K b = h.valAfter j K b := by
  classical
  unfold NamesH.valAfter NamesH.restrict
  simp only [List.filter_map, Function.comp_def, List.filter_filter]
  rw [List.filter_congr (q := fun xe => decide (K xe.1 ∧ xe.2.1.op.Writes j b))
    (fun xe _ => by
      by_cases hw : xe.2.1.op.Writes j b
      · simp only [hw, and_true, decide_eq_decide]
        have hex : ∃ b, M.Mem b ∧ xe.2.1.op.Writes j b := ⟨b, hb, hw⟩
        simp only [decide_eq_true hex, Bool.and_true]
      · simp [hw])]
  rw [List.getLast?_map]
  cases (h.ents.filter (fun xe => decide (K xe.1 ∧ xe.2.1.op.Writes j b))).getLast? with
  | none => simp [restrictN_lookup _ _ _ hb]
  | some xe => simp [restrictN_lookup _ _ _ hb]

theorem restrict_cur (h : NamesH) (j : Ino) (M : NameSet) (b : GoString) (hb : M.Mem b) :
    (h.restrict j M).cur !! b = h.cur !! b := restrictN_lookup _ _ _ hb

theorem mem_restrict_ents {h : NamesH} {j : Ino} {M : NameSet} {x : Nat} {e : LogEntry} {E : Ents}
    (hx : (x, e, E) ∈ (h.restrict j M).ents) : ∃ E', (x, e, E') ∈ h.ents := by
  unfold NamesH.restrict at hx
  simp only [List.mem_map, List.mem_filter] at hx
  obtain ⟨⟨x', e', E'⟩, ⟨hm, -⟩, he⟩ := hx
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, -⟩ := he
  exact ⟨E', hm⟩

/-- A step writing one of the names restricted to: the restriction logs it. -/
theorem restrict_log_writes (h : NamesH) (j : Ino) (M : NameSet) (x : Nat) (e : LogEntry) (c : Ents)
    (b : GoString) (hb : M.Mem b) (hw : e.op.Writes j b) :
    (h.log x e c).restrict j M = (h.restrict j M).log x e (restrictN M c) := by
  classical
  unfold NamesH.restrict NamesH.log
  simp only [List.filter_append, List.filter_cons, List.filter_nil, List.map_append]
  rw [if_pos (by simpa using ⟨b, hb, hw⟩)]
  rfl

theorem restrict_restrict (h : NamesH) (j : Ino) (M : NameSet) :
    ((h.restrict j M).restrict j M).cur = (h.restrict j M).cur := by
  unfold NamesH.restrict
  exact restrictN_restrictN M M h.cur (fun _ hb => hb)

/-- **A crash of a region, with one claim restricted to some of its names**, is a crash of the
region so restricted. -/
theorem regionCrashed_restrict {c : Claim} {rest : List Claim} {n : Nat} {m' : Tree} (M : NameSet)
    (hM : ∀ b, M.Mem b → c.2.1.Mem b) (h : RegionCrashed (c :: rest) n m') :
    RegionCrashed ((c.1, M, c.2.2.restrict c.1 M) :: rest) n m' := by
  obtain ⟨K, h1, h2, h3⟩ := h
  -- each claim of the restricted region has its entries among one claim's of the region
  have back : ∀ d ∈ ((c.1, M, c.2.2.restrict c.1 M) :: rest), ∃ d' ∈ (c :: rest),
      ∀ x e E, (x, e, E) ∈ d.2.2.ents → ∃ E', (x, e, E') ∈ d'.2.2.ents := by
    intro d hd
    rcases List.mem_cons.1 hd with rfl | hd
    · exact ⟨c, List.mem_cons_self .., fun x e E hx => mem_restrict_ents hx⟩
    · exact ⟨d, List.mem_cons_of_mem _ hd, fun x e E hx => ⟨E, hx⟩⟩
  refine ⟨K, fun d hd d' hd' x e E y e' E' hx hy hK hlt => ?_, fun d hd y e E hy hn => ?_,
    fun d hd b hb => ?_⟩
  · obtain ⟨d1, hd1, hb1⟩ := back d hd
    obtain ⟨d2, hd2, hb2⟩ := back d' hd'
    obtain ⟨E1, hx1⟩ := hb1 x e E hx
    obtain ⟨E2, hy2⟩ := hb2 y e' E' hy
    exact h1 d1 hd1 d2 hd2 x e E1 y e' E2 hx1 hy2 hK hlt
  · obtain ⟨d1, hd1, hb1⟩ := back d hd
    obtain ⟨E1, hy1⟩ := hb1 y e E hy
    exact h2 d1 hd1 y e E1 hy1 hn
  · rcases List.mem_cons.1 hd with rfl | hd
    · show m'.entry c.1 b = (c.2.2.restrict c.1 M).valAfter c.1 K b
      rw [valAfter_restrict _ _ _ _ _ hb]
      exact h3 c (List.mem_cons_self ..) b (hM b hb)
    · exact h3 d (List.mem_cons_of_mem _ hd) b hb

/-! ## The region and its facts -/

/-- The claim on `wal` alone, and merged with `wal.tmp`'s. -/
abbrev wO : NameSet := .only [walB]
abbrev wN : NameSet := .only [walB, wtB]
abbrev sN : NameSet := .only [segB]

theorem wO_wal : wO.Mem walB := by simp [wO, NameSet.Mem]
theorem wN_wal : wN.Mem walB := by simp [wN, NameSet.Mem]
theorem wN_wt : wN.Mem wtB := by simp [wN, NameSet.Mem]
theorem sN_seg : sN.Mem segB := by simp [sN, NameSet.Mem]

/-- The key of the claim on `wal`: alone, or merged (`mg`). -/
abbrev wKey : Bool → NameSet
  | false => wO
  | true => wN

theorem wKey_wal (mg : Bool) : (wKey mg).Mem walB := by cases mg <;> simp [wKey, wO_wal, wN_wal]

theorem wO_sub (mg : Bool) : ∀ b, wO.Mem b → (wKey mg).Mem b := by
  intro b hb
  simp only [wO, NameSet.Mem, List.mem_singleton] at hb
  subst hb; exact wKey_wal mg

/-- The region: `wal` of `j`, and the tracked `seg`, if any. -/
def regionOf (j : Ino) (hw : NamesH) : Option (Ino × NamesH) → List Claim
  | none => [(j, wO, hw)]
  | some (J, hs) => [(j, wO, hw), (J, sN, hs)]

/-- **`SafeT` of every crash keeping `K`**, read through the claims. -/
def DSafeK (j : Ino) (ko : Option Ino) (hw : NamesH) (hsO : Option (Ino × NamesH))
    (K : Nat → Prop) : Prop :=
  (∀ i, hw.valAfter j K walB ≠ some (.file i)) ∧
  (∀ J, hw.valAfter j K walB = some (.dir J) →
    ∃ k hs, hsO = some (J, hs) ∧ ko = some k ∧ hs.valAfter J K segB = some (.file k))

/-- **Every crash keeping `K` has `wal` as now, once there.** (Its `seg` half is in `DSafeK`, which
tracks `seg` exactly once `wal` can be a directory.) -/
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
    hv (j, wO, hw) (by cases hsO <;> simp [regionOf]) walB wO_wal
  obtain ⟨⟨h1, h2⟩, -⟩ := h K hK
  refine ⟨fun i => by rw [hwal]; exact h1 i, fun J hJ => ?_⟩
  rw [hwal] at hJ
  obtain ⟨k, hs, rfl, hk, hseg⟩ := h2 J hJ
  refine ⟨k, hk, ?_⟩
  rw [hv (J, sN, hs) (by simp [regionOf]) segB sN_seg]
  exact hseg

/-- The tracked `seg`'s claim of a fresh generation. -/
def initSeg (m : Tree) (j : Ino) : Option (Ino × NamesH) :=
  match m.entry j walB with
  | some (.dir J) => some (J, NamesH.init m J sN)
  | _ => none

/-- A new generation's fresh claims, on a `SafeT` tree, start the facts. -/
theorem dinv_init {j : Ino} {ko : Option Ino} {m : Tree} (h : SafeT j ko m) :
    DInv j ko (NamesH.init m j wO) (initSeg m j) := by
  intro K _
  have hw : (NamesH.init m j wO).valAfter j K walB = m.entry j walB :=
    valAfter_init _ _ _ _ _ wO_wal
  refine ⟨⟨fun i => by rw [hw]; exact h.1 i, fun J hJ => ?_⟩, fun _ => ?_⟩
  · rw [hw] at hJ
    obtain ⟨k, hk, hs⟩ := h.2 J hJ
    refine ⟨k, _, by unfold initSeg; rw [hJ], hk, ?_⟩
    rw [valAfter_init _ _ _ _ _ sN_seg]; exact hs
  · rw [hw]; unfold NamesH.init; rw [restrictN_lookup _ _ _ wO_wal, entsOf_lookup]

/-- **The rename of `wal.tmp` (the directory `J`, whose `seg` is the key's file) onto the absent
`wal`**: the facts hold with `J`'s claim tracked. Every entry of `J`'s claim is below the rename's
call's start (`hs.next ≤ e.start`, from `osNames_next` and the call's begin), so a crash keeping
the rename keeps them, and leaves `seg` as now (`HistCoh`). -/
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
      exact hK (j, wO, hw.log x e c) (by simp [regionOf]) (J, sN, hs) (by simp [regionOf])
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
      exact hK (j, wO, hw.log x e c) (by simp [regionOf]) (j, wO, hw.log x e c)
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

/-! ## A fresh generation's claims -/

theorem namesOf_nil (m : Tree) (j : Ino) (N : NameSet) : namesOf (m, []) j N = NamesH.init m j N := by
  unfold namesOf NamesH.init
  simp [Hist.now, Hist.ops, replay]

theorem init_restrict (m : Tree) (j : Ino) (N : NameSet) :
    (NamesH.init m j N).restrict j N = NamesH.init m j N := by
  unfold NamesH.init NamesH.restrict
  simp only [List.filter_nil, List.map_nil, restrictN_restrictN N N _ (fun _ hb => hb)]

/-- The directory a name of `j` names, if any. -/
def dirOf (m : Tree) (j : Ino) (b : GoString) : Option Ino :=
  match m.entry j b with
  | some (.dir J) => some J
  | _ => none

theorem dirOf_some {m : Tree} {j J : Ino} {b : GoString} (h : dirOf m j b = some J) :
    m.entry j b = some (.dir J) := by
  unfold dirOf at h
  split at h
  · cases h; assumption
  · cases h

theorem initSeg_eq (m : Tree) (j : Ino) :
    initSeg m j = (dirOf m j walB).map (fun J => (J, NamesH.init m J sN)) := by
  unfold initSeg dirOf
  split <;> rfl

/-- The directories a fresh generation's program needs: the root `j`, `wal`'s and `wal.tmp`'s
(when directories), distinct and in the tree. -/
theorem dirs_ok {R : Roots} {m : Tree} (hwf : TreeWf R m) {r : GoString} {j : Ino}
    (hr : (r, j) ∈ R) :
    j ∈ m ∧ (∀ J, dirOf m j walB = some J → J ∈ m ∧ J ≠ j) ∧
      (∀ J, dirOf m j wtB = some J → J ∈ m ∧ J ≠ j ∧ dirOf m j walB ≠ some J) := by
  refine ⟨hwf.1 j (.root r j hr), fun J hJ => ?_, fun J hJ => ?_⟩
  · have he := dirOf_some hJ
    exact ⟨(hwf.2.2.1 j walB _ he).2 J (by simp [Node.dirIno]), fun h => hwf.2.2.2.1 j walB J he r (h ▸ hr)⟩
  · have he := dirOf_some hJ
    refine ⟨(hwf.2.2.1 j wtB _ he).2 J (by simp [Node.dirIno]), fun h => hwf.2.2.2.1 j wtB J he r (h ▸ hr),
      fun h => ?_⟩
    exact wt_ne_wal (hwf.2.2.2.2 j wtB j walB _ he (dirOf_some h)).2

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

/-- A whole `.except []` claim of each directory of `o`. -/
def optClaim (V : Hist) : Option Ino → IProp GF
  | none => iprop(emp)
  | some J => osNames (L := L) J (.except []) (DFrac.own 1) (namesOf V J (.except []))

/-- `l` without `o`'s directory. -/
def eraseOpt (l : List Ino) : Option Ino → List Ino
  | none => l
  | some J => l.erase J

theorem bigSepL_take_opt (V : Hist) (l : List Ino) (o : Option Ino) (ho : ∀ J, o = some J → J ∈ l) :
    ([∗list] J ∈ l, osNames (L := L) J (.except []) (DFrac.own 1) (namesOf V J (.except []))) ⊢
      optClaim (L := L) V o ∗
        [∗list] J ∈ eraseOpt l o,
          osNames (L := L) J (.except []) (DFrac.own 1) (namesOf V J (.except [])) := by
  cases o with
  | none => unfold optClaim eraseOpt; iintro H; isplitr; · iempintro
            iexact H
  | some J =>
    unfold optClaim eraseOpt
    refine (BigSepL.bigSepL_perm (List.perm_cons_erase (ho J rfl))).1.trans ?_
    exact BigSepL.bigSepL_cons.1

theorem mem_erase_opt {l : List Ino} {o : Option Ino} {J : Ino} (h : J ∈ l)
    (hne : o ≠ some J) : J ∈ eraseOpt l o := by
  cases o with
  | none => exact h
  | some J' => unfold eraseOpt; exact (List.mem_erase_of_ne (fun e => hne (by rw [e]))).2 h

/-- One name's claim taken out of an `.except X` claim of a fresh generation. -/
theorem osNames_take1 (R : Roots) (V : Hist) (j : Ino) (X : List GoString) (b : GoString)
    (hb : b ∉ X) {E : CoPset} (hE : ↑osShN ⊆ E) :
    ⊢ osSharedInv (L := L) R -∗
      osNames (L := L) j (.except X) (DFrac.own 1) (namesOf V j (.except X)) ={E}=∗
      osNames (L := L) j (.only [b]) (DFrac.own 1) (namesOf V j (.only [b])) ∗
      osNames (L := L) j (.except (X ++ [b])) (DFrac.own 1) (namesOf V j (.except (X ++ [b]))) := by
  iintro #Hsh H
  imod osNames_split R j (.except X) [b] _ hE $$ Hsh H with ⟨Hb, Hr⟩
  have hi : (NameSet.except X).inter [b] = .only [b] := by
    simp only [NameSet.inter, List.filter_cons, List.filter_nil]
    rw [if_pos (decide_eq_true hb)]
  have hd : (NameSet.except X).diff [b] = .except (X ++ [b]) := rfl
  rw [namesOf_restrict V j (.except X) ((NameSet.except X).inter [b]) (fun c hc => by
      rw [hi] at hc
      simp only [NameSet.Mem, List.mem_singleton] at hc ⊢
      subst hc; exact hb),
    namesOf_restrict V j (.except X) ((NameSet.except X).diff [b]) (fun c hc => by
      simp only [NameSet.diff, NameSet.Mem, List.mem_append, not_or] at hc ⊢
      exact hc.1), hi, hd]
  imodintro
  iframe Hb Hr

/-! ## The invariant -/

def dsN : Namespace := nroot .@ "dirswap"

theorem dsN_disj : ↑osN ⊆ (⊤ : CoPset) \ ↑dsN := mask_ndot_ne' nroot "osfs" "dirswap" (by decide)

theorem dsN_shN : ↑osShN ⊆ (⊤ : CoPset) \ ↑dsN :=
  mask_ndot_ne' nroot "osfsShared" "dirswap" (by decide)

/-- The invariant's half of the segment's file of the key `ko`: of its `OsMeta` and bytes, every
crash of which is `DataGood`. -/
def keyRes : Option Ino → IProp GF
  | none => iprop(emp)
  | some k => iprop(∃ (m : OsMeta) (bs : List ByteG),
      osMeta (L := L) k (DFrac.own (1 : Qp).half) m ∗
      osBytes (L := L) k 0 (DFrac.own (1 : Qp).half) bs ∗
      ⌜∀ fo, FileCrashedR m [(0, DFrac.own (1 : Qp).half, bs)] fo → DataGood fo⌝)

instance keyRes_timeless (ko : Option Ino) : Timeless (keyRes (L := L) ko) := by
  cases ko <;> unfold keyRes <;> unfold osMeta osBytes bytesG <;> infer_instance

/-- The segment's file of the key `ko` as a generation starts with it: `DataGood`. -/
def startFile : Option Ino → IProp GF
  | none => iprop(emp)
  | some k => iprop(∃ f : OsFile, ⌜DataGood (some f)⌝ ∗ osFileStart (L := L) k f)

/-- The tracked `seg`'s claim, at the fraction `q`. -/
def jcl (q : Qp) : Option (Ino × NamesH) → List (Claim × DFrac)
  | none => []
  | some (J, hs) => [((J, sN, hs), DFrac.own q)]

theorem jcl_halves (hsO : Option (Ino × NamesH)) :
    osClaims L (jcl 1 hsO) ⊣⊢ osClaims L (jcl (1 : Qp).half hsO) ∗ osClaims L (jcl (1 : Qp).half hsO) := by
  cases hsO with
  | none => unfold osClaims jcl; simp only [BigSepL.bigSepL_nil]; exact sep_emp.symm
  | some p =>
    obtain ⟨J, hs⟩ := p
    unfold osClaims jcl
    have h := osNames_frac (L := L) J sN (1 : Qp).half (1 : Qp).half hs
    rw [Qp.half_add_half] at h
    constructor
    · iintro H
      icases BigSepL.bigSepL_singleton.1 $$ H with H
      icases h.1 $$ H with ⟨A, B⟩
      isplitl [A]
      · iapply BigSepL.bigSepL_singleton.2; iexact A
      · iapply BigSepL.bigSepL_singleton.2; iexact B
    · iintro ⟨A, B⟩
      icases BigSepL.bigSepL_singleton.1 $$ A with A
      icases BigSepL.bigSepL_singleton.1 $$ B with B
      iapply BigSepL.bigSepL_singleton.2
      iapply h.2; iframe A B

/-- **One side's half** (the invariant's or the program's): the ghost variable, half of the claim
on `wal`, half of the tracked `seg`'s. -/
def dsHalf (j : Ino) (γ : GName) (ko : Option Ino) (mg : Bool) (hw : NamesH)
    (hsO : Option (Ino × NamesH)) : IProp GF :=
  iprop(ghostVar γ (1 : Qp).half (ko, mg, hw, hsO) ∗
    osNames (L := L) j (wKey mg) (DFrac.own (1 : Qp).half) hw ∗ osClaims L (jcl (1 : Qp).half hsO))

/-- **The crash invariant** of the root directory `j`. -/
def dsInv (j : Ino) (γ : GName) : IProp GF :=
  inv dsN iprop(∃ (ko : Option Ino) (mg : Bool) (hw : NamesH) (hsO : Option (Ino × NamesH)),
    dsHalf (L := L) j γ ko mg hw hsO ∗ ⌜DInv j ko (hw.restrict j wO) hsO⌝ ∗ keyRes (L := L) ko)

instance dsInv_persistent (j : Ino) (γ : GName) : Persistent (dsInv (L := L) j γ) := by
  unfold dsInv; infer_instance

/-- The invariant allocated, with the program's half. -/
theorem ds_alloc (j : Ino) (ko : Option Ino) (mg : Bool) (hw : NamesH) (hsO : Option (Ino × NamesH))
    (hD : DInv j ko (hw.restrict j wO) hsO) (E : CoPset) :
    ⊢ osNames (L := L) j (wKey mg) (DFrac.own 1) hw -∗ osClaims L (jcl 1 hsO) -∗ keyRes (L := L) ko
      ={E}=∗ ∃ γ, dsInv (L := L) j γ ∗ dsHalf (L := L) j γ ko mg hw hsO := by
  iintro Hw Hs Hk
  imod ghostVar_alloc (GF := GF) (ko, mg, hw, hsO) with ⟨%γ, Hv⟩
  icases (ghostVar_split_half γ 1 (ko, mg, hw, hsO)).1 $$ Hv with ⟨Hv1, Hv2⟩
  have h := osNames_frac (L := L) j (wKey mg) (1 : Qp).half (1 : Qp).half hw
  rw [Qp.half_add_half] at h
  icases h.1 $$ Hw with ⟨Hw1, Hw2⟩
  icases (jcl_halves (L := L) hsO).1 $$ Hs with ⟨Hs1, Hs2⟩
  imod inv_alloc dsN E iprop(∃ (ko : Option Ino) (mg : Bool) (hw : NamesH)
      (hsO : Option (Ino × NamesH)), dsHalf (L := L) j γ ko mg hw hsO ∗
      ⌜DInv j ko (hw.restrict j wO) hsO⌝ ∗ keyRes (L := L) ko) $$ [Hv1 Hw1 Hs1 Hk] with #Hinv
  · inext; iexists ko, mg, hw, hsO; unfold dsHalf; iframe Hv1 Hw1 Hs1 Hk; ipureintro; exact hD
  imodintro
  iexists γ
  isplitr
  · unfold dsInv; iexact Hinv
  unfold dsHalf; iframe Hv2 Hw2 Hs2

/-- **A fresh generation's start**: from the tree's resources (`osShared`, nothing logged) on a
`SafeT` tree, the invariant with the program's half, and the whole claims the program changes:
`wal.tmp`'s, and the `.except []` claim of `wal.tmp`'s directory. -/
theorem ds_start (R : Roots) (r : GoString) (j : Ino) (hr : (r, j) ∈ R) (m : Tree)
    (hwf : TreeWf R m) (ko : Option Ino) (hs : SafeT j ko m) (E : CoPset) (hE : ↑osShN ⊆ E) :
    ⊢ osShared (L := L) R (m, []) -∗ keyRes (L := L) ko ={E}=∗
      ∃ γ, dsInv (L := L) j γ ∗ dsHalf (L := L) j γ ko false (NamesH.init m j wO) (initSeg m j) ∗
        osNames (L := L) j (.only [wtB]) (DFrac.own 1) (NamesH.init m j (.only [wtB])) ∗
        optClaim (L := L) (m, []) (dirOf m j wtB) ∗
        osSharedInv (L := L) R ∗ osAboveInv (L := L) ∗ osCallPerms (L := L) R ∗ osLogLb (L := L) 0 := by
  obtain ⟨hj, hW, hT⟩ := dirs_ok hwf hr
  have hnow : Hist.now ((m, []) : Hist) = m := by simp [Hist.now, Hist.ops, replay]
  have mem : ∀ J, J ∈ m → J ∈ dirsOf (m, []) := fun J h => by
    show J ∈ (GMap.toList (Hist.now ((m, []) : Hist))).map (·.1)
    rw [hnow]
    cases he : m !! J with
    | none => have := (GMap.mem_iff _ _).1 h; rw [he] at this; cases this
    | some d => exact List.mem_map.2 ⟨(J, d), (GMap.mem_toList _ _ _).2 he, rfl⟩
  unfold osShared
  iintro ⟨#Hsh, #Hab, Hperm, Hlb, Hall⟩ Hk
  -- the root's claim
  icases (BigSepL.bigSepL_perm (List.perm_cons_erase (mem j hj))).1 $$ Hall with Hall
  icases BigSepL.bigSepL_cons.1 $$ Hall with ⟨Hj, Hall⟩
  -- `wal`'s directory's
  ihave Hall := bigSepL_take_opt (L := L) (m, []) _ (dirOf m j walB) (fun J hJ =>
    (List.mem_erase_of_ne (hW J hJ).2).2 (mem J (hW J hJ).1)) $$ Hall
  icases Hall with ⟨HW, Hall⟩
  -- `wal.tmp`'s directory's
  ihave Hall := bigSepL_take_opt (L := L) (m, []) _ (dirOf m j wtB) (fun J hJ =>
    mem_erase_opt ((List.mem_erase_of_ne (hT J hJ).2.1).2 (mem J (hT J hJ).1))
      (fun h => (hT J hJ).2.2 h)) $$ Hall
  icases Hall with ⟨HT, -⟩
  -- the root's claim split
  imod osNames_take1 (L := L) R (m, []) j [] walB (by simp) hE $$ Hsh Hj with ⟨Hw, Hj⟩
  rw [List.nil_append]
  imod osNames_take1 (L := L) R (m, []) j [walB] wtB (by decide) hE $$ Hsh Hj with ⟨Ht, -⟩
  -- `wal`'s directory's claim: its `seg`
  ihave Hs : |={E}=> osClaims L (jcl 1 (initSeg m j)) $$ [HW]
  · rw [initSeg_eq]
    cases hd : dirOf m j walB with
    | none => unfold optClaim; iclear HW; unfold osClaims; simp only [Option.map, jcl]
              imodintro; iapply BigSepL.bigSepL_nil.2; iempintro
    | some J =>
      unfold optClaim
      simp only [hd]
      imod osNames_take1 (L := L) R (m, []) J [] segB (by simp) hE $$ Hsh HW with ⟨HS, -⟩
      simp only [Option.map, jcl]
      unfold osClaims
      imodintro
      iapply BigSepL.bigSepL_singleton.2
      rw [namesOf_nil]
      iexact HS
  imod Hs
  rw [namesOf_nil, namesOf_nil]
  have hD := dinv_init hs
  rw [← init_restrict m j wO] at hD
  imod ds_alloc (L := L) j ko false (NamesH.init m j wO) (initSeg m j) hD E $$ Hw Hs Hk
    with ⟨%γ, Hinv, Hh⟩
  imodintro
  iexists γ
  iframe Hinv Hh Ht HT Hsh Hab Hperm
  simp only [List.length_nil]
  iexact Hlb

end res

end DS
end osfs_walfs
end EtcdGrove
end Perennial

end
