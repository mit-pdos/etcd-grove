/-
**`segdir`'s crash facts over the shared view's claims** (`notes/fs-interp-state-determined.md`, §7).

The region is one claim, on `seg` and `seg.tmp` of the root `j` (`bN`). The facts (`BInv`) quantify
over every kept set `K` closed under the claim's `Follows` (`RegionCut`) and read each name through
`NamesH.valAfter`: neither name a directory, `seg` nothing or the key's file, and `seg`, once
something in a crash, as it is now (so absent now, it is absent from every crash). A crash concludes
`SafeT` of the tree left (`binv_crash`); a generation's fresh claim starts the facts (`binv_init`); a
step writing `seg.tmp` only, to no directory, keeps them (`binv_tmp`); with `seg` absent the key may
change (`binv_rekey`); the rename of `seg.tmp` (the key's file) onto the absent `seg` keeps them
(`binv_rename`).

The names, the data and `SafeT` are here, in `osfs_walfs`, as the top-level statements name them.
-/
module

public import GooseLang.Ext.Fs.CrashRegion
public import GooseLang.Ext.Fs.TreeSharedCreateN
public import Proof.os.UnlinkN
public import Proof.os.CrashFile
public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.walfs.DSClaims

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace osfs_walfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

/-! ## The names and the data -/

def segB : GoString := go!"seg"
def tmpB : GoString := go!"seg.tmp"

theorem segB_ok : NameOk segB := by decide
theorem tmpB_ok : NameOk tmpB := by decide
theorem tmp_ne_seg : tmpB ≠ segB := by decide

/-- The data of a committed segment (`newData`). -/
def dataC : List w8 := [W8 0xde, W8 0xad, W8 0xbe, W8 0xef, W8 0x01, W8 0x23, W8 0x45, W8 0x67]

/-- What a crash may leave of the file `seg` names: no file, or the data at 0. -/
def DataGood (fo : Option OsFile) : Prop :=
  ∀ f, fo = some f → 8 ≤ f.size ∧ ∀ b < 8, f.contents[b]? = dataC[b]?

theorem not_mem_take_of_nodup {α : Type} {l : List α} (h : l.Nodup) {i : Nat} {b : α}
    (hb : l[i]? = some b) : b ∉ l.take i := by
  intro hm
  obtain ⟨j, hj, hjb⟩ := List.getElem_of_mem hm
  have hji : j < i := by simp at hj; omega
  have hil : i < l.length := (List.getElem?_eq_some_iff.1 hb).1
  have hjl : j < l.length := by omega
  have e1 : l[j] = b := by rw [← hjb, List.getElem_take]
  have e2 : l[i] = b := (List.getElem?_eq_some_iff.1 hb).2
  exact List.pairwise_iff_getElem.1 h j i hjl hil hji (e1.trans e2.symm)


/-! ## What every crash of the tree must be -/


/-- **The tree a boot may find**, in the directory `j`: neither `seg` nor `seg.tmp` a directory;
`seg` nothing, or the file of the key `ko`. -/
def SafeT (j : Ino) (ko : Option Ino) (m : Tree) : Prop :=
  (∀ J, m.entry j segB ≠ some (.dir J)) ∧ (∀ J, m.entry j tmpB ≠ some (.dir J)) ∧
  (m.entry j segB = none ∨ ∃ k, ko = some k ∧ m.entry j segB = some (.file k))


/-! ## The claim and its facts -/

namespace BC

abbrev bN : NameSet := .only [segB, tmpB]

theorem bN_seg : bN.Mem segB := by simp [NameSet.Mem]
theorem bN_tmp : bN.Mem tmpB := by simp [NameSet.Mem]

/-- **`SafeT` of every crash keeping `K`**, and `seg` as now once there, read through the claim. -/
def BSafeK (j : Ino) (ko : Option Ino) (h : NamesH) (K : Nat → Prop) : Prop :=
  (∀ J, h.valAfter j K segB ≠ some (.dir J)) ∧ (∀ J, h.valAfter j K tmpB ≠ some (.dir J)) ∧
  (h.valAfter j K segB = none ∨ ∃ k, ko = some k ∧ h.valAfter j K segB = some (.file k)) ∧
  (h.valAfter j K segB ≠ none → h.valAfter j K segB = h.cur !! segB)

/-- **The invariant's facts**, over every kept set closed in the claim. -/
def BInv (j : Ino) (ko : Option Ino) (h : NamesH) : Prop :=
  ∀ K, DS.RegionCut [(j, bN, h)] K → BSafeK j ko h K

theorem binv_crash {j : Ino} {ko : Option Ino} {h : NamesH} {n : Nat} {m' : Tree}
    (hb : BInv j ko h) (hc : RegionCrashed [(j, bN, h)] n m') : SafeT j ko m' := by
  obtain ⟨K, hK, hv⟩ := DS.regionCut_of_crashed hc
  have hs : m'.entry j segB = h.valAfter j K segB := hv _ (List.mem_singleton_self _) segB bN_seg
  have ht : m'.entry j tmpB = h.valAfter j K tmpB := hv _ (List.mem_singleton_self _) tmpB bN_tmp
  obtain ⟨h1, h2, h3, -⟩ := hb K hK
  unfold SafeT
  rw [hs, ht]
  exact ⟨h1, h2, h3⟩

theorem binv_init {j : Ino} {ko : Option Ino} {m : Tree} (h : SafeT j ko m) :
    BInv j ko (NamesH.init m j bN) := by
  intro K _
  have hs : (NamesH.init m j bN).valAfter j K segB = m.entry j segB :=
    DS.valAfter_init _ _ _ _ _ bN_seg
  have ht : (NamesH.init m j bN).valAfter j K tmpB = m.entry j tmpB :=
    DS.valAfter_init _ _ _ _ _ bN_tmp
  have hc : (NamesH.init m j bN).cur !! segB = m.entry j segB := by
    show restrictN bN (entsOf m j) !! segB = _
    rw [restrictN_lookup _ _ _ bN_seg, entsOf_lookup]
  unfold BSafeK
  rw [hs, ht, hc]
  exact ⟨h.1, h.2.1, h.2.2, fun _ => rfl⟩

/-- A cut of the claim with one more entry is a cut of the claim before it. -/
theorem regionCut_log {j : Ino} {N : NameSet} {h : NamesH} {x : Nat} {e : LogEntry} {c : Ents}
    {K : Nat → Prop} (hK : DS.RegionCut [(j, N, h.log x e c)] K) : DS.RegionCut [(j, N, h)] K := by
  intro d hd d' hd' x1 e1 E1 y e' E' hx hy hk hlt
  simp only [List.mem_singleton] at hd hd'
  subst hd hd'
  exact hK _ (List.mem_singleton_self _) _ (List.mem_singleton_self _) x1 e1 E1 y e' E'
    (by show _ ∈ h.ents ++ _; exact List.mem_append_left _ hx)
    (by show _ ∈ h.ents ++ _; exact List.mem_append_left _ hy) hk hlt

/-- **A step writing `seg.tmp` only, leaving no directory there, with `seg` as it was.** -/
theorem binv_tmp {j : Ino} {ko : Option Ino} {h : NamesH} (hb : BInv j ko h) (x : Nat)
    (e : LogEntry) (c : Ents) (hns : ¬ e.op.Writes j segB) (hcs : c !! segB = h.cur !! segB)
    (hct : ∀ J, c !! tmpB ≠ some (.dir J)) : BInv j ko (h.log x e c) := by
  intro K hK
  obtain ⟨h1, h2, h3, h4⟩ := hb K (regionCut_log hK)
  have hs : (h.log x e c).valAfter j K segB = h.valAfter j K segB :=
    DS.valAfter_log_skip _ _ _ _ _ _ _ (fun hw => hns hw.2)
  have hc : (h.log x e c).cur !! segB = h.cur !! segB := hcs
  unfold BSafeK
  rw [hs, hc]
  refine ⟨h1, fun J => ?_, h3, h4⟩
  by_cases hw : K x ∧ e.op.Writes j tmpB
  · rw [DS.valAfter_log_last _ _ _ _ _ _ _ hw.1 hw.2]; exact hct J
  · rw [DS.valAfter_log_skip _ _ _ _ _ _ _ hw]; exact h2 J

/-- With `seg` absent now, no crash has it, and any key will do. -/
theorem binv_rekey {j : Ino} {ko : Option Ino} {h : NamesH} (hb : BInv j ko h)
    (hn : h.cur !! segB = none) (ko' : Option Ino) : BInv j ko' h := by
  intro K hK
  obtain ⟨h1, h2, -, h4⟩ := hb K hK
  have hs : h.valAfter j K segB = none := by
    cases hv : h.valAfter j K segB with
    | none => rfl
    | some v =>
      have h4' := h4 (by rw [hv]; exact Option.some_ne_none v)
      rw [hv, hn] at h4'; cases h4'
  exact ⟨h1, h2, .inl hs, h4⟩

/-- **The rename of `seg.tmp`, the key's file `k`, onto the absent `seg`.** -/
theorem binv_rename {j k : Ino} {h : NamesH} (hb : BInv j (some k) h) (hn : h.cur !! segB = none)
    (x : Nat) (e : LogEntry) (c : Ents) (hws : e.op.Writes j segB) (hcs : c !! segB = some (.file k))
    (hct : ∀ J, c !! tmpB ≠ some (.dir J)) : BInv j (some k) (h.log x e c) := by
  intro K hK
  obtain ⟨h1, h2, -, h4⟩ := hb K (regionCut_log hK)
  have hs0 : h.valAfter j K segB = none := by
    cases hv : h.valAfter j K segB with
    | none => rfl
    | some v =>
      have h4' := h4 (by rw [hv]; exact Option.some_ne_none v)
      rw [hv, hn] at h4'; cases h4'
  have hc : (h.log x e c).cur !! segB = some (.file k) := hcs
  have ht : ∀ J, (h.log x e c).valAfter j K tmpB ≠ some (.dir J) := fun J => by
    by_cases hw : K x ∧ e.op.Writes j tmpB
    · rw [DS.valAfter_log_last _ _ _ _ _ _ _ hw.1 hw.2]; exact hct J
    · rw [DS.valAfter_log_skip _ _ _ _ _ _ _ hw]; exact h2 J
  unfold BSafeK
  by_cases hK' : K x
  · have hs : (h.log x e c).valAfter j K segB = some (.file k) := by
      rw [DS.valAfter_log_last _ _ _ _ _ _ _ hK' hws]; exact hcs
    rw [hs, hc]
    exact ⟨fun J h => (by cases h), ht, .inr ⟨k, rfl, rfl⟩, fun _ => rfl⟩
  · have hs : (h.log x e c).valAfter j K segB = none := by
      rw [DS.valAfter_log_skip _ _ _ _ _ _ _ (fun hw => hK' hw.1)]; exact hs0
    rw [hs]
    exact ⟨fun J h => (by cases h), ht, .inl rfl, fun h => absurd rfl h⟩

/-! ## The claim's names now -/

/-- **What the names hold now**: neither a directory; `seg` nothing or the key's file. -/
def NowOk (ko : Option Ino) (c : Ents) : Prop :=
  (∀ J, c !! segB ≠ some (.dir J)) ∧ (∀ J, c !! tmpB ≠ some (.dir J)) ∧
  (c !! segB = none ∨ ∃ k, ko = some k ∧ c !! segB = some (.file k))

/-- The facts at the cut keeping every entry, with the claim's coherence: the names now. -/
theorem binv_now {j : Ino} {ko : Option Ino} {h : NamesH} (hb : BInv j ko h) (hc : HistCoh h j bN) :
    NowOk ko h.cur := by
  obtain ⟨h1, h2, h3, -⟩ := hb (fun _ => True) (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial)
  have e : ∀ b, bN.Mem b → h.valAfter j (fun _ => True) b = h.cur !! b :=
    fun b hb => hc.2 _ (fun _ _ => trivial) b hb
  rw [e _ bN_seg] at h1 h3
  rw [e _ bN_tmp] at h2
  exact ⟨h1, h2, h3⟩

theorem remove_tmp_not_seg (j : Ino) (n : Node) : ¬ (MetaOp.remove j tmpB n).Writes j segB := by
  simp [MetaOp.Writes, MetaOp.slots, Ne.symm tmp_ne_seg]

theorem create_tmp_not_seg (j i : Ino) : ¬ (MetaOp.create j tmpB i).Writes j segB := by
  simp [MetaOp.Writes, MetaOp.slots, Ne.symm tmp_ne_seg]

theorem rename_writes_seg (j : Ino) (n : Node) (old : Option Node) :
    (MetaOp.rename j tmpB j segB n old).Writes j segB := by
  left; simp [MetaOp.slots]

/-- With the key's file named nowhere, the key `none` will do. -/
theorem safeT_unnamed {j k : Ino} {m : Tree} (h : SafeT j (some k) m) (hn : ¬ Named m k) :
    SafeT j none m := by
  refine ⟨h.1, h.2.1, ?_⟩
  rcases h.2.2 with h3 | ⟨k', hk', hs⟩
  · exact .inl h3
  · cases hk'; exact absurd ⟨j, segB, hs⟩ hn

/-! ## The invariant -/

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

def bootN : Namespace := nroot .@ "walfs"

theorem bootN_disj : ↑osN ⊆ (⊤ : CoPset) \ ↑bootN := mask_ndot_ne' nroot "osfs" "walfs" (by decide)

theorem bootN_shN : ↑osShN ⊆ (⊤ : CoPset) \ ↑bootN :=
  mask_ndot_ne' nroot "osfsShared" "walfs" (by decide)

/-- **One side's half** (the invariant's or the program's): the ghost variable recording the key
and the claim's history, and half of the claim on `seg` and `seg.tmp`. -/
def bHalf (j : Ino) (γ : GName) (ko : Option Ino) (h : NamesH) : IProp GF :=
  iprop(ghostVar γ (1 : Qp).half (ko, h) ∗ osNames (L := L) j bN (DFrac.own (1 : Qp).half) h)

instance bHalf_timeless (j : Ino) (γ : GName) (ko : Option Ino) (h : NamesH) :
    Timeless (bHalf (L := L) j γ ko h) := by
  unfold bHalf; infer_instance

/-- **The crash invariant** of the root directory `j`: half of the claim, the facts, and the
invariant's half of the key's file (`DS.keyRes`, its every crash `DataGood`). -/
def bootInv (j : Ino) (γ : GName) : IProp GF :=
  inv bootN iprop(∃ (ko : Option Ino) (h : NamesH),
    bHalf (L := L) j γ ko h ∗ ⌜BInv j ko h⌝ ∗ DS.keyRes (L := L) ko)

instance bootInv_persistent (j : Ino) (γ : GName) : Persistent (bootInv (L := L) j γ) := by
  unfold bootInv; infer_instance

/-- Two halves agree. -/
theorem bHalf_agree (j : Ino) (γ : GName) (ko ko' : Option Ino) (h h' : NamesH) :
    ⊢ bHalf (L := L) j γ ko h -∗ bHalf (L := L) j γ ko' h' -∗
      ⌜ko = ko' ∧ h = h'⌝ ∗ bHalf (L := L) j γ ko h ∗ bHalf (L := L) j γ ko h := by
  unfold bHalf
  iintro ⟨Hv, Hw⟩ ⟨Hv', Hw'⟩
  icases ghostVar_agree γ _ _ _ _ $$ Hv Hv' with %he
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  isplitr
  · ipureintro; exact ⟨rfl, rfl⟩
  iframe

/-- The two halves of a whole claim, with a new value of the ghost variable. -/
theorem bHalf_update (j : Ino) (γ : GName) (ko : Option Ino) (h : NamesH) (ko' : Option Ino)
    (h' : NamesH) (E : CoPset) :
    ⊢ ghostVar γ (1 : Qp).half (ko, h) -∗ ghostVar γ (1 : Qp).half (ko, h) -∗
      osNames (L := L) j bN (DFrac.own 1) h' ={E}=∗
      bHalf (L := L) j γ ko' h' ∗ bHalf (L := L) j γ ko' h' := by
  iintro Hv Hv1 Hw
  have hfr := osNames_frac (L := L) j bN (1 : Qp).half (1 : Qp).half h'
  rw [Qp.half_add_half] at hfr
  icases hfr.1 $$ Hw with ⟨Hw, Hw1⟩
  imod ghostVar_update_halves (ko', h') γ _ _ $$ Hv Hv1 with ⟨Hv, Hv1⟩
  imodintro
  unfold bHalf
  iframe

/-- The invariant allocated, with the program's half. -/
theorem boot_alloc (j : Ino) (ko : Option Ino) (h : NamesH) (hb : BInv j ko h) (E : CoPset) :
    ⊢ osNames (L := L) j bN (DFrac.own 1) h -∗ DS.keyRes (L := L) ko ={E}=∗
      ∃ γ, bootInv (L := L) j γ ∗ bHalf (L := L) j γ ko h := by
  iintro Hw Hk
  imod ghostVar_alloc (GF := GF) (ko, h) with ⟨%γ, Hv⟩
  icases (ghostVar_split_half γ 1 (ko, h)).1 $$ Hv with ⟨Hv1, Hv2⟩
  imod bHalf_update (L := L) j γ ko h ko h E $$ Hv1 Hv2 Hw with ⟨Hh1, Hh2⟩
  imod inv_alloc bootN E iprop(∃ (ko : Option Ino) (h : NamesH),
      bHalf (L := L) j γ ko h ∗ ⌜BInv j ko h⌝ ∗ DS.keyRes (L := L) ko) $$ [Hh1 Hk] with #Hinv
  · inext; iexists ko, h; iframe Hh1 Hk; ipureintro; exact hb
  imodintro
  iexists γ
  iframe Hh2
  unfold bootInv; iexact Hinv

theorem except_inter_b : (NameSet.except []).inter [segB, tmpB] = bN := by
  simp [NameSet.inter, bN]

/-- **A fresh generation's start**: from the tree's resources (`osShared`, nothing logged) on a
`SafeT` tree, the invariant with the program's half, and what the program keeps of the rest. -/
theorem boot_start (R : Roots) (r : GoString) (j : Ino) (hr : (r, j) ∈ R) (m : Tree)
    (hwf : TreeWf R m) (ko : Option Ino) (hs : SafeT j ko m) (E : CoPset) (hE : ↑osShN ⊆ E) :
    ⊢ osShared (L := L) R (m, []) -∗ DS.keyRes (L := L) ko ={E}=∗
      ∃ γ, bootInv (L := L) j γ ∗ bHalf (L := L) j γ ko (NamesH.init m j bN) ∗
        osSharedInv (L := L) R ∗ osCallPerms (L := L) R := by
  have hj := (DS.dirs_ok hwf hr).1
  have hnow : Hist.now ((m, []) : Hist) = m := by simp [Hist.now, Hist.ops, replay]
  have mem : j ∈ dirsOf (m, []) := by
    show j ∈ (GMap.toList (Hist.now ((m, []) : Hist))).map (·.1)
    rw [hnow]
    cases he : m !! j with
    | none => have := (GMap.mem_iff _ _).1 hj; rw [he] at this; cases this
    | some d => exact List.mem_map.2 ⟨(j, d), (GMap.mem_toList _ _ _).2 he, rfl⟩
  unfold osShared
  iintro ⟨#Hsh, -, Hperm, -, Hall⟩ Hk
  icases (BigSepL.bigSepL_perm (List.perm_cons_erase mem)).1 $$ Hall with Hall
  icases BigSepL.bigSepL_cons.1 $$ Hall with ⟨Hj, -⟩
  imod osNames_split R j (.except []) [segB, tmpB] _ hE $$ Hsh Hj with ⟨Hb, -⟩
  rw [namesOf_restrict (m, []) j (.except []) ((NameSet.except []).inter [segB, tmpB])
    (fun c _ => by simp [NameSet.Mem]), except_inter_b, DS.namesOf_nil]
  imod boot_alloc (L := L) j ko (NamesH.init m j bN) (binv_init hs) E $$ Hb Hk with ⟨%γ, Hinv, Hh⟩
  imodintro
  iexists γ
  iframe Hinv Hh Hsh Hperm

/-- **The names now**, read through the invariant. -/
theorem boot_facts (R : Roots) (j : Ino) (γ : GName) (ko : Option Ino) (h : NamesH) :
    ⊢ bootInv (L := L) j γ -∗ osSharedInv (L := L) R -∗ bHalf (L := L) j γ ko h ={⊤}=∗
      bHalf (L := L) j γ ko h ∗ ⌜NowOk ko h.cur⌝ := by
  iintro #Hinv #Hsh Hh
  unfold bHalf
  icases Hh with ⟨Hv, Hw⟩
  imod osNames_histCoh R j bN _ h CoPset.subseteq_top $$ Hsh Hw with ⟨Hw, %hc⟩
  unfold bootInv
  imod inv_acc (E := ⊤) (show ↑bootN ⊆ (⊤ : CoPset) from CoPset.subseteq_top) $$ Hinv
    with ⟨Hi, Hclose⟩
  icases Hi with ⟨%ko1, %h1, >Hh1, >%hb, >Hk⟩
  unfold bHalf
  icases Hh1 with ⟨Hv1, Hw1⟩
  icases ghostVar_agree γ _ _ _ _ $$ Hv Hv1 with %he
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  imod Hclose $$ [Hv1 Hw1 Hk] with -
  · inext; iexists ko, h; try unfold bHalf
    iframe Hv1 Hw1 Hk; ipureintro; exact hb
  imodintro
  iframe Hv Hw
  ipureintro; exact binv_now hb hc

/-- **With `seg` absent, a new key and its file deposited.** -/
theorem boot_deposit (j : Ino) (γ : GName) (ko : Option Ino) (h : NamesH) (k : Ino)
    (hn : h.cur !! segB = none) :
    ⊢ bootInv (L := L) j γ -∗ bHalf (L := L) j γ ko h -∗ DS.keyRes (L := L) (some k) ={⊤}=∗
      bHalf (L := L) j γ (some k) h := by
  iintro #Hinv Hh Hk
  unfold bootInv
  imod inv_acc (E := ⊤) (show ↑bootN ⊆ (⊤ : CoPset) from CoPset.subseteq_top) $$ Hinv
    with ⟨Hi, Hclose⟩
  icases Hi with ⟨%ko1, %h1, >Hh1, >%hb, >-⟩
  icases bHalf_agree (L := L) j γ _ _ _ _ $$ Hh Hh1 with ⟨%he, Hh, Hh1⟩
  obtain ⟨rfl, rfl⟩ := he
  unfold bHalf
  icases Hh with ⟨Hv, Hw⟩
  icases Hh1 with ⟨Hv1, Hw1⟩
  have hfr := osNames_frac (L := L) j bN (1 : Qp).half (1 : Qp).half h
  rw [Qp.half_add_half] at hfr
  ihave Hw := hfr.2 $$ [Hw Hw1]
  · iframe Hw Hw1
  imod bHalf_update (L := L) j γ ko h (some k) h _ $$ Hv Hv1 Hw with ⟨Hh, Hh1⟩
  try unfold bHalf
  imod Hclose $$ [Hh1 Hk] with -
  · inext; iexists (some k), h; iframe Hh1 Hk; ipureintro; exact binv_rekey hb hn _
  imodintro
  iexact Hh

end res

/-! ## A crash -/

section crash
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF]

/-- **A crash, from the old generation's invariant**: the tree left is `SafeT` with a key whose
file, as the new generation starts with it, is `DataGood`. -/
theorem boot_crash (Q : OsState → OsState → Prop) (L L' : GooseLocalGS GF) (R : Roots) (j : Ino)
    (γ : GName) (V' : Hist) :
    ⊢ bootInv (L := L) j γ -∗ osSharedInv (L := L) R -∗
      crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) [] false V' ={⊤}=∗
      ∃ (ko : Option Ino) (D : List Ino), ⌜SafeT j ko V'.now⌝ ∗ DS.startFile (L := L') ko ∗
        crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D false V' := by
  iintro #Hinv #Hsh Hr
  unfold bootInv
  imod inv_acc (E := ⊤) (show ↑bootN ⊆ (⊤ : CoPset) from CoPset.subseteq_top) $$ Hinv
    with ⟨Hi, Hclose⟩
  icases Hi with ⟨%ko, %h, >Hh, >%hb, >Hk⟩
  unfold bHalf
  icases Hh with ⟨Hv, Hw⟩
  ihave Hc := osCommitLb_zero (L := L)
  imod Hc
  ihave Hcl : osClaims L [((j, bN, h), DFrac.own (1 : Qp).half)] $$ [Hw]
  · unfold osClaims; iapply BigSepL.bigSepL_singleton.2; iexact Hw
  imod crashRest_region Q L L' [] false V' R _ 0 _ bootN_shN $$ Hsh Hr Hcl Hc with ⟨%hreg, Hr, Hcl⟩
  have hsafe : SafeT j ko V'.now := binv_crash hb hreg
  icases (osClaims_cons L _ _).1 $$ Hcl with ⟨Hw, -⟩
  cases ko with
  | none =>
    imod Hclose $$ [Hv Hw Hk] with -
    · inext; iexists none, h; try unfold bHalf
      iframe Hv Hw Hk; ipureintro; exact hb
    imodintro
    iexists none, []
    iframe Hr
    isplitr
    · ipureintro; exact hsafe
    unfold DS.startFile; iempintro
  | some k =>
    unfold DS.keyRes
    icases Hk with ⟨%m, %bs, Hm, Hb, %hg⟩
    icases osCrash_take_runs_keep Q L L' [] false V' k List.not_mem_nil _ m
      [(0, DFrac.own (1 : Qp).half, bs)] $$ Hr Hm [Hb] with ⟨%fo, %hfo, Hf, Hr, Hm, Hb⟩
    · iapply BigSepL.bigSepL_singleton.2; iexact Hb
    icases BigSepL.bigSepL_singleton.1 $$ Hb with Hb
    imod Hclose $$ [Hv Hw Hm Hb] with -
    · inext; iexists (some k), h; try unfold bHalf
      iframe Hv Hw
      isplitr
      · ipureintro; exact hb
      dsimp only
      iexists m, bs
      iframe Hm Hb
      ipureintro; exact hg
    imodintro
    obtain ⟨hfc, hnamed, -⟩ := hfo
    cases fo with
    | none =>
      iexists none, [k]
      iframe Hr
      isplitr
      · ipureintro
        exact safeT_unnamed hsafe (fun hn => by have := hnamed hn; simp at this)
      unfold DS.startFile; iempintro
    | some f =>
      iexists (some k), [k]
      iframe Hr
      isplitr
      · ipureintro; exact hsafe
      unfold DS.startFile osFileStartO
      iexists f
      iframe Hf
      ipureintro; exact hg _ hfc

end crash

/-! ## The steps that change the claim, the invariant opened around them -/

section steps
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

/-- The invariant opened around a step: the whole claim, the facts, and what closes it again with
the claim's new history (whose facts the caller shows). -/
theorem boot_acc (j : Ino) (γ : GName) (ko : Option Ino) (h : NamesH) :
    ⊢ bootInv (L := L) j γ -∗ bHalf (L := L) j γ ko h ={⊤, ⊤ \ ↑bootN}=∗
      osNames (L := L) j bN (DFrac.own 1) h ∗ ⌜BInv j ko h⌝ ∗
      (∀ h', ⌜BInv j ko h'⌝ -∗ osNames (L := L) j bN (DFrac.own 1) h' ={⊤ \ ↑bootN, ⊤}=∗
        bHalf (L := L) j γ ko h') := by
  iintro #Hinv Hh
  unfold bootInv
  imod inv_acc (E := ⊤) (show ↑bootN ⊆ (⊤ : CoPset) from CoPset.subseteq_top) $$ Hinv
    with ⟨Hi, Hclose⟩
  icases Hi with ⟨%ko1, %h1, >Hh1, >%hb, >Hk⟩
  icases bHalf_agree (L := L) j γ _ _ _ _ $$ Hh Hh1 with ⟨%he, Hh, Hh1⟩
  obtain ⟨rfl, rfl⟩ := he
  unfold bHalf
  icases Hh with ⟨Hv, Hw⟩
  icases Hh1 with ⟨Hv1, Hw1⟩
  have hfr := osNames_frac (L := L) j bN (1 : Qp).half (1 : Qp).half h
  rw [Qp.half_add_half] at hfr
  ihave Hw := hfr.2 $$ [Hw Hw1]
  · iframe Hw Hw1
  imodintro
  iframe Hw
  isplitr
  · ipureintro; exact hb
  iintro %h' %hb' Hw
  imod bHalf_update (L := L) j γ ko h ko h' _ $$ Hv Hv1 Hw with ⟨Hh, Hh1⟩
  try unfold bHalf
  imod Hclose $$ [Hh1 Hk] with -
  · inext; iexists ko, h'; iframe Hh1 Hk; ipureintro; exact hb'
  imodintro
  iexact Hh

/-- **`unlink(2)` of `d/seg.tmp`, the file `i`**, `d` the directory `j`, by a call begun after the
claim's last change, the invariant opened around it: `seg.tmp` gone, or no effect and an error. -/
theorem wp_unlinkTmp (R : Roots) (d : GoString) (dq : DFrac) (j : Ino) (γ : GName) (ko : Option Ino)
    (h : NamesH) (i : Ino) (t s0 : Nat) (q : Qp) (hi : h.cur !! tmpB = some (.file i))
    (hs : h.next ≤ s0) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ bootInv (L := L) j γ -∗
      osPathS (L := L) R d dq j -∗ bHalf (L := L) j γ ko h -∗ osCallS (L := L) t s0 (child d tmpB) q -∗
      (∀ e : w64, osCallPerm (L := L) (callKey R d) q -∗ osPathS (L := L) R d dq j -∗
        ((⌜e ≠ 0⌝ ∗ bHalf (L := L) j γ ko h) ∨
          ∃ h', bHalf (L := L) j γ ko h' ∗ ⌜h'.cur !! tmpB = none ∧ h'.cur !! segB = h.cur !! segB⌝) -∗
        Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Unlink" (Val (PairV (osTokV t) (#(child d tmpB))))) {{ Φ }} := by
  iintro #Hos #Hsh #Hinv Hp Hh Hc HΦ
  iapply (wp_atomic (E2 := (⊤ : CoPset) \ ↑bootN))
  imod boot_acc (L := L) j γ ko h $$ Hinv Hh with ⟨Hw, %hb, Hclose⟩
  imodintro
  iapply wp_osUnlinkSN R d tmpB j i bN dq h t s0 q tmpB_ok bN_tmp hi hs bootN_disj bootN_shN
    $$ Hos Hsh Hp Hw Hc
  iintro %e Hperm Hp Ha
  unfold osNamesAfter
  icases Ha with (⟨%hne, Hw⟩ | ⟨%x, -, Hw⟩)
  · imod Hclose $$ %h %hb Hw with Hh
    imodintro
    iapply HΦ $$ Hperm Hp
    ileft; iframe Hh; ipureintro; exact hne
  · let c := restrictN bN (GMap.delete tmpB h.cur)
    have hcs : c !! segB = h.cur !! segB := by
      rw [restrictN_lookup _ _ _ bN_seg, GMap.lookup_delete_ne _ tmp_ne_seg]
    have hct : c !! tmpB = none := by
      rw [restrictN_lookup _ _ _ bN_tmp, GMap.lookup_delete]
    imod Hclose $$ %_ %(binv_tmp hb x ⟨.remove j tmpB (.file i), s0⟩ c (remove_tmp_not_seg j _)
      hcs (fun J => by rw [hct]; simp)) Hw with Hh
    imodintro
    iapply HΦ $$ Hperm Hp
    iright; iexists _; iframe Hh; ipureintro; exact ⟨hct, hcs⟩

/-- **`open(2)` with `O_CREAT` of `d/seg.tmp`, absent**, by a call begun after the claim's last
change, the invariant opened around it: a new file there (its fd on success), or no effect and an
error. -/
theorem wp_createTmp (R : Roots) (d : GoString) (dq : DFrac) (j : Ino) (γ : GName) (ko : Option Ino)
    (h : NamesH) (t s0 : Nat) (q : Qp) (fl : w64) (hfl : OpenFlagsOk fl.toNat)
    (hcr : fl.toNat / O_CREAT % 2 = 1) (hn : h.cur !! tmpB = none) (hs : h.next ≤ s0)
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ bootInv (L := L) j γ -∗
      osPathS (L := L) R d dq j -∗ bHalf (L := L) j γ ko h -∗ osCallS (L := L) t s0 (child d tmpB) q -∗
      (∀ fd : w64, ∀ e : w64, osCallPerm (L := L) (callKey R d) q -∗ osPathS (L := L) R d dq j -∗
        ((⌜e ≠ 0 ∧ fd = -1⌝ ∗ bHalf (L := L) j γ ko h) ∨
          ∃ i h', bHalf (L := L) j γ ko h' ∗
            ⌜h'.cur !! tmpB = some (.file i) ∧ h'.cur !! segB = h.cur !! segB⌝ ∗
            osMeta (L := L) i (DFrac.own 1) newMeta ∗
            (⌜e ≠ 0 ∧ fd = -1⌝ ∨ ⌜e = 0 ∧ 0 ≤ fd.toInt⌝ ∗ osFd (L := L) fd (DFrac.own 1) (openFd i fl))) -∗
        Φ (PairV (#fd) (#e))) -∗
      WP (ExternalOp fsExt.name "Open" (Val (PairV (osTokV t) (PairV (#(child d tmpB)) (#fl)))))
        {{ Φ }} := by
  iintro #Hos #Hsh #Hinv Hp Hh Hc HΦ
  iapply (wp_atomic (E2 := (⊤ : CoPset) \ ↑bootN))
  imod boot_acc (L := L) j γ ko h $$ Hinv Hh with ⟨Hw, %hb, Hclose⟩
  imodintro
  iapply wp_osOpenCreateSN R d tmpB j bN dq h t s0 q fl hfl hcr (.inr hn) tmpB_ok bN_tmp
    (fun J => by rw [hn]; simp) hs bootN_disj bootN_shN $$ Hos Hsh Hp Hw Hc
  iintro %fd %e Hperm Hp Hr
  icases Hr with (⟨%i, %hi, -, -⟩ | ⟨-, %x, %i, -, Hw, Hm, Hfd⟩ | ⟨%he, Hw⟩)
  · rw [hn] at hi; cases hi
  · let c : Ents := <[tmpB := .file i]> h.cur
    have hcs : c !! segB = h.cur !! segB := GMap.lookup_insert_ne _ _ tmp_ne_seg
    have hct : c !! tmpB = some (.file i) := GMap.lookup_insert _ _ _
    imod Hclose $$ %_ %(binv_tmp hb x ⟨.create j tmpB i, s0⟩ c (create_tmp_not_seg j i)
      hcs (fun J => by rw [hct]; simp)) Hw with Hh
    imodintro
    iapply HΦ $$ Hperm Hp
    iright; iexists i, _; iframe Hh Hm Hfd; ipureintro; exact ⟨hct, hcs⟩
  · imod Hclose $$ %h %hb Hw with Hh
    imodintro
    iapply HΦ $$ Hperm Hp
    ileft; iframe Hh; ipureintro; exact he

/-- **`rename(2)` of `d/seg.tmp`, the key's file `i`, onto the absent `d/seg`**, by a call begun
after the claim's last change, the invariant opened around it (`binv_rename`): `seg` names `i`, or
no effect and an error. -/
theorem wp_renameTmp (R : Roots) (d : GoString) (dq : DFrac) (j : Ino) (γ : GName) (h : NamesH)
    (i : Ino) (t s0 : Nat) (q : Qp) (hi : h.cur !! tmpB = some (.file i))
    (hsn : h.cur !! segB = none) (hs : h.next ≤ s0) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ bootInv (L := L) j γ -∗
      osPathS (L := L) R d dq j -∗ bHalf (L := L) j γ (some i) h -∗
      osCallS (L := L) t s0 (child d tmpB) q -∗
      (∀ e : w64, osCallPerm (L := L) (callKey R d) q -∗ osPathS (L := L) R d dq j -∗
        ((⌜e ≠ 0⌝ ∗ bHalf (L := L) j γ (some i) h) ∨
          ∃ h', bHalf (L := L) j γ (some i) h' ∗
            ⌜h'.cur !! tmpB = none ∧ h'.cur !! segB = some (.file i)⌝) -∗
        Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Rename" (Val (PairV (osTokV t)
        (PairV (#(child d tmpB)) (#(child d segB)))))) {{ Φ }} := by
  iintro #Hos #Hsh #Hinv Hp Hh Hc HΦ
  iapply (wp_atomic (E2 := (⊤ : CoPset) \ ↑bootN))
  imod boot_acc (L := L) j γ (some i) h $$ Hinv Hh with ⟨Hw, %hb, Hclose⟩
  imodintro
  iapply wp_osRenameFileS1 R d tmpB segB j i bN dq h t s0 q tmpB_ok segB_ok bN_tmp bN_seg tmp_ne_seg
    hi (fun J => by rw [hsn]; simp) hs bootN_disj bootN_shN $$ Hos Hsh Hp Hw Hc
  iintro %e Hperm Hp Ha
  unfold osNamesAfter
  icases Ha with (⟨%hne, Hw⟩ | ⟨%x, -, Hw⟩)
  · imod Hclose $$ %h %hb Hw with Hh
    imodintro
    iapply HΦ $$ Hperm Hp
    ileft; iframe Hh; ipureintro; exact hne
  · let c := restrictN bN (<[segB := .file i]> (GMap.delete tmpB h.cur))
    have hcs : c !! segB = some (.file i) := by
      rw [restrictN_lookup _ _ _ bN_seg, GMap.lookup_insert]
    have hct : c !! tmpB = none := by
      rw [restrictN_lookup _ _ _ bN_tmp, GMap.lookup_insert_ne _ _ (Ne.symm tmp_ne_seg),
        GMap.lookup_delete]
    imod Hclose $$ %_ %(binv_rename hb hsn x ⟨.rename j tmpB j segB (.file i) (h.cur !! segB), s0⟩ c
      (rename_writes_seg j _ _) hcs (fun J => by rw [hct]; simp)) Hw with Hh
    imodintro
    iapply HΦ $$ Hperm Hp
    iright; iexists _; iframe Hh; ipureintro; exact ⟨hct, hcs⟩

end steps

end BC

end osfs_walfs
end EtcdGrove
end Perennial

end
