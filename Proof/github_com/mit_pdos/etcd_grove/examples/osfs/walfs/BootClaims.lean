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
public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.walfs.DSClaims

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace osfs_walfs

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

end BC

end osfs_walfs
end EtcdGrove
end Perennial

end
