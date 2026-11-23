/- Lean-first (no Rocq counterpart).

# The crash boot's resources (`notes/wal-fsext-w4c-plan.md`, "W4c U3 log", (b))

The separation-logic steps of `walBootCrash` (`BootCrash.lean`), each over one directory or one list:

* `osNames_split_only`: a claim `.except X` split into `.except (X ++ l)` and a claim `.only [b]`
  per name of `l` (the area's per WAL name, a WAL directory's per pipeline name);
* `bigSepM_sub_list`/`bigSepM_names`: some entries of a map's big separating conjunction, as a list;
* `walDirFiles`/`tmpDirFiles`: the crash boot's files of one WAL directory (its pipeline names'
  `tmpEnt`s and its `walOthers`) and of one `nm.tmp` directory (its `.touch`'s `tmpEnt`), from
  `dirBootFiles` and the directory's files-only fact (`BootFo`);
* `walDir_boot`: a WAL directory's whole claim and files as `walInv_alloc` takes them (its claim on
  the non-pipeline names, `walTmpsRes`, `walOthers`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.BootCrashSub
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.TmpClaim

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF]

/-- **A claim `.except X` split into `.except (X ++ l)` and one `.only [b]` per name of `l`**, the
histories as the boot history has them. -/
theorem osNames_split_only (L : GooseLocalGS GF) (R : Roots) (V : Hist) (j : Ino) (E : CoPset)
    (hE : ↑osShN ⊆ E) : ∀ (l X : List GoString), l.Nodup → (∀ b ∈ l, b ∉ X) →
    ⊢ osSharedInv (L := L) R -∗
      osNames (L := L) j (.except X) (DFrac.own 1) (namesOf V j (.except X)) ={E}=∗
      osNames (L := L) j (.except (X ++ l)) (DFrac.own 1) (namesOf V j (.except (X ++ l))) ∗
      [∗list] b ∈ l, osNames (L := L) j (.only [b]) (DFrac.own 1) (namesOf V j (.only [b]))
  | [], X, _, _ => by
    iintro #Hsh H
    rw [List.append_nil]
    imodintro
    iframe H
    iapply BigSepL.bigSepL_nil.2; iempintro
  | b :: l, X, hl, hX => by
    iintro #Hsh H
    imod osNames_split R j (.except X) [b] _ hE $$ Hsh H with ⟨Hb, Hr⟩
    have hb : (NameSet.except X).inter [b] = .only [b] := by
      simp only [NameSet.inter, List.filter_cons, List.filter_nil]
      rw [if_pos (decide_eq_true (hX b (List.mem_cons_self ..)))]
    have hd : (NameSet.except X).diff [b] = .except (X ++ [b]) := rfl
    rw [namesOf_restrict V j (.except X) ((NameSet.except X).inter [b]) (fun c hc => by
        rw [hb] at hc
        simp only [NameSet.Mem, List.mem_singleton] at hc ⊢
        subst hc; exact hX _ (List.mem_cons_self ..)),
      namesOf_restrict V j (.except X) ((NameSet.except X).diff [b]) (fun c hc => by
        simp only [NameSet.diff, NameSet.Mem, List.mem_append, not_or] at hc ⊢
        exact hc.1), hb, hd]
    have hl' := List.nodup_cons.1 hl
    imod osNames_split_only L R V j E hE l (X ++ [b]) hl'.2 (fun c hc hm => by
        rcases List.mem_append.1 hm with h | h
        · exact hX c (List.mem_cons_of_mem _ hc) h
        · rw [List.mem_singleton] at h; subst h; exact hl'.1 hc) $$ Hsh Hr with ⟨Hr, Hl⟩
    rw [show X ++ [b] ++ l = X ++ b :: l by simp]
    imodintro
    iframe Hr
    iapply BigSepL.bigSepL_cons.2
    iframe Hb Hl

/-- A list whose map has no duplicate has none. -/
theorem nodup_of_map' {α β : Type} (p : α → β) : ∀ {L : List α}, (L.map p).Nodup → L.Nodup
  | [], _ => List.nodup_nil
  | a :: L, h => by
    rw [List.map_cons, List.nodup_cons] at h
    exact List.nodup_cons.2 ⟨fun hm => h.1 (List.mem_map.2 ⟨a, hm, rfl⟩), nodup_of_map' p h.2⟩

/-- **Some entries of a map's big separating conjunction, as a list** (affine). -/
theorem bigSepM_sub_list {K V A : Type} [DecidableEq K] (M : GMap K V) (Φ : K → V → IProp GF)
    (l : List A) (f : A → K) (g : A → V) (hl : (l.map f).Nodup)
    (hs : ∀ x ∈ l, M !! f x = some (g x)) :
    ([∗list] kv ∈ GMap.toList M, Φ kv.1 kv.2) ⊢ [∗list] x ∈ l, Φ (f x) (g x) := by
  have hnd : (l.map (fun x => (f x, g x))).Nodup :=
    nodup_of_map' Prod.fst (by rw [List.map_map]; exact hl)
  have hsub : l.map (fun x => (f x, g x)) ⊆ GMap.toList M := by
    intro kv hkv
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hkv
    exact (GMap.mem_toList _ _ _).2 (hs x hx)
  obtain ⟨l0, hp0, hs0⟩ := List.subperm_of_subset hnd hsub
  obtain ⟨rest, hrest⟩ := hs0.exists_perm_append
  have hperm : ((l.map (fun x => (f x, g x))) ++ rest).Perm (GMap.toList M) :=
    (hp0.symm.append_right rest).trans hrest.symm
  refine (BigSepL.bigSepL_submseteq (Φ := fun kv => Φ kv.1 kv.2) hperm).trans ?_
  rw [BigSepL.bigSepL_map]

/-- **A map's entries at the names of `l`**, as lookups (nothing for an absent name). -/
theorem bigSepM_names (M : GMap GoString Node) (Φ : Option Node → IProp GF) (h0 : ⊢ Φ none)
    (l : List GoString) (hl : l.Nodup) :
    ([∗list] bn ∈ GMap.toList M, if bn.1 ∈ l then Φ (some bn.2) else emp) ⊢
      [∗list] b ∈ l, Φ (M !! b) := by
  let f : GoString → Option (GoString × Node) := fun b => (M !! b).map (b, ·)
  have hf : ∀ b x, f b = some x → x = (b, x.2) ∧ M !! b = some x.2 := by
    intro b x h
    simp only [f] at h
    cases e : M !! b with
    | none => rw [e] at h; cases h
    | some n => rw [e] at h; cases h; exact ⟨rfl, rfl⟩
  have hfst : ∀ b x, f b = some x → x.1 = b := fun b x h => congrArg Prod.fst (hf b x h).1
  have hnd : ((l.filterMap f).map Prod.fst).Nodup := by
    refine List.Nodup.mapOnW (nodup_filterMap_of hl (fun a _ a' _ x h h' => ?_)) (fun x hx y hy e => ?_)
    · rw [← hfst a x h, ← hfst a' x h']
    · obtain ⟨a, -, ha⟩ := List.mem_filterMap.1 hx
      obtain ⟨a', -, ha'⟩ := List.mem_filterMap.1 hy
      have h1 := (hf a x ha).2
      have h2 := (hf a' y ha').2
      rw [← hfst a x ha, e, hfst a' y ha'] at h1
      rw [h1] at h2
      exact Prod.ext e (Option.some.inj h2)
  refine (bigSepM_sub_list M (fun b n => if b ∈ l then Φ (some n) else emp) (l.filterMap f) Prod.fst Prod.snd hnd (fun x hx => ?_)).trans ?_
  · obtain ⟨a, -, ha⟩ := List.mem_filterMap.1 hx
    rw [hfst a x ha]; exact (hf a x ha).2
  · refine (BigSepL.bigSepL_mono (Ψ := fun _ x => Φ (some x.2)) (fun {k x} hk => ?_)).trans ?_
    · have hx := List.mem_of_getElem? hk
      obtain ⟨a, ha, hfa⟩ := List.mem_filterMap.1 hx
      have : x.1 ∈ l := by rw [hfst a x hfa]; exact ha
      show (if x.1 ∈ l then Φ (some x.2) else emp) ⊢ Φ (some x.2)
      rw [if_pos this]
    · rw [BigSepL.bigSepL_filterMap f (Φ := fun x => Φ (some x.2))]
      refine BigSepL.bigSepL_mono (fun {k b} _ => ?_)
      simp only [f]
      cases M !! b with
      | none => exact Affine.affine.trans h0
      | some n => exact .rfl

/-- A file's `tmpEnt` is its `trFile`. -/
theorem tmpEnt_file (L : GooseLocalGS GF) (i : Ino) :
    tmpEnt (hG := ⟨G, L⟩) (some (.file i)) = trFile (hG := ⟨G, L⟩) i False := rfl

theorem tmpEnt_none (L : GooseLocalGS GF) : ⊢ tmpEnt (hG := ⟨G, L⟩) none := by
  show ⊢ iprop(emp); exact .rfl

/-- **A WAL directory's files** (the crash boot's, `dirBootFiles`, all of it files): its pipeline
names' and its others' (`walOthers`, on the claim of its non-pipeline names). -/
theorem walDirFiles (L : GooseLocalGS GF) (m : Tree) (J : Ino) (nm : GoString) (hnm : walNameOk nm)
    (hfo : FilesOnly (entsOf m J)) :
    ([∗list] i ∈ dirBootFiles m nm J, trFile (hG := ⟨G, L⟩) i False) ⊢
      ([∗list] b ∈ walTmps, tmpEnt (hG := ⟨G, L⟩) (entsOf m J !! b)) ∗
      walOthers (L := L) [] J (restrictN (.except walTmps) (entsOf m J)) := by
  classical
  unfold dirBootFiles
  rw [BigSepL.bigSepL_filterMap]
  refine ((BigSepL.bigSepL_mono (Ψ := fun _ be =>
      iprop((if be.1 ∈ walTmps then tmpEnt (hG := ⟨G, L⟩) (some be.2) else emp) ∗
        (if be.1 ∉ walTmps ∧ walNameP be.1 = false then tmpEnt (hG := ⟨G, L⟩) (some be.2) else emp)))
      (fun {k be} hk => ?_)).trans BigSepL.bigSepL_sep_eqv.1).trans (sep_mono ?_ ?_)
  · have he : entsOf m J !! be.1 = some be.2 :=
      (GMap.mem_toList _ _ _).1 (List.mem_of_getElem? hk)
    obtain ⟨b, n⟩ := be
    obtain ⟨i, hi⟩ := hfo _ _ he
    simp only at hi
    subst hi
    simp only [tmpEnt_file]
    by_cases hb : walNameP b = false
    · rw [if_pos ((bootTake_wal hnm).2 hb)]
      by_cases ht : b ∈ walTmps
      · rw [if_pos ht, if_neg (fun h => h.1 ht)]
        exact sep_emp.2
      · rw [if_neg ht, if_pos ⟨ht, hb⟩]
        exact emp_sep.2
    · rw [if_neg (fun h => hb ((bootTake_wal hnm).1 h)),
        if_neg (fun h => hb (walTmps_not_wal b h)), if_neg (fun h => hb h.2)]
      exact sep_emp.2
  · exact bigSepM_names (entsOf m J) (tmpEnt (hG := ⟨G, L⟩)) (tmpEnt_none L) walTmps (by decide)
  · refine (bigSepM_sub_list (entsOf m J) (fun b n => if b ∉ walTmps ∧ walNameP b = false then
      tmpEnt (hG := ⟨G, L⟩) (some n) else emp) (GMap.toList (othersOf [] J (restrictN (.except walTmps)
      (entsOf m J)))) Prod.fst Prod.snd (GMap.toList_keys_nodup _) (fun kv hkv => ?_)).trans ?_
    · have h := (GMap.mem_toList _ _ _).1 hkv
      rw [othersOf_lookup] at h
      split at h
      · by_cases hm : (NameSet.except walTmps).Mem kv.1
        · rw [restrictN_lookup _ _ _ hm] at h; exact h
        · rw [restrictN_lookup_not _ _ _ hm] at h; cases h
      · cases h
    · refine BigSepL.bigSepL_mono (fun {k kv} hk => ?_)
      have h := (GMap.mem_toList _ _ _).1 (List.mem_of_getElem? hk)
      rw [othersOf_lookup] at h
      split at h
      · next hc =>
        have hm : kv.1 ∉ walTmps := by
          intro hm
          rw [restrictN_lookup_not (NameSet.except walTmps) _ kv.1 (fun h' => h' hm)] at h
          cases h
        show (if kv.1 ∉ walTmps ∧ walNameP kv.1 = false then _ else _) ⊢ _
        rw [if_pos ⟨hm, hc.1⟩]
      · cases h

/-- **A WAL name's temporary directory's probe** (the crash boot's file at its `.touch`). -/
theorem tmpDirFiles (L : GooseLocalGS GF) (m : Tree) (J : Ino) (nm : GoString) (hnm : walNameOk nm)
    (hfo : FilesOnly (entsOf m J)) :
    ([∗list] i ∈ dirBootFiles m (tmpName nm) J, trFile (hG := ⟨G, L⟩) i False) ⊢
      tmpEnt (hG := ⟨G, L⟩) (entsOf m J !! go!".touch") := by
  classical
  have hbt : ∀ b, BootTake (tmpName nm) b ↔ b ∈ [go!".touch"] := by
    intro b
    unfold BootTake
    simp only [List.mem_singleton]
    constructor
    · rintro (⟨h, -⟩ | ⟨-, h⟩)
      · exact (tmpName_not_walName' nm h).elim
      · exact h
    · intro h; exact .inr ⟨⟨nm, hnm, rfl⟩, h⟩
  unfold dirBootFiles
  rw [BigSepL.bigSepL_filterMap]
  refine (BigSepL.bigSepL_mono (Ψ := fun _ be =>
      iprop(if be.1 ∈ [go!".touch"] then tmpEnt (hG := ⟨G, L⟩) (some be.2) else emp))
      (fun {k be} hk => ?_)).trans ?_
  · have he : entsOf m J !! be.1 = some be.2 :=
      (GMap.mem_toList _ _ _).1 (List.mem_of_getElem? hk)
    obtain ⟨b, n⟩ := be
    obtain ⟨i, hi⟩ := hfo _ _ he
    simp only at hi
    subst hi
    simp only [tmpEnt_file]
    by_cases hb : BootTake (tmpName nm) b
    · rw [if_pos hb, if_pos ((hbt b).1 hb)]; exact .rfl
    · rw [if_neg hb, if_neg (fun h => hb ((hbt b).2 h))]; exact .rfl
  · refine (bigSepM_names (entsOf m J) (tmpEnt (hG := ⟨G, L⟩)) (tmpEnt_none L) [go!".touch"]
      (by simp)).trans ?_
    exact BigSepL.bigSepL_singleton.1

/-- **A WAL directory, as the new invariant takes it**: from its whole claim and its files, its claim
on the non-pipeline names, its pipeline names (`walTmpsRes`) and its others (`walOthers`). -/
theorem walDir_boot (L : GooseLocalGS GF) (R : Roots) (V : Hist) (hV : V.2 = []) (J : Ino)
    (nm : GoString) (hnm : walNameOk nm) (hfo : FilesOnly (entsOf V.now J)) (E : CoPset)
    (hE : ↑osShN ⊆ E) :
    ⊢ osSharedInv (L := L) R -∗
      osNames (L := L) J (.except []) (DFrac.own 1) (namesOf V J (.except [])) -∗
      ([∗list] i ∈ dirBootFiles V.now nm J, trFile (hG := ⟨G, L⟩) i False) ={E}=∗
      osNames (L := L) J (.except walTmps) (DFrac.own 1) (namesOf V J (.except walTmps)) ∗
      (walTmpsRes (hG := ⟨G, L⟩) J ∗ walTmpsHalf (hG := ⟨G, L⟩) J) ∗
      walOthers (L := L) [] J (restrictN (.except walTmps) (entsOf V.now J)) := by
  iintro #Hsh H Hf
  have hcm0 : ⊢ |==> osCommitLb (L := L) 0 := by
    unfold osCommitLb gCommitLb
    letI := (gooseOsGS (L := L)).osAllG
    exact monoNatLbOwn_0 _
  imod hcm0 with #H0
  imod osNames_split_only L R V J E hE walTmps [] (by decide) (fun _ _ h => by cases h) $$ Hsh H
    with ⟨H, Ht⟩
  rw [List.nil_append]
  ihave Hf := walDirFiles L V.now J nm hnm hfo $$ Hf
  icases Hf with ⟨Hf, Ho⟩
  imodintro
  iframe H Ho
  have helt : ∀ b, osNames (L := L) J (.only [b]) (DFrac.own 1) (namesOf V J (.only [b])) ∗
      tmpEnt (hG := ⟨G, L⟩) (entsOf V.now J !! b) ∗ osCommitLb (L := L) 0 ⊢
      tmpClaim (hG := ⟨G, L⟩) J b ∗ tmpHalf (hG := ⟨G, L⟩) J b := by
    intro b
    have e : (namesOf V J (.only [b])).cur !! b = entsOf V.now J !! b := by
      show restrictN _ (entsOf V.now J) !! b = _
      exact restrictN_lookup _ _ _ (List.mem_singleton_self _)
    have hf : HistFoP (fun _ => True) 0 J (.only [b]) (namesOf V J (.only [b])) := by
      refine HistFoP.of_boot (by simp [namesOf, hV]) (fun b' hb' _ J' hd => ?_)
      have e' : b' = b := List.mem_singleton.1 hb'
      subst e'
      have hb2 : (namesOf V J (.only [b'])).boot !! b' = entsOf V.now J !! b' := by
        show restrictN _ (entsOf V.1 J) !! b' = _
        rw [restrictN_lookup _ _ _ (List.mem_singleton_self _)]
        simp [Hist.now, Hist.ops, hV, replay]
      rw [hb2] at hd
      obtain ⟨i, hi⟩ := hfo _ _ hd
      cases hi
    rw [← e]
    exact tmpWhole_split (hG := ⟨G, L⟩) J b _ 0 hf
  iunfold walTmps at Ht Hf
  icases Ht with ⟨Ht0, Ht1, -⟩
  icases Hf with ⟨Hf0, Hf1, -⟩
  ihave ⟨Hc0, Hh0⟩ := helt _ $$ [$Ht0 $Hf0 $H0]
  ihave ⟨Hc1, Hh1⟩ := helt _ $$ [$Ht1 $Hf1 $H0]
  unfold walTmpsRes walTmpsHalf walTmps
  iframe Hc0 Hc1 Hh0 Hh1
  isplitl []
  · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; iempintro
  · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; iempintro

end res

end WalFs
end EtcdGrove
end Perennial

end
