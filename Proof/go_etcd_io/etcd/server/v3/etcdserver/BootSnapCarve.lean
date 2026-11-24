/-
**The new snapshot directory's names, carved into the claims `bootOk` hands on** (claim #34, stage 4,
2026-11-23). Lean-first. A defs module: `bootstrapSnapshot`'s proof, and any proof that holds an empty
directory's whole claim and wants one free name per file it may later create there.

* `carveFree`: the whole claim on the names of an empty directory `d`, but those of `X`, with a share of
  its path and of its call permission, gives `backend.fileFreeF (child d b)` for every name `b` of a
  duplicate-free list `l` of valid names outside `X` whose paths fit (each with half of what the
  previous one left of the shares).
* `sepL_toMap`: a big separating conjunction over a duplicate-free list of indices as one over a finite
  map whose keys are the list's (`snapFree`'s shape).
* `allW64`: every `w64`, once; `snapNames sd`: the backend's `db` and every index's `.snap.db`, distinct.
* `snapDir_carve`: the snapshot directory `config.snapDirOf dd`, new and empty, gives the backend file's
  free name and `snapFreeAll`'s claims, at the file extension's instances.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBbolt
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Net
public import Proof.go_etcd_io.etcd.server.v3.storage.OpenSnapshotBackendLemmas
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.LockRange
public import Proof.go_etcd_io.etcd.server.v3.config.PathFits
public import Proof.path.CleanIdem

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bootSnap

open Iris Iris.BI Iris.ProofMode Fs

/-! ### Pure facts -/

section pure
variable [GooseExts]

/-- A restriction of an empty entry map is empty. -/
theorem restrictN_none (N : NameSet) (e : Ents) (he : ∀ b, e !! b = none) (b : GoString) :
    restrictN N e !! b = none := by
  by_cases hb : N.Mem b
  · rw [restrictN_lookup N e b hb, he b]
  · exact restrictN_lookup_not N e b hb

/-- A map injective on a duplicate-free list keeps it duplicate-free. -/
theorem nodup_map_on {α β : Type} (f : α → β) : ∀ (l : List α),
    (∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) → l.Nodup → (l.map f).Nodup
  | [], _, _ => List.nodup_nil
  | a :: l, hf, hl => by
    have hl' := List.nodup_cons.1 hl
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, nodup_map_on f l (fun x hx y hy => hf x (List.mem_cons_of_mem _ hx) y
      (List.mem_cons_of_mem _ hy)) hl'.2⟩
    obtain ⟨b, hb, hfb⟩ := List.mem_map.1 hm
    have := hf b (List.mem_cons_of_mem _ hb) a (List.mem_cons_self ..) hfb
    subst this
    exact hl'.1 hb

/-- Every `w64`, once. -/
def allW64 : List w64 := (List.range (2 ^ 64)).map (fun n => BitVec.ofNat 64 n)

theorem mem_allW64 (i : w64) : i ∈ allW64 := by
  unfold allW64
  exact List.mem_map.2 ⟨i.toNat, List.mem_range.2 i.isLt, BitVec.ofNat_toNat _ _⟩

theorem allW64_nodup : allW64.Nodup := by
  unfold allW64
  refine nodup_map_on _ _ ?_ List.nodup_range
  intro a ha b hb hab
  have ha' := List.mem_range.1 ha
  have hb' := List.mem_range.1 hb
  have := congrArg BitVec.toNat hab
  simp only [BitVec.toNat_ofNat] at this
  rw [Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] at this
  exact this

/-- Database snapshot names of distinct indices are distinct. -/
theorem snapDBName_inj {i i' : w64} (h : snap.snapDBName i = snap.snapDBName i') : i = i' := by
  unfold snap.snapDBName at h
  have hl : ∀ n, (WalFs.hex16 n).length = 16 := fun n => by simp [WalFs.hex16]
  have h1 := (List.append_inj h (by rw [hl, hl])).1
  have h2 := WalFs.hex16_inj h1
  have hi : uint.nat i < 2 ^ 64 := by word
  have hi' : uint.nat i' < 2 ^ 64 := by word
  rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hi'] at h2
  word

theorem snapDBName_length (i : w64) : (snap.snapDBName i).length = 24 := by
  simp [snap.snapDBName, WalFs.hex16]

theorem snapDBPath_child (sd : GoString) (i : w64) :
    snap.snapDBPath sd i = child sd (snap.snapDBName i) := rfl

theorem backendPathOf_child (dd : GoString) :
    config.backendPathOf dd = child (config.snapDirOf dd) go!"db" := rfl

/-- The flattened form of a clean absolute path (`cleanAbsPath`) is `path.segsPath`'s. -/
theorem flatten_segsPath : ∀ cs : List GoString,
    (cs.map (go!"/" ++ ·)).flatten = path.segsPath cs
  | [] => rfl
  | c :: cs => by
    rw [List.map_cons, List.flatten_cons, flatten_segsPath cs]
    conv => rhs; unfold path.segsPath
    rw [List.foldl_cons, path.segsPath_foldl]
    simp

/-- **A clean absolute path in `cleanAbsPath`'s form is one in `filepath.CleanAbs`'s.** -/
theorem cleanAbs_of_cleanAbsPath {p : GoString} (hp : cleanAbsPath p) : filepath.CleanAbs p := by
  obtain ⟨cs, hne, hok, rfl⟩ := hp
  refine ⟨cs, hne, fun c hc => ?_, flatten_segsPath cs⟩
  obtain ⟨h1, h2, h3, h4⟩ := hok c hc
  exact ⟨h1, fun x hx he => h2 (by subst he; exact hx), h3, h4⟩

/-- **The snapshot directory is `snap` in the member directory**, when the member directory
`Join(dd, "member")` is clean and absolute. -/
theorem snapDirOf_child {dd : GoString} (hm : cleanAbsPath (path.joinModel [dd, go!"member"])) :
    config.snapDirOf dd = child (path.joinModel [dd, go!"member"]) go!"snap" := by
  unfold config.snapDirOf
  rw [← path.joinModel_triple dd go!"member" go!"snap" (by decide) (by decide),
    filepath.joinModel_name _ _ (cleanAbs_of_cleanAbsPath hm) (by unfold path.cleanSeg; decide)]
  simp [child, slashB]

theorem nameOk_snap : NameOk go!"snap" := by unfold NameOk; decide

theorem nameOk_db : NameOk go!"db" := by unfold NameOk; decide

/-- The names `bootstrapSnapshot` hands out of the new snapshot directory: `db` and every index's
`.snap.db`. -/
def snapNames : List GoString := go!"db" :: allW64.map snap.snapDBName

theorem snapNames_nodup : snapNames.Nodup := by
  unfold snapNames
  refine List.nodup_cons.2 ⟨?_, ?_⟩
  · intro hm
    obtain ⟨i, -, hi⟩ := List.mem_map.1 hm
    have := snapDBName_length i
    rw [hi] at this
    exact absurd this (by decide)
  · exact nodup_map_on _ _ (fun a _ b _ h => snapDBName_inj h) allW64_nodup

theorem snapNames_ok {dd : GoString} (hd : DirFits dd) :
    ∀ b ∈ snapNames, NameOk b ∧ PathFits (child (config.snapDirOf dd) b) := by
  intro b hb
  unfold snapNames at hb
  rcases List.mem_cons.1 hb with rfl | hb
  · exact ⟨nameOk_db, config.pathFits_snapDir_child hd (by decide)⟩
  · obtain ⟨i, -, rfl⟩ := List.mem_map.1 hb
    exact ⟨snap.snapDBName_nameOk i, snap.pathFits_snapDBPath hd i⟩

end pure

/-! ### A list as a map -/

section map
variable {PROP : Type _} [BI PROP] [BIAffine PROP]

/-- **A big separating conjunction over a duplicate-free list of indices, as one over a map** whose
keys are the list's. -/
theorem sepL_toMap (Φ : w64 → PROP) : ∀ l : List w64, l.Nodup →
    ([∗list] i ∈ l, Φ i) ⊢ ∃ F : GMap w64 Unit, ⌜∀ i, F !! i ≠ none ↔ i ∈ l⌝ ∗
      [∗map] i ↦ _x ∈ F, Φ i
  | [], _ => by
    iintro -
    iexists ∅
    isplitl []
    · ipureintro; intro i; simp
    iapply BigSepM.bigSepM_empty.2; iempintro
  | i :: l, hl => by
    have hl' := List.nodup_cons.1 hl
    iintro H
    icases (BigSepL.bigSepL_cons).1 $$ H with ⟨Hi, Hl⟩
    icases sepL_toMap Φ l hl'.2 $$ Hl with ⟨%F, %hF, HF⟩
    have hFi : F !! i = none := by
      cases hc : F !! i with
      | none => rfl
      | some u => exact absurd ((hF i).1 (by rw [hc]; simp)) hl'.1
    iexists GMap.insert i () F
    isplitl []
    · ipureintro; intro k
      by_cases hk : i = k
      · subst hk; simp [GMap.lookup_insert]
      · rw [GMap.lookup_insert_ne _ _ hk, hF k]
        simp only [List.mem_cons]
        constructor
        · exact Or.inr
        · rintro (rfl | h)
          · exact absurd rfl hk
          · exact h
    iapply (BigSepM.bigSepM_insert hFi).2
    iframe Hi HF

end map

/-! ### Carving the claims -/

section carve
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The free names of an empty directory, one claim each** (see the file header). -/
theorem carveFree (R : Roots) (d : GoString) (j : Ino) (E : CoPset) (hE : ↑osShN ⊆ E) :
    ∀ (l X : List GoString) (q qc : Qp) (h : NamesH), l.Nodup → (∀ b ∈ l, b ∉ X) →
    (∀ b ∈ l, NameOk b ∧ PathFits (child d b)) → (∀ b, h.cur !! b = none) →
    ⊢ osInv (GF := GF) -∗ osSharedInv R -∗ osPathS R d (DFrac.own q) j -∗
      osCallPerm (callKey R d) qc -∗ osNames j (.except X) (DFrac.own 1) h ={E}=∗
      [∗list] b ∈ l, backend.fileFreeF (child d b)
  | [], _, _, _, _, _, _, _, _ => by
    iintro #Hinv #Hsh Hp Hc Hn
    imodintro
    iapply BigSepL.bigSepL_nil.2; iempintro
  | b :: l, X, q, qc, h, hl, hX, hok, hcur => by
    iintro #Hinv #Hsh Hp Hc Hn
    have hbX : b ∉ X := hX b (List.mem_cons_self ..)
    imod osNames_split R j (.except X) [b] h hE $$ Hsh Hn with ⟨Hb, Hr⟩
    have hb : (NameSet.except X).inter [b] = .only [b] := by
      simp only [NameSet.inter, List.filter_cons, List.filter_nil]
      simp [hbX]
    have hd : (NameSet.except X).diff [b] = .except (X ++ [b]) := rfl
    rw [hb, hd]
    rw [← Qp.half_add_half q, ← Qp.half_add_half qc]
    icases (osPathS_frac R d q.half q.half j).1 $$ Hp with ⟨Hp1, Hp2⟩
    icases (osCallPerm_split (callKey R d) qc.half qc.half).1 $$ Hc with ⟨Hc1, Hc2⟩
    have hl' := List.nodup_cons.1 hl
    imod carveFree R d j E hE l (X ++ [b]) q.half qc.half (h.restrict j (.except (X ++ [b]))) hl'.2
      (fun c hc hm => by
        rcases List.mem_append.1 hm with h' | h'
        · exact hX c (List.mem_cons_of_mem _ hc) h'
        · rw [List.mem_singleton] at h'; subst h'; exact hl'.1 hc)
      (fun c hc => hok c (List.mem_cons_of_mem _ hc))
      (fun c => restrictN_none _ _ hcur c) $$ Hinv Hsh Hp2 Hc2 Hr with Hl
    imodintro
    iapply BigSepL.bigSepL_cons.2
    iframe Hl
    unfold backend.fileFreeF
    iexists R, d, b, DFrac.own q.half, j, qc.half, h.restrict j (.only [b])
    iframe Hinv Hsh Hp1 Hc1 Hb
    ipureintro
    exact ⟨rfl, (hok b (List.mem_cons_self ..)).1, restrictN_none _ _ hcur b,
      (hok b (List.mem_cons_self ..)).2⟩

/-- **The new snapshot directory's claims** (see the file header): the backend file's free name and
every index's snapshot file's, from the whole of the empty directory `config.snapDirOf dd`. -/
-- (the kernel's check exceeded the default heartbeats on the VM's build, 2026-11-24)
set_option maxHeartbeats 0 in
theorem snapDir_carve (R : Roots) (dd : GoString) (J : Ino) (q qc : Qp) (h : NamesH)
    (hd : DirFits dd) (hcur : ∀ b, h.cur !! b = none) :
    ⊢ osInv (GF := GF) -∗ osSharedInv R -∗ osPathS R (config.snapDirOf dd) (DFrac.own q) J -∗
      osCallPerm (callKey R (config.snapDirOf dd)) qc -∗ osNames J (.except []) (DFrac.own 1) h ={⊤}=∗
      backend.fileFreeF (config.backendPathOf dd) ∗
      ∃ F : GMap w64 Unit, ⌜∀ i, F !! i ≠ none⌝ ∗
        [∗map] i ↦ _x ∈ F, backend.fileFreeF (snap.snapDBPath (config.snapDirOf dd) i) := by
  iintro #Hinv #Hsh Hp Hc Hn
  imod carveFree R (config.snapDirOf dd) J ⊤ CoPset.subseteq_top snapNames [] q qc h
    snapNames_nodup (fun _ _ h => by simp at h) (snapNames_ok hd) hcur $$ Hinv Hsh Hp Hc Hn with Hl
  unfold snapNames
  icases (BigSepL.bigSepL_cons).1 $$ Hl with ⟨Hdb, Hl⟩
  rw [BigSepL.bigSepL_map]
  simp only [snapDBPath_child, backendPathOf_child]
  icases sepL_toMap (fun i => backend.fileFreeF (GF := GF) (child (config.snapDirOf dd) (snap.snapDBName i)))
    allW64 allW64_nodup $$ Hl with ⟨%F, %hF, HF⟩
  imodintro
  iframe Hdb
  iexists F
  iframe HF
  ipureintro
  intro i
  exact (hF i).2 (mem_allW64 i)

end carve

end bootSnap
end EtcdGrove
end Perennial
