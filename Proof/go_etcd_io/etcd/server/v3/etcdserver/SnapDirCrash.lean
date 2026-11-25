/-
**The snapshot directory across a crash** (D6-T6, P7, 2026-11-25; `notes/etcd-dist-d6.md` §T6, rounds 1-4).
Lean-first. A defs module: the crash law of the snapshot directory's invariant (`snapDirKeep`,
`Proof/.../rafthttp/Net.lean`), which the member's crash law (T7, `memberGen_crash_law_holds`) applies.

What Go does (fork `8c28a4296`, `server/etcdserver/api/snap/`): `SaveDBFrom` writes a temporary file, syncs
it, links it at `<index>.snap.db` and syncs the directory before returning; `ReleaseSnapDBs` removes files
below an index with no sync. So after a crash a saved file is there, whole; a file linked but not yet synced
is there, whole, or absent; a removed file may be back (`nonissues/etcd-snapdb-removed-before-dirsync.md`).
The invariant's body (`snapDirBody`) records exactly that: saved (`E`) means durable (`fileAtDur`), the
other files are pending (`fileAtPend`), the free names are free in every crash (`fileFreeDur`), a saved index
without a file has its removal fact `Rm`.

* `snapSlot sd J V i`: the new generation's claim on index `i`'s name in the snapshot directory `J`, fresh
  (`namesOf V`, nothing logged), with its path and a share of its call permission: what the member's
  restart carves from the new generation's claim on the directory.
* `snapDirKept R V' sd` (persistent, T7's obligation): the crash kept the snapshot directory, i.e. every
  directory the old generation resolves `sd` to (`osPathS`) is the one the crashed tree resolves it to
  (`lookupH R V' sd`). True of Go: `TouchDirAll(MemberDir())` and `TouchDirAll(SnapDir())` sync the parent
  of each directory they make (`fileutil.go:49-85`, F-N2) and ext4 commits the whole journal (coordinator's
  decision (b) on #50, 2026-11-25: a premise, not a field of `snap.snapDirOwn`).
* `snapDir_crash.law` / `snapDir_crash_law_holds`: from the old generation's `snapDirKeep` (with `crashed`
  and a later credit), the removal facts' weakening `Rm → Rm'` and the image's `img → img'`, `snapDirKept`, the file system's restart
  resources (`crashRest`) and the new generation's `snap.snapDirOwn` and slots, the new generation's
  `snapDirKeep` at `Rm'`, with the files it kept taken from `crashRest`. Per index (`snapStep`): a durable
  file comes back whole under its name; a pending one comes back whole (and stays pending) or is gone (its
  name then free); a free name stays free; the name of a saved index without a file is dropped.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BootSnapCarve
import all Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Net

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace snapCrash

open Iris Iris.BI Iris.ProofMode Fs backend

/-! ### Options as resources -/

section opt
variable {PROP : Type _} [BI PROP] [BIAffine PROP]

/-- `Φ i x` when `f i = some x`, nothing otherwise. -/
def optF {α : Type} (f : w64 → Option α) (Φ : w64 → α → PROP) (i : w64) : PROP :=
  match f i with
  | some x => Φ i x
  | none => emp

theorem optF_some {α : Type} {f : w64 → Option α} {Φ : w64 → α → PROP} {i : w64} {x : α}
    (h : f i = some x) : optF f Φ i = Φ i x := by
  unfold optF; rw [h]

theorem optF_none {α : Type} {f : w64 → Option α} {Φ : w64 → α → PROP} {i : w64}
    (h : f i = none) : optF f Φ i = emp := by
  unfold optF; rw [h]

/-- A big separating conjunction over a list, its terms equal on the list's elements. -/
theorem sepL_congr (Φ Ψ : w64 → PROP) : ∀ (l : List w64), (∀ k ∈ l, Φ k = Ψ k) →
    ([∗list] k ∈ l, Φ k) ⊢ [∗list] k ∈ l, Ψ k
  | [], _ => .rfl
  | k :: l, h => by
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨Hk, H⟩
    iapply BigSepL.bigSepL_cons.2
    rw [← h k (List.mem_cons_self ..)]
    iframe Hk
    iapply sepL_congr Φ Ψ l (fun k' hk' => h k' (List.mem_cons_of_mem _ hk')) $$ H

/-- A map's big separating conjunction, over a duplicate-free list having its keys. -/
theorem map_toList {α : Type} (Φ : w64 → α → PROP) :
    ∀ (l : List w64) (M : GMap w64 α), l.Nodup → (∀ i, M !! i ≠ none → i ∈ l) →
    ([∗map] i ↦ x ∈ M, Φ i x) ⊢ [∗list] i ∈ l, optF (M !! ·) Φ i
  | [], M, _, hM => by
    have hM0 : M = ∅ := GMap.ext (fun i => by
      rw [GMap.lookup_empty]
      cases h : M !! i with
      | none => rfl
      | some _ => exact absurd (hM i (by rw [h]; simp)) (by simp))
    subst hM0
    iintro -
    iapply BigSepL.bigSepL_nil.2; iempintro
  | i :: l, M, hl, hM => by
    have hl' := List.nodup_cons.1 hl
    cases hMi : M !! i with
    | none =>
      have hM' : ∀ k, M !! k ≠ none → k ∈ l := fun k hk => by
        rcases List.mem_cons.1 (hM k hk) with rfl | h
        · exact absurd hMi hk
        · exact h
      iintro H
      iapply BigSepL.bigSepL_cons.2
      isplitr
      · rw [optF_none (f := (M !! ·)) hMi]; iempintro
      iapply map_toList Φ l M hl'.2 hM' $$ H
    | some x =>
      have hM' : ∀ k, (GMap.delete i M) !! k ≠ none → k ∈ l := fun k hk => by
        by_cases hik : i = k
        · subst hik; exact absurd (GMap.lookup_delete M i) hk
        · rw [GMap.lookup_delete_ne M hik] at hk
          rcases List.mem_cons.1 (hM k hk) with rfl | h
          · exact absurd rfl hik
          · exact h
      iintro H
      icases (BigSepM.bigSepM_delete (Φ := Φ) hMi).1 $$ H with ⟨Hi, H⟩
      iapply BigSepL.bigSepL_cons.2
      isplitl [Hi]
      · rw [optF_some (f := (M !! ·)) hMi]; iexact Hi
      ihave H := map_toList Φ l (GMap.delete i M) hl'.2 hM' $$ H
      iapply sepL_congr _ _ l (fun k hk => by
        have hik : i ≠ k := fun h => hl'.1 (by rw [h]; exact hk)
        unfold optF
        simp only [GMap.lookup_delete_ne M hik]) $$ H

/-- A big separating conjunction over a duplicate-free list, as one over the map of the list's
elements to `f`'s values. -/
theorem list_toMap {α : Type} (f : w64 → Option α) (Φ : w64 → α → PROP) :
    ∀ (l : List w64), l.Nodup →
    ([∗list] i ∈ l, optF f Φ i) ⊢ ∃ M : GMap w64 α, ⌜∀ i, i ∈ l → M !! i = f i⌝ ∗
      ⌜∀ i, i ∉ l → M !! i = none⌝ ∗ [∗map] i ↦ x ∈ M, Φ i x
  | [], _ => by
    iintro -
    iexists ∅
    isplitr
    · ipureintro; intro i h; simp at h
    isplitr
    · ipureintro; intro i _; exact GMap.lookup_empty i
    iapply BigSepM.bigSepM_empty.2; iempintro
  | i :: l, hl => by
    have hl' := List.nodup_cons.1 hl
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨Hi, H⟩
    icases list_toMap f Φ l hl'.2 $$ H with ⟨%M, %hM, %hM', HM⟩
    have hMi : M !! i = none := hM' i hl'.1
    cases hfi : f i with
    | none =>
      iexists M
      isplitr
      · ipureintro; intro k hk
        rcases List.mem_cons.1 hk with rfl | hk
        · rw [hMi, hfi]
        · exact hM k hk
      isplitr
      · ipureintro; intro k hk; exact hM' k (fun h => hk (List.mem_cons_of_mem _ h))
      iexact HM
    | some x =>
      rw [optF_some hfi]
      iexists GMap.insert i x M
      isplitr
      · ipureintro; intro k hk
        by_cases hik : i = k
        · subst hik; rw [GMap.lookup_insert, hfi]
        · rw [GMap.lookup_insert_ne _ _ hik]
          rcases List.mem_cons.1 hk with rfl | hk
          · exact absurd rfl hik
          · exact hM k hk
      isplitr
      · ipureintro; intro k hk
        have hik : i ≠ k := fun h => hk (by rw [← h]; exact List.mem_cons_self ..)
        rw [GMap.lookup_insert_ne _ _ hik]; exact hM' k (fun h => hk (List.mem_cons_of_mem _ h))
      iapply (BigSepM.bigSepM_insert hMi).2
      iframe Hi HM

end opt

/-! ### The new generation's slots and T7's obligation -/

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `snapSlot` at the file extension's instances. -/
def snapSlotF [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] (sd : GoString) (J : Ino) (V : Hist)
    (i : w64) : IProp GF :=
  iprop(∃ (R : Roots) (dq : DFrac) (qc : Qp), osInv ∗ osSharedInv R ∗ osPathS R sd dq J ∗
    osCallPerm (callKey R sd) qc ∗
    osNames J (.only [snap.snapDBName i]) (DFrac.own 1) (namesOf V J (.only [snap.snapDBName i])) ∗
    ⌜PathFits (snap.snapDBPath sd i)⌝)

/-- **The generation's fresh claim on index `i`'s name in the snapshot directory `J`** (see the file
header), at the program's instances (`backend.onFs`). -/
def snapSlot (sd : GoString) (J : Ino) (V : Hist) (i : w64) : IProp GF := onFs (snapSlotF sd J V i)

/-- `snapDirKept` at the file extension's instances. -/
def snapDirKeptF [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] (R : Roots) (V' : Hist)
    (sd : GoString) : IProp GF :=
  iprop(□ ∀ (R0 : Roots) (dq : DFrac) (j : Ino), osSharedInv R0 -∗ osPathS R0 sd dq j -∗
    ⌜lookupH R V' sd = some (.dir j)⌝)

/-- **The crash kept the snapshot directory** (persistent; T7's obligation, see the file header): every
directory this generation resolves `sd` to is the one the crashed tree `V'` (under the roots `R`)
resolves it to. -/
def snapDirKept (R : Roots) (V' : Hist) (sd : GoString) : IProp GF := onFs (snapDirKeptF R V' sd)

instance snapDirKeptF_persistent [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] (R : Roots) (V' : Hist)
    (sd : GoString) : Persistent (snapDirKeptF (GF := GF) R V' sd) := by
  unfold snapDirKeptF; infer_instance

end defs

/-! ### One index across the crash -/

section step
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable {GF : BundledGFunctors} [G : GooseGlobalGS HasLC.hasLC GF]

theorem child_inj {d d' b b' : GoString} (hb : NameOk b) (hb' : NameOk b')
    (h : child d b = child d' b') : d = d' ∧ b = b' := by
  have h1 := congrArg baseOf h
  rw [baseOf_child' _ _ hb, baseOf_child' _ _ hb'] at h1
  subst h1
  have h2 := congrArg parentOf h
  rw [parentOf_child' _ _ hb, parentOf_child' _ _ hb] at h2
  exact ⟨Option.some.inj h2, rfl⟩

/-- A file at `p` survives as a file at `p` with any weaker crash promise. -/
theorem fileAtCrashF_mono (L : GooseLocalGS GF) (p : GoString) (D : Data)
    (P P' : Ino → Option Node → Prop) (hP : ∀ x v, P x v → P' x v) :
    fileAtCrashF (hG := ⟨G, L⟩) p D P ⊢ fileAtCrashF (hG := ⟨G, L⟩) p D P' := by
  unfold fileAtCrashF nameCrash
  iintro ⟨%R, %d, %b, %dq, %j, %qc, %h, %x, %hp, #Hinv, #Hsh, Hp, Hc, Hn, ⟨%n, #Hlb, %hc⟩, Hf⟩
  iexists R, d, b, dq, j, qc, h, x
  iframe Hinv Hsh Hp Hc Hn Hf
  isplitr
  · ipureintro; exact hp
  iexists n
  iframe Hlb
  ipureintro; exact crashLeaves_mono hc (hP x)

/-- The old generation's claim on index `i`'s name is in the directory the crashed tree has at `sd`. -/
theorem old_dir (L : GooseLocalGS GF) (R R0 : Roots) (V' : Hist) (sd d b : GoString) (i : w64)
    (J j : Ino) (dq : DFrac) (hJ : lookupH R V' sd = some (.dir J)) (hb : NameOk b)
    (hp : snap.snapDBPath sd i = child d b) :
    ⊢ snapDirKeptF (hG := ⟨G, L⟩) R V' sd -∗ osSharedInv (L := L) R0 -∗
      osPathS (L := L) R0 d dq j -∗ ⌜d = sd ∧ b = snap.snapDBName i ∧ j = J⌝ := by
  rw [bootSnap.snapDBPath_child] at hp
  obtain ⟨rfl, rfl⟩ := child_inj (snap.snapDBName_nameOk i) hb hp
  unfold snapDirKeptF
  iintro #Hk #Hsh Hp
  ihave %h := Hk $$ %R0 %dq %j Hsh Hp
  ipureintro
  rw [hJ] at h
  cases h
  exact ⟨rfl, rfl, rfl⟩

/-- **A file of the old generation at index `i`, across the crash** (see the file header): what the
crash promised of its name (`P`, durable or pending), and the name now nothing (the new slot becomes a
free name, free in every crash: nothing is logged) or the file (taken from `crashRest`, whole, with the
new slot). -/
theorem step_file (Q : OsState → OsState → Prop) (L L' : GooseLocalGS GF) (Dl : List Ino) (tt : Bool)
    (V' : Hist) (hV : V'.2 = []) (R : Roots) (J : Ino) (sd : GoString) (i : w64) (Dt : Data)
    (hJ : lookupH R V' sd = some (.dir J))
    (hDl : ∀ x ∈ Dl, V'.now.entry J (snap.snapDBName i) ≠ some (.file x))
    (P : Ino → Option Node → Prop) (hP : ∀ x v, P x v → v = none ∨ v = some (.file x)) :
    ⊢ snapDirKeptF (hG := ⟨G, L⟩) R V' sd -∗
      crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) Dl tt V' -∗
      fileAtCrashF (hG := ⟨G, L⟩) (snap.snapDBPath sd i) Dt P -∗
      snapSlotF (hG := ⟨G, L'⟩) sd J V' i ={⊤}=∗
      ∃ Dn : List Ino, ⌜∀ x ∈ Dn, V'.now.entry J (snap.snapDBName i) = some (.file x)⌝ ∗
        ⌜∃ x, P x (V'.now.entry J (snap.snapDBName i))⌝ ∗
        crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) (Dn ++ Dl) tt V' ∗
        ((⌜V'.now.entry J (snap.snapDBName i) = none⌝ ∗
            fileFreeDurF (hG := ⟨G, L'⟩) (snap.snapDBPath sd i)) ∨
          (⌜(V'.now.entry J (snap.snapDBName i)).isSome⌝ ∗
            fileAtCrashF (hG := ⟨G, L'⟩) (snap.snapDBPath sd i) Dt durNamed)) := by
  iintro #Hk Hcr Hf Hs
  unfold fileAtCrashF
  icases Hf with ⟨%R0, %d, %b, %dq, %j, %qc, %h, %x, %hp, -, #Hsh, Hp, -, Hn, #Hnc, Hfh⟩
  obtain ⟨hpe, hb, -, -⟩ := hp
  ihave %hdj := old_dir L R R0 V' sd d b i J j dq hJ hb hpe $$ Hk Hsh Hp
  obtain ⟨hd, hbn, hjJ⟩ := hdj
  subst d b j
  imod nameCrash_crash Q L L' Dl tt V' R0 J (snap.snapDBName i) (DFrac.own 1) h (P x) ⊤
    CoPset.subseteq_top $$ Hsh Hcr Hn Hnc with ⟨%hPv, Hcr, -⟩
  unfold snapSlotF
  icases Hs with ⟨%R', %dq', %qc', #Hinv', #Hsh', Hp', Hc', Hn', %hfits'⟩
  imod osCommitLb_zero (L := L') with #H0
  have hcur := namesOf_cur V' J (snap.snapDBName i)
  rcases hP x _ hPv with hv | hv
  · imodintro
    iexists []
    rw [List.nil_append]
    iframe Hcr
    isplitr
    · ipureintro; intro y hy; simp at hy
    isplitr
    · ipureintro; exact ⟨x, hPv⟩
    ileft
    isplitr
    · ipureintro; exact hv
    unfold fileFreeDurF nameCrash
    iexists R', sd, snap.snapDBName i, dq', J, qc', namesOf V' J (.only [snap.snapDBName i])
    iframe Hinv' Hsh' Hp' Hc' Hn'
    isplitr
    · ipureintro
      exact ⟨bootSnap.snapDBPath_child sd i, snap.snapDBName_nameOk i, by rw [hcur, hv], hfits'⟩
    iexists 0
    iframe H0
    ipureintro
    exact crashLeaves_mono (crashLeaves_fresh V' hV J (snap.snapDBName i)) (fun v h => h.trans hv)
  · have hx : x ∉ Dl := fun hm => hDl x hm hv
    have hnm : Named V'.now x := ⟨J, snap.snapDBName i, hv⟩
    icases fileHoldsMDur_crash Q L L' Dl tt V' x hx hnm Dt $$ Hcr Hfh with ⟨Hfh', Hcr⟩
    imodintro
    iexists [x]
    rw [List.singleton_append]
    iframe Hcr
    isplitr
    · ipureintro; intro y hy; simp at hy; subst hy; exact hv
    isplitr
    · ipureintro; exact ⟨x, hPv⟩
    iright
    isplitr
    · ipureintro; rw [hv]; rfl
    unfold nameCrash
    iexists R', sd, snap.snapDBName i, dq', J, qc', namesOf V' J (.only [snap.snapDBName i]), x
    iframe Hinv' Hsh' Hp' Hc' Hn' Hfh'
    isplitr
    · ipureintro
      exact ⟨bootSnap.snapDBPath_child sd i, snap.snapDBName_nameOk i, by rw [hcur, hv], hfits'⟩
    iexists 0
    iframe H0
    ipureintro
    exact crashLeaves_mono (crashLeaves_fresh V' hV J (snap.snapDBName i)) (fun v h => h.trans hv)

/-- **A free name of the old generation at index `i`, across the crash**: still free, a free name of the
new generation (nothing logged). -/
theorem step_free (Q : OsState → OsState → Prop) (L L' : GooseLocalGS GF) (Dl : List Ino) (tt : Bool)
    (V' : Hist) (hV : V'.2 = []) (R : Roots) (J : Ino) (sd : GoString) (i : w64)
    (hJ : lookupH R V' sd = some (.dir J)) :
    ⊢ snapDirKeptF (hG := ⟨G, L⟩) R V' sd -∗
      crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) Dl tt V' -∗
      fileFreeDurF (hG := ⟨G, L⟩) (snap.snapDBPath sd i) -∗
      snapSlotF (hG := ⟨G, L'⟩) sd J V' i ={⊤}=∗
      ⌜V'.now.entry J (snap.snapDBName i) = none⌝ ∗
      crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) Dl tt V' ∗
      fileFreeDurF (hG := ⟨G, L'⟩) (snap.snapDBPath sd i) := by
  iintro #Hk Hcr Hf Hs
  unfold fileFreeDurF
  icases Hf with ⟨%R0, %d, %b, %dq, %j, %qc, %h, %hp, -, #Hsh, Hp, -, Hn, #Hnc⟩
  obtain ⟨hpe, hb, -, -⟩ := hp
  ihave %hdj := old_dir L R R0 V' sd d b i J j dq hJ hb hpe $$ Hk Hsh Hp
  obtain ⟨hd, hbn, hjJ⟩ := hdj
  subst d b j
  imod nameCrash_crash Q L L' Dl tt V' R0 J (snap.snapDBName i) (DFrac.own 1) h (· = none) ⊤
    CoPset.subseteq_top $$ Hsh Hcr Hn Hnc with ⟨%hv, Hcr, -⟩
  unfold snapSlotF
  icases Hs with ⟨%R', %dq', %qc', #Hinv', #Hsh', Hp', Hc', Hn', %hfits'⟩
  imod osCommitLb_zero (L := L') with #H0
  have hcur := namesOf_cur V' J (snap.snapDBName i)
  imodintro
  iframe Hcr
  isplitr
  · ipureintro; exact hv
  unfold nameCrash
  iexists R', sd, snap.snapDBName i, dq', J, qc', namesOf V' J (.only [snap.snapDBName i])
  iframe Hinv' Hsh' Hp' Hc' Hn'
  isplitr
  · ipureintro
    exact ⟨bootSnap.snapDBPath_child sd i, snap.snapDBName_nameOk i, by rw [hcur, hv], hfits'⟩
  iexists 0
  iframe H0
  ipureintro
  exact crashLeaves_mono (crashLeaves_fresh V' hV J (snap.snapDBName i)) (fun v h => h.trans hv)

end step


/-! ### Every index across the crash -/

section pureKeep
variable [GooseExts]

open Classical in
/-- Index `i`'s file is kept: the crashed tree names something there, or the index was saved (durable). -/
def keepP (V' : Hist) (J : Ino) (E : GMap w64 Unit) (i : w64) : Prop :=
  (V'.now.entry J (snap.snapDBName i)).isSome ∨ E !! i ≠ none

open Classical in
/-- The new generation's files: the old ones kept. -/
def keepM (V' : Hist) (J : Ino) (E : GMap w64 Unit) (M : GMap w64 Data) (i : w64) : Option Data :=
  match M !! i with
  | some D => if keepP V' J E i then some D else none
  | none => none

open Classical in
/-- The new generation's free names: the old ones, and the names of the pending files gone. -/
def keepF (V' : Hist) (J : Ino) (E : GMap w64 Unit) (M : GMap w64 Data) (F : GMap w64 Unit)
    (i : w64) : Option Unit :=
  match M !! i with
  | some _ => if keepP V' J E i then none else some ()
  | none => F !! i

end pureKeep

section loop
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable {GF : BundledGFunctors} [G : GooseGlobalGS HasLC.hasLC GF]

/-- A file of the directory at the instances (`snapFileAt`'s body, with its certificate). -/
def fileOldF (L : GooseLocalGS GF) (sd : GoString) (img : w64 → Data → IProp GF) (E : GMap w64 Unit)
    (i : w64) (D : Data) : IProp GF :=
  iprop(((⌜E !! i ≠ none⌝ ∗ fileAtCrashF (hG := ⟨G, L⟩) (snap.snapDBPath sd i) D durNamed) ∨
    (⌜E !! i = none⌝ ∗ fileAtCrashF (hG := ⟨G, L⟩) (snap.snapDBPath sd i) D pendNamed)) ∗ □ img i D)

/-- What the old generation holds at index `i`. -/
def oldAt (L : GooseLocalGS GF) (sd : GoString) (img : w64 → Data → IProp GF) (E : GMap w64 Unit)
    (M : GMap w64 Data) (F : GMap w64 Unit) (i : w64) : IProp GF :=
  iprop(optF (M !! ·) (fun i D => fileOldF L sd img E i D) i ∗
    optF (F !! ·) (fun i _ => fileFreeDurF (hG := ⟨G, L⟩) (snap.snapDBPath sd i)) i)

/-- What the new generation holds at index `i`. -/
def newAt (L' : GooseLocalGS GF) (V' : Hist) (J : Ino) (sd : GoString) (img : w64 → Data → IProp GF)
    (E : GMap w64 Unit) (M : GMap w64 Data) (F : GMap w64 Unit) (i : w64) : IProp GF :=
  iprop(optF (keepM V' J E M) (fun i D => fileOldF L' sd img E i D) i ∗
    optF (keepF V' J E M F) (fun i _ => fileFreeDurF (hG := ⟨G, L'⟩) (snap.snapDBPath sd i)) i)

/-- **Index `i` across the crash** (see the file header). -/
theorem step_index (Q : OsState → OsState → Prop) (L L' : GooseLocalGS GF) (Dl : List Ino) (tt : Bool)
    (V' : Hist) (hV : V'.2 = []) (R : Roots) (J : Ino) (sd : GoString) (img : w64 → Data → IProp GF)
    (E : GMap w64 Unit) (M : GMap w64 Data) (F : GMap w64 Unit)
    (hMF : ∀ i, F !! i ≠ none ↔ (E !! i = none ∧ M !! i = none)) (i : w64)
    (hJ : lookupH R V' sd = some (.dir J))
    (hDl : ∀ x ∈ Dl, V'.now.entry J (snap.snapDBName i) ≠ some (.file x)) :
    ⊢ snapDirKeptF (hG := ⟨G, L⟩) R V' sd -∗
      crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) Dl tt V' -∗
      oldAt L sd img E M F i -∗ snapSlotF (hG := ⟨G, L'⟩) sd J V' i ={⊤}=∗
      ∃ Dn : List Ino, ⌜∀ x ∈ Dn, V'.now.entry J (snap.snapDBName i) = some (.file x)⌝ ∗
        crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) (Dn ++ Dl) tt V' ∗
        newAt L' V' J sd img E M F i := by
  classical
  iintro #Hk Hcr Ho Hs
  unfold oldAt newAt
  icases Ho with ⟨HoM, HoF⟩
  cases hMi : M !! i with
  | some D =>
    have hFi : F !! i = none := by
      cases h : F !! i with
      | none => rfl
      | some _ => exact absurd ((hMF i).1 (by rw [h]; simp)).2 (by rw [hMi]; simp)
    rw [optF_some (f := (M !! ·)) hMi]
    unfold fileOldF
    icases HoM with ⟨Hd, #Himg⟩
    icases Hd with (⟨%hE, Hf⟩ | ⟨%hE, Hf⟩)
    · imod step_file Q L L' Dl tt V' hV R J sd i D hJ hDl durNamed
        (fun x v h => Or.inr h) $$ Hk Hcr Hf Hs with ⟨%Dn, %hDn, %hPx, Hcr, Hout⟩
      obtain ⟨x, hPx⟩ := hPx
      have hkp : keepP V' J E i := Or.inr hE
      have hkM : keepM V' J E M i = some D := by simp [keepM, hMi, hkp]
      have hkF : keepF V' J E M F i = none := by simp [keepF, hMi, hkp]
      rw [optF_some hkM, optF_none hkF]
      icases Hout with (⟨%hv, -⟩ | ⟨-, Hf⟩)
      · exfalso; unfold durNamed at hPx; rw [hv] at hPx; cases hPx
      imodintro
      iexists Dn
      iframe Hcr
      isplitr
      · ipureintro; exact hDn
      isplitl [Hf]
      · isplitl [Hf]
        · ileft; iframe Hf; ipureintro; exact hE
        iexact Himg
      iempintro
    · imod step_file Q L L' Dl tt V' hV R J sd i D hJ hDl pendNamed
        (fun x v h => h) $$ Hk Hcr Hf Hs with ⟨%Dn, %hDn, -, Hcr, Hout⟩
      icases Hout with (⟨%hv, Hfr⟩ | ⟨%hv, Hf⟩)
      · have hkp : ¬ keepP V' J E i := by
          unfold keepP; rw [hv]; simp [hE]
        have hkM : keepM V' J E M i = none := by simp [keepM, hMi, hkp]
        have hkF : keepF V' J E M F i = some () := by simp [keepF, hMi, hkp]
        rw [optF_none hkM, optF_some hkF]
        imodintro
        iexists Dn
        iframe Hcr Hfr
        ipureintro; exact hDn
      · have hkp : keepP V' J E i := Or.inl hv
        have hkM : keepM V' J E M i = some D := by simp [keepM, hMi, hkp]
        have hkF : keepF V' J E M F i = none := by simp [keepF, hMi, hkp]
        rw [optF_some hkM, optF_none hkF]
        imodintro
        iexists Dn
        iframe Hcr
        isplitr
        · ipureintro; exact hDn
        isplitl [Hf]
        · isplitl [Hf]
          · iright
            isplitr
            · ipureintro; exact hE
            iapply fileAtCrashF_mono L' _ _ durNamed pendNamed (fun x v h => Or.inr h) $$ Hf
          iexact Himg
        iempintro
  | none =>
    have hkM : keepM V' J E M i = none := by unfold keepM; rw [hMi]
    have hkF : keepF V' J E M F i = F !! i := by unfold keepF; rw [hMi]
    rw [optF_none hkM]
    cases hFi : F !! i with
    | some u =>
      rw [optF_some (f := (F !! ·)) hFi, optF_some (f := keepF V' J E M F) (hkF.trans hFi)]
      imod step_free Q L L' Dl tt V' hV R J sd i hJ $$ Hk Hcr HoF Hs with ⟨-, Hcr, Hfr⟩
      imodintro
      iexists []
      rw [List.nil_append]
      iframe Hcr Hfr
      ipureintro; intro x hx; simp at hx
    | none =>
      rw [optF_none (f := keepF V' J E M F) (hkF.trans hFi)]
      imodintro
      iexists []
      rw [List.nil_append]
      iframe Hcr
      ipureintro; exact ⟨fun x hx => by simp at hx, trivial, trivial⟩

/-- **Every index of `l` across the crash**: the files the crash kept taken from `crashRest` one by one (a
file is named once in the crashed tree: `TreeWf`). -/
theorem loop (Q : OsState → OsState → Prop) (L L' : GooseLocalGS GF) (tt : Bool)
    (V' : Hist) (hV : V'.2 = []) (R : Roots) (J : Ino) (sd : GoString) (img : w64 → Data → IProp GF)
    (E : GMap w64 Unit) (M : GMap w64 Data) (F : GMap w64 Unit)
    (hMF : ∀ i, F !! i ≠ none ↔ (E !! i = none ∧ M !! i = none))
    (hJ : lookupH R V' sd = some (.dir J))
    (huniq : ∀ j1 b1 j2 b2 n, V'.now.entry j1 b1 = some n → V'.now.entry j2 b2 = some n →
      j1 = j2 ∧ b1 = b2) :
    ∀ (l : List w64) (Dl : List Ino), l.Nodup →
    (∀ x ∈ Dl, ∀ i ∈ l, V'.now.entry J (snap.snapDBName i) ≠ some (.file x)) →
    ⊢ snapDirKeptF (hG := ⟨G, L⟩) R V' sd -∗
      crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) Dl tt V' -∗
      ([∗list] i ∈ l, oldAt L sd img E M F i ∗ snapSlotF (hG := ⟨G, L'⟩) sd J V' i) ={⊤}=∗
      ∃ D' : List Ino, crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) (D' ++ Dl) tt V' ∗
        [∗list] i ∈ l, newAt L' V' J sd img E M F i
  | [], Dl, _, _ => by
    iintro #Hk Hcr -
    imodintro
    iexists []
    rw [List.nil_append]
    iframe Hcr
    iapply BigSepL.bigSepL_nil.2; iempintro
  | i :: l, Dl, hl, hDl => by
    have hl' := List.nodup_cons.1 hl
    iintro #Hk Hcr H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨⟨Ho, Hs⟩, H⟩
    imod step_index Q L L' Dl tt V' hV R J sd img E M F hMF i hJ
      (fun x hx => hDl x hx i (List.mem_cons_self ..)) $$ Hk Hcr Ho Hs with ⟨%Dn, %hDn, Hcr, Hn⟩
    imod loop Q L L' tt V' hV R J sd img E M F hMF hJ huniq l (Dn ++ Dl) hl'.2
      (fun x hx i' hi' he => by
        rcases List.mem_append.1 hx with hx | hx
        · have h1 := hDn x hx
          obtain ⟨-, hb⟩ := huniq _ _ _ _ _ he h1
          have := bootSnap.snapDBName_inj hb
          subst this; exact hl'.1 hi'
        · exact hDl x hx i' (List.mem_cons_of_mem _ hi') he) $$ Hk Hcr H with ⟨%D', Hcr, H⟩
    imodintro
    iexists D' ++ Dn
    rw [List.append_assoc]
    iframe Hcr
    iapply BigSepL.bigSepL_cons.2
    iframe Hn H

end loop

/-! ### The law -/

section law
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext] [lctx : GoLocalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [G : GooseGlobalGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The generation `L` at the statement's Go context `lctx` (`etcd_dist.atCtx`'s shape): so that the
program's instances over `lctx` (`go.Semantics`, the file extension's `FsCtx`) apply at it. -/
abbrev atC (L : GooseLocalGS GF) : GooseLocalGS GF := { L with goose_go_local_context := lctx }

/-- **The snapshot directory's crash law** (D6-T6; see the file header). For the old generation `L` and the
new `L'` of a crash (both at the statement's Go context, `atC`) whose crashed history is `V'` (nothing
logged) under the roots `R`, at the program's file-extension instances (`c`, `c'`: the one `FsCtx`, seen
from each generation): the old generation's invariant with its crash token (`snapDirKeep`), its `crashed`
and a later credit; the removal facts' weakening `Rm → Rm'` (a plain persistent wand: the body keeps one
for every index) and the image facts' `img → img'` (the body keeps them persistent; the member's
crash law passes `srvImageM_gen`, the image at the old generation's ghost state to the new one's: the
coordinator's option (a), 2026-11-25); T7's obligation that the crash kept the directory (`snapDirKept`: `sd` resolves to the
same directory `J` in the crashed tree, `lookupH R V' sd = some (.dir J)`, which Go provides by
`TouchDirAll`'s syncs of the parents of `member` and `snap`, F-N2); the old generation's view of the roots
and the file system's restart resources (`crashRest`, whose taken files `D` are not named at `J`'s
snapshot names); and the new generation's right on the directory (`snap.snapDirOwn`) and its fresh claim
on every index's name (`snapSlot`, nothing logged). Gives the new generation's invariant with its crash
token, at `img'` and `Rm'`, and the restart resources with the kept files `D'` taken. -/
abbrev snapDir_crash.law : Prop :=
  ∀ (L L' : GooseLocalGS GF) (c : FsCtx (hG := ⟨G, atC L⟩) GF) (c' : FsCtx (hG := ⟨G, atC L'⟩) GF)
    (Q : OsState → OsState → Prop) (tt : Bool) (V' : Hist)
    (D : List Ino) (R : Roots) (J : Ino) (sd : GoString) (γd : GName) (img img' : w64 → Data → IProp GF)
    (Rm Rm' : w64 → IProp GF),
    theFs (hG := ⟨G, atC L⟩) GF = some c → theFs (hG := ⟨G, atC L'⟩) GF = some c' →
    V'.2 = [] → lookupH R V' sd = some (.dir J) →
    (∀ x ∈ D, ∀ i, V'.now.entry J (snap.snapDBName i) ≠ some (.file x)) →
    ⊢ £ 1 -∗ snapDirKeep (hG := ⟨G, atC L⟩) sd γd img Rm -∗ crashed (hC := (atC L).goose_crashGS) -∗
      □ (∀ j, Rm j -∗ Rm' j) -∗ □ (∀ j Dt, img j Dt -∗ img' j Dt) -∗
      snapDirKept (hG := ⟨G, atC L⟩) R V' sd -∗
      (letI := FsCtx.S (hG := ⟨G, atC L⟩) c; letI := FsCtx.ok (hG := ⟨G, atC L⟩) c
       letI := FsCtx.has (hG := ⟨G, atC L⟩) c
       iprop(osSharedInv (L := atC L) R ∗
        crashRest Q (gooseOsGS (L := atC L)) (gooseOsGS (L := atC L')) D tt V')) -∗
      snap.snapDirOwn (hG := ⟨G, atC L'⟩) (snap.snapDBPath sd) -∗
      ([∗list] i ∈ snap.allW64, snapSlot (hG := ⟨G, atC L'⟩) sd J V' i) ={⊤}=∗
      ∃ D' : List Ino, snapDirKeep (hG := ⟨G, atC L'⟩) sd γd img' Rm' ∗
        (letI := FsCtx.S (hG := ⟨G, atC L⟩) c; letI := FsCtx.ok (hG := ⟨G, atC L⟩) c
         letI := FsCtx.has (hG := ⟨G, atC L⟩) c
         crashRest Q (gooseOsGS (L := atC L)) (gooseOsGS (L := atC L')) (D' ++ D) tt V')

/-- `snapSaved` is a ghost-map element of the global names: the same at every generation. -/
theorem snapSaved_gen (L L' : GooseLocalGS GF) (γd : GName) (i : w64) :
    snapSaved (hG := ⟨G, L⟩) γd i ⊢ snapSaved (hG := ⟨G, L'⟩) γd i := by
  unfold snapSaved; exact .rfl

theorem snapDir_crash_law_holds : snapDir_crash.law (GF := GF) := by
  classical
  intro L L' c c' Q tt V' D R J sd γd img img' Rm Rm' hfs hfs' hV hJ hD
  obtain ⟨S, ok, has, fa, fsa, ne⟩ := c
  obtain ⟨S', ok', has', fa', fsa', ne'⟩ := c'
  have hS : S' = S := has'.sem_eq.symm.trans has.sem_eq
  subst S'
  have hok : ok' = ok := Subsingleton.elim _ _
  have hhas : has' = has := Subsingleton.elim _ _
  subst ok' has'
  letI := S; letI := ok; letI := has
  -- the program's instances in every `onFs`
  have hfileO : ∀ (E : GMap w64 Unit) (i : w64) (Dt : Data),
      (iprop(snapFileAt (hG := ⟨G, atC L⟩) sd E i Dt ∗ □ img i Dt) : IProp GF) =
        fileOldF (atC L) sd img E i Dt := by
    intro E i Dt
    unfold snapFileAt fileOldF fileAtDur fileAtPend
    rw [onFs_some (hG := ⟨G, atC L⟩) hfs, onFs_some (hG := ⟨G, atC L⟩) hfs]
  have hfileN : ∀ (E : GMap w64 Unit) (i : w64) (Dt : Data),
      (iprop(snapFileAt (hG := ⟨G, atC L'⟩) sd E i Dt ∗ □ img i Dt) : IProp GF) =
        fileOldF (atC L') sd img E i Dt := by
    intro E i Dt
    unfold snapFileAt fileOldF fileAtDur fileAtPend
    rw [onFs_some (hG := ⟨G, atC L'⟩) hfs', onFs_some (hG := ⟨G, atC L'⟩) hfs']
  have hfreeO : ∀ (i : w64), fileFreeDur (hG := ⟨G, atC L⟩) (snap.snapDBPath sd i) =
      fileFreeDurF (hG := ⟨G, atC L⟩) (snap.snapDBPath sd i) := by
    intro i; unfold fileFreeDur; rw [onFs_some (hG := ⟨G, atC L⟩) hfs]
  have hfreeN : ∀ (i : w64), fileFreeDur (hG := ⟨G, atC L'⟩) (snap.snapDBPath sd i) =
      fileFreeDurF (hG := ⟨G, atC L'⟩) (snap.snapDBPath sd i) := by
    intro i; unfold fileFreeDur; rw [onFs_some (hG := ⟨G, atC L'⟩) hfs']
  have hslot : ∀ i, snapSlot (hG := ⟨G, atC L'⟩) sd J V' i = snapSlotF (hG := ⟨G, atC L'⟩) sd J V' i := by
    intro i; unfold snapSlot; rw [onFs_some (hG := ⟨G, atC L'⟩) hfs']
  have hkept : snapDirKept (hG := ⟨G, atC L⟩) R V' sd = snapDirKeptF (hG := ⟨G, atC L⟩) R V' sd := by
    unfold snapDirKept; rw [onFs_some (hG := ⟨G, atC L⟩) hfs]
  rw [hkept]
  simp only [hslot]
  iintro Hlc Hkeep #Hcrd #Hrm #Himg #Hk ⟨#Hsh, Hcr⟩ Hown Hslots
  -- the crashed tree's names are unique (a file is named once)
  imod crashRest_treeWf' Q (atC L) (atC L') D tt V' R ⊤ CoPset.subseteq_top $$ Hsh Hcr with ⟨%hwf, Hcr⟩
  -- the old invariant: its contents out, closed with the crash token
  unfold snapDirKeep
  icases Hkeep with ⟨%γk, #Hinv, Htok⟩
  iinv Hinv with Hi Hclose
  imod (lc_fupd_elim_later (P := snapDirInvK (hG := ⟨G, atC L⟩) sd γd γk img Rm)) $$ Hlc Hi with Hi
  iunfold snapDirInvK at Hi
  icases Hi with ⟨Hown0, Hb⟩
  icases Hb with (Hb | ⟨-, Ht⟩)
  rotate_left
  · iexfalso; iapply token_exclusive $$ Htok Ht
  imod Hclose $$ [Hown0 Htok] with -
  · inext
    iunfold snapDirInvK
    iframe Hown0
    iright
    iframe Hcrd Htok
  iunfold snapDirBody at Hb
  icases Hb with ⟨%M, %E, %F, Ha, %hMF, HM, HF, #HEs, #HRm⟩
  -- every index's old resources and new slot, in one list
  ihave HM := (BigSepM.bigSepM_mono_of_forall (Ψ := fun i Dt => fileOldF (atC L) sd img E i Dt)
    (fun {i Dt} => by rw [hfileO])) $$ HM
  ihave HF := (BigSepM.bigSepM_mono_of_forall (Ψ := fun i (_ : Unit) =>
    fileFreeDurF (hG := ⟨G, atC L⟩) (snap.snapDBPath sd i)) (fun {i _} => by rw [hfreeO])) $$ HF
  ihave HM := map_toList _ snap.allW64 M bootSnap.allW64_nodup (fun i _ => bootSnap.mem_allW64 i) $$ HM
  ihave HF := map_toList _ snap.allW64 F bootSnap.allW64_nodup (fun i _ => bootSnap.mem_allW64 i) $$ HF
  ihave Hold := BigSepL.bigSepL_sep_eqv_symm.1 $$ [HM HF]
  · iframe HM HF
  ihave Hall := BigSepL.bigSepL_sep_eqv_symm.1 $$ [Hold Hslots]
  · iframe Hold Hslots
  imod loop Q (atC L) (atC L') tt V' hV R J sd img E M F hMF hJ hwf.2.2.2.2 snap.allW64 D
    bootSnap.allW64_nodup (fun x hx i _ => hD x hx i) $$ Hk Hcr [Hall] with ⟨%D', Hcr, Hnew⟩
  · unfold oldAt; iexact Hall
  -- the new generation's maps
  unfold newAt
  icases BigSepL.bigSepL_sep_eqv.1 $$ Hnew with ⟨HM', HF'⟩
  icases list_toMap _ _ snap.allW64 bootSnap.allW64_nodup $$ HM' with ⟨%M', %hM', -, HM'⟩
  icases list_toMap _ _ snap.allW64 bootSnap.allW64_nodup $$ HF' with ⟨%F', %hF', -, HF'⟩
  have hM'i : ∀ i, M' !! i = keepM V' J E M i := fun i => hM' i (bootSnap.mem_allW64 i)
  have hF'i : ∀ i, F' !! i = keepF V' J E M F i := fun i => hF' i (bootSnap.mem_allW64 i)
  ihave HM' := (BigSepM.bigSepM_mono_of_forall (Ψ := fun i Dt =>
    iprop(snapFileAt (hG := ⟨G, atC L'⟩) sd E i Dt ∗ □ img i Dt))
    (fun {i Dt} => by rw [hfileN])) $$ HM'
  ihave HF' := (BigSepM.bigSepM_mono_of_forall (Ψ := fun i (_ : Unit) =>
    fileFreeDur (hG := ⟨G, atC L'⟩) (snap.snapDBPath sd i)) (fun {i _} => by rw [hfreeN])) $$ HF'
  -- the image facts weakened, `img → img'`
  ihave HM' := BigSepM.bigSepM_impl (Ψ := fun i Dt =>
    iprop(snapFileAt (hG := ⟨G, atC L'⟩) sd E i Dt ∗ □ img' i Dt)) $$ HM' []
  · iintro !> %i %Dt %_ ⟨Hf, #Hi⟩
    iframe Hf
    iintro !>
    iapply Himg $$ Hi
  -- the new invariant and its crash token
  imod token_alloc (GF := GF) with ⟨%γk', Htok'⟩
  imod (inv_alloc snapDirN ⊤ (snapDirInvK (hG := ⟨G, atC L'⟩) sd γd γk' img' Rm')) $$ [Hown Ha HM' HF']
    with #Hinv'
  · inext
    iunfold snapDirInvK
    iframe Hown
    ileft
    iunfold snapDirBody
    iexists M', E, F'
    iframe Ha HM' HF'
    isplitr
    · ipureintro
      intro i
      rw [hF'i, hM'i]
      unfold keepF keepM
      cases hMi : M !! i with
      | some Dt =>
        by_cases hk : keepP V' J E i
        · simp only [hk, if_true]
          constructor
          · intro h; exact absurd rfl h
          · rintro ⟨-, h⟩; cases h
        · simp only [hk, if_false]
          have hE : E !! i = none := by
            cases h : E !! i with
            | none => rfl
            | some _ => exact absurd (Or.inr (by rw [h]; simp)) hk
          simp [hE]
      | none =>
        simp only
        rw [hMF i, hMi]
        simp
    isplitr
    · iintro !> %i %hi
      iapply snapSaved_gen (atC L) (atC L')
      iapply HEs $$ %i %hi
    iintro !> %i %hi
    obtain ⟨hEi, hMi'⟩ := hi
    have hMi : M !! i = none := by
      rw [hM'i] at hMi'
      unfold keepM at hMi'
      cases h : M !! i with
      | none => rfl
      | some Dt =>
        rw [h] at hMi'
        have hk : keepP V' J E i := Or.inr hEi
        simp [hk] at hMi'
    iapply Hrm
    iapply HRm $$ %i %(And.intro hEi hMi)
  imodintro
  iexists D'
  iframe Hcr
  iexists γk'
  iframe Hinv' Htok'

end law

end snapCrash
end EtcdGrove
end Perennial
