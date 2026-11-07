/-
The crash interpretation of the Linux file extension (`ExtCrashInterp fsExt`): what the restarted
boot program gets after a machine crash (a process's restart is one, by the environment's
assumption on restarts). Untrusted.

* The new generation's ghost state is allocated from the state the crash left (`os_local_initG`,
  `CrashFiles.lean`): every file with its `OsMeta` and bytes from the state (`osFileStartG`; after a
  machine crash all of it on disk and clean, `metaOf_ofDisk`, `bytesOf_ofDisk`), and the tree's
  history, whole: a prefix of the old history replayed, nothing logged (`TreeCrashed`).
* The restart gets `crashRest Q old new [] false V'` (for the new history `V'`): the old
  generation's maps of bytes, files and changes in flight with what they hold, the old history's
  authority, the new generation's files and history, and the crash's facts (the crashed state, its
  coherence with the old maps, and the premise `Q`). A client takes from it, with what its
  invariant kept of the old generation:
  - a file (`crashRest_take_runs_keep`, with the bytes in runs; `crashRest_take_tok_keep`, with the
    token of a change in flight that holds its `OsMeta`): what the crash did to it
    (`FileCrashedR`: a size within the old bounds, every byte known clean kept and clean), whether
    the new tree names it (then it is there), and the crash's facts (`CrashSeenR`);
  - the tree (`crashRest_tree`): the new history, whole, and that it is a crash of the old one.
* `Q` is a premise on crashes (minibolt's P1: `fsSemWith Q`); `Q := fun _ _ => True` for the plain
  interpretation (`fs_crash_interp`).
-/
module

public import GooseLang.Ext.Fs.CrashFiles
public import Perennial.GooseLang.CrashAdequacy

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

/-! ## The new generation's ghost state, from any crash outcome -/

section init
variable {GF : BundledGFunctors}

/-- The bytes of the files `F`, each flagged clean if it is. -/
def bytesMapF (F : GMap Ino OsFile) : GMap (Ino × Nat) (w8 × Bool) :=
  ⟨fun k => (F !! k.1).bind (fun f => (bytesOf f)[k.2]?),
   ⟨F.toList.flatMap (fun pf => (List.range pf.2.size).map (fun b => (pf.1, b))),
    fun ⟨i, b⟩ h => by
      simp only [List.mem_flatMap]
      cases hf : F !! i with
      | none => simp [hf] at h
      | some f =>
        simp only [hf, Option.bind_some] at h
        refine ⟨⟨i, f⟩, (GMap.mem_toList _ _ _).2 hf, ?_⟩
        simp only [List.mem_map, List.mem_range, Prod.mk.injEq]
        refine ⟨b, ?_, by simp⟩
        rw [← bytesOf_length]
        exact (Option.isSome_iff_exists.1 h).elim fun _ h' => (List.getElem?_eq_some_iff.1 h').1⟩⟩

theorem bytesMapG_eq (st : OsState) : bytesMapG st = bytesMapF st.fs.files :=
  GMap.ext (fun _ => rfl)

/-- The start resources of a new generation's state `st` with the history `V`: every file and byte,
whole, the half of the cells' view that the invariant takes, and the history, whole. -/
def osStartG (hL : OsGS GF) (st : OsState) (V : Hist) : IProp GF :=
  iprop(([∗map] k ↦ x ∈ bytesMapG st, gElem hL hL.γb k (DFrac.own 1) x) ∗
    ([∗map] i ↦ m ∈ metaMapG st, gElem hL hL.γm i (DFrac.own 1) m) ∗
    gVar hL (1 : Qp).half ((∅ : GMap Loc (Option w8 × Bool)), 0) ∗
    gElem hL hL.γd () (DFrac.own 1) (st.fs.roots, V))

/-- **The new generation's ghost state**, from any state with no process state whose files and tree
are well formed and coherent with the history `V`. -/
theorem os_local_initG (hPre : OsGpreS GF) (st : OsState) (V : Hist)
    (hp : st.proc = ProcState.empty) (hwf : OsWf st) (htw : FsTreeWf st)
    (htc : TreeCoh st V ∅ ∅) :
    ⊢@{IProp GF} |==> ∃ hL : OsGS GF, osCtx hL st ∗ osStartG hL st V := by
  letI := hPre.osPreAllG
  have hcoh := osCohG hp hwf
  imod ghost_map_alloc (GF := GF) (bytesMapG st) with ⟨%γb, Hab, Hb⟩
  imod ghost_map_alloc (GF := GF) (metaMapG st) with ⟨%γm, Ham, Hm⟩
  imod ghost_map_alloc (GF := GF) (∅ : GMap w64 OsFd) with ⟨%γf, Haf, -⟩
  imod ghost_map_alloc (GF := GF) (∅ : GMap Nat TokInfo) with ⟨%γt, Hat, -⟩
  imod ghostVar_alloc (GF := GF) ((∅ : GMap Loc (Option w8 × Bool)), 0) with ⟨%γv, Hv⟩
  icases (ghostVar_split_half γv 1 _).1 $$ Hv with ⟨Hv1, Hv2⟩
  imod ghost_map_alloc (GF := GF) (histMap (st.fs.roots, V)) with ⟨%γd, Had, Hd⟩
  imod ghost_map_alloc (GF := GF) (∅ : GMap w64 (Ino × DirPh)) with ⟨%γdf, Hadf, -⟩
  imod ghost_map_alloc (GF := GF) (∅ : GMap Nat (Nat × Qp)) with ⟨%γc, Hac, -⟩
  imodintro
  iexists (⟨hPre.osPreAllG, γb, γm, γf, γt, γv, γd, γdf, γc⟩ : OsGS GF)
  isplitl [Hab Ham Haf Hat Hv1 Had Hadf Hac]
  · unfold osCtx osCtxF treeCtx tokRes rdRes gAuth gVar
    isplitl [Hab Ham Haf Hat Hv1]
    · iexists (bytesMapG st), (metaMapG st), ∅, ∅
      rw [cellView_of_maps_empty (by rw [hp]; rfl),
        show st.proc.inflight = ∅ by rw [hp]; rfl, GMap.map_size_empty]
      iframe Hab Ham Haf Hat Hv1
      isplitr
      · ipureintro; exact ⟨hwf, hcoh⟩
      · iapply BigSepM.bigSepM_empty.2; itrivial
    · iexists V, ∅, ∅
      iframe Had Hadf Hac
      isplitr
      · ipureintro; exact ⟨htw, htc⟩
      unfold callRes
      isplitl [] <;> iapply BigSepM.bigSepM_empty.2 <;> itrivial
  · unfold osStartG gElem gVar histMap
    ihave Hd := (show ([∗map] k ↦ v ∈ ({[() := (st.fs.roots, V)]} : GMap Unit (Roots × Hist)),
          ghostMapElem (GF := GF) γd k (DFrac.own 1) v) ⊢
        ghostMapElem γd () (DFrac.own 1) ((st.fs.roots, V) : Roots × Hist) from
      (BigSepM.bigSepM_singleton (M := GMap Unit)
        (Φ := fun (k : Unit) (v : Roots × Hist) =>
          ghostMapElem (GF := GF) γd k (DFrac.own 1) v)).1) $$ Hd
    iframe

variable (hL : OsGS GF)

/-- The start resources of the file `f` of inode `i`: its `OsMeta` and its bytes, whole. -/
def fileStartG (i : Ino) (f : OsFile) : IProp GF :=
  iprop(gElem hL hL.γm i (DFrac.own 1) (metaOf f) ∗ bytesG hL i 0 (DFrac.own 1) (bytesOf f))

theorem bigSepM_insertBytesG (i : Ino) :
    ∀ (off : Nat) (ys : List (w8 × Bool)) (m : GMap (Ino × Nat) (w8 × Bool)),
    (∀ k, k < ys.length → m !! (i, off + k) = none) →
    ([∗map] k ↦ x ∈ insertBytes i off ys m, gElem hL hL.γb k (DFrac.own 1) x) ⊢
      bytesG hL i off (DFrac.own 1) ys ∗ [∗map] k ↦ x ∈ m, gElem hL hL.γb k (DFrac.own 1) x
  | off, [], m, _ => by
    simp only [insertBytes]
    iintro H; iframe H; iapply (bytesG_nil hL i off _).2; iempintro
  | off, y :: ys, m, hfree => by
    simp only [insertBytes]
    refine (bigSepM_insertBytesG i (off + 1) ys _ (fun k hk => ?_)).trans ?_
    · rw [GMap.lookup_insert_ne _ _ (by simp; omega)]
      rw [show off + 1 + k = off + (k + 1) by omega]; exact hfree (k + 1) (by simp; omega)
    have hm : m !! (i, off) = none := by simpa using hfree 0 (by simp)
    have hins := (BigSepM.bigSepM_insert (Φ := fun k x => gElem hL hL.γb k (DFrac.own 1) x)
      (m := m) (i := (i, off)) (x := y) hm).1
    iintro ⟨H1, H2⟩
    icases hins $$ H2 with ⟨Hy, Hm⟩
    iframe Hm
    iapply (bytesG_cons hL i off _ y ys).2
    iframe

/-- The start resources, file by file. -/
theorem start_filesG : ∀ F : GMap Ino OsFile,
    ([∗map] k ↦ x ∈ bytesMapF F, gElem hL hL.γb k (DFrac.own 1) x) ∗
      ([∗map] i ↦ m ∈ GMap.fmap metaOf F, gElem hL hL.γm i (DFrac.own 1) m) ⊢
    [∗map] i ↦ f ∈ F, fileStartG hL i f := by
  refine GMap.map_ind ?_ ?_
  · have h1 : bytesMapF (∅ : GMap Ino OsFile) = ∅ :=
      GMap.ext (fun k => by simp [bytesMapF])
    have h2 : GMap.fmap metaOf (∅ : GMap Ino OsFile) = ∅ := GMap.ext (fun k => by simp)
    rw [h1, h2]
    iintro -; iapply BigSepM.bigSepM_empty.2; iempintro
  · intro i f F hi IH
    have hm : GMap.fmap metaOf (<[i := f]> F) = <[i := metaOf f]> (GMap.fmap metaOf F) :=
      GMap.ext (fun q => by
        by_cases hq : q = i
        · subst hq; simp [GMap.lookup_fmap]
        · simp [GMap.lookup_fmap, Ne.symm hq])
    have hmp : GMap.fmap metaOf F !! i = none := by simp [GMap.lookup_fmap, hi]
    have Hins := (BigSepM.bigSepM_insert (Φ := fun i f => fileStartG hL i f) (m := F) (x := f)
      hi).2
    refine BIBase.Entails.trans ?_ Hins
    rw [hm]
    have Hmi := (BigSepM.bigSepM_insert (Φ := fun i m => gElem hL hL.γm i (DFrac.own 1) m)
      (m := GMap.fmap metaOf F) (i := i) (x := metaOf f) (by exact hmp)).1
    refine BIBase.Entails.trans (sep_mono_right Hmi) ?_
    have hb : bytesMapF (<[i := f]> F) = insertBytes i 0 (bytesOf f) (bytesMapF F) :=
      GMap.ext (fun k => by
        obtain ⟨q, b⟩ := k
        rw [lookup_insertBytes]
        by_cases hq : q = i
        · subst hq
          simp only [bytesMapF, GMap.lookup_mk, GMap.lookup_insert,
            Option.bind_some, hi, Option.bind_none, _root_.true_and, Nat.zero_le, Nat.zero_add,
            Nat.sub_zero]
          by_cases hb : b < (bytesOf f).length
          · simp [hb]
          · simp [hb, List.getElem?_eq_none (show (bytesOf f).length ≤ b by omega)]
        · simp [bytesMapF, Ne.symm hq, hq])
    rw [hb]
    have Hb := bigSepM_insertBytesG hL i 0 (bytesOf f) (bytesMapF F)
      (fun k _ => by simp [bytesMapF, hi])
    iintro ⟨Hb', Hm, Hms⟩
    icases Hb $$ Hb' with ⟨Hb1, Hb2⟩
    isplitl [Hm Hb1]
    · unfold fileStartG; iframe
    iapply IH; iframe

/-- The start resources of a new generation, file by file, the half of the cells' view, and the
history. -/
theorem osStartG_files (st : OsState) (V : Hist) :
    osStartG hL st V ⊢ ([∗map] i ↦ f ∈ st.fs.files, fileStartG hL i f) ∗
      gVar hL (1 : Qp).half ((∅ : GMap Loc (Option w8 × Bool)), 0) ∗
      gElem hL hL.γd () (DFrac.own 1) (st.fs.roots, V) := by
  unfold osStartG metaMapG
  rw [bytesMapG_eq]
  iintro ⟨Hb, Hm, Hv, Hd⟩
  iframe Hv Hd
  iapply start_filesG hL st.fs.files; iframe

end init

/-! ## The restart's resources -/

/-- What the restarted boot program learns of the file of inode `i`, taken with the old
generation's `OsMeta` `m`, the bytes of the runs `rs` and the changes in flight `ts` (tokens it
holds): the new file `fo` is the one of `i` in the state `st'` the new generation starts from, which
a crash (`OsCrash`, and `Q`) made of the crashed state `st`; `st` is coherent with the old ghost
maps, in which `i`'s `OsMeta` is `m`, the runs' bytes are as `rs` says, and the changes `ts` are in
flight; every change in flight on `i` is one of `ts`, or takes a fraction of the `OsMeta` and none
of the runs' bytes. -/
def CrashSeenR (Q : OsState → OsState → Prop) (i : Ino) (m : OsMeta)
    (rs : List (Nat × DFrac × List (w8 × Bool))) (ts : List (Nat × TokInfo))
    (fo : Option OsFile) : Prop :=
  ∃ (st st' : OsState) (Γb : GMap (Ino × Nat) (w8 × Bool)) (Γm : GMap Ino OsMeta)
    (Γf : GMap w64 OsFd) (Γt : GMap Nat TokInfo),
    OsCoh st Γb Γm Γf Γt ∧ OsCrash st st' ∧ Q st st' ∧ st'.fs.files !! i = fo ∧
    Γm !! i = some m ∧
    (∀ r ∈ rs, ∀ k (hk : k < r.2.2.length), Γb !! (i, r.1 + k) = some r.2.2[k]) ∧
    (∀ x ∈ ts, Γt !! x.1 = some x.2) ∧
    (∀ t ti, Γt !! t = some ti → ti.c.ino = i → (t, ti) ∈ ts ∨
      (ti.q ≠ 1 ∧ ∀ r ∈ rs, ∀ k < r.2.2.length, r.1 + k ∉ affRange st ti.c)) ∧ OsWf st

section crash
variable {GF : BundledGFunctors}

/-- The new generation's file, if the crash kept it. -/
def fileStartO (hL : OsGS GF) (i : Ino) : Option OsFile → IProp GF
  | none => iprop(emp)
  | some f => fileStartG hL i f

/-- The new generation's history, until it is taken. -/
def treeLeft (hL : OsGS GF) (R : Roots) (V' : Hist) : Bool → IProp GF
  | true => iprop(emp)
  | false => gElem hL hL.γd () (DFrac.own 1) (R, V')

/-- **The restart's resources**, once the files `D` and (if `tt`) the tree are taken, the new
history being `V'`. -/
def crashRest (Q : OsState → OsState → Prop) (hL hL' : OsGS GF) (D : List Ino) (tt : Bool)
    (V' : Hist) : IProp GF :=
  iprop(∃ (Γb : GMap (Ino × Nat) (w8 × Bool)) (Γm : GMap Ino OsMeta) (F : GMap Ino OsFile)
      (st st' : OsState) (Γf : GMap w64 OsFd) (Γt Γt' : GMap Nat TokInfo) (V : Hist),
    ⌜(∀ i m, Γm !! i = some m → i ∉ D → FileCrashedG Γb i m (F !! i)) ∧
      (∀ i, i ∉ D → F !! i = st'.fs.files !! i) ∧
      OsCoh st Γb Γm Γf Γt ∧ OsCrash st st' ∧ Q st st' ∧
      (∀ t ti, Γt' !! t = some ti → Γt !! t = some ti) ∧
      (∀ t ti, Γt !! t = some ti → ti.c.ino ∉ D → Γt' !! t = some ti) ∧
      st'.fs.roots = st.fs.roots ∧ TreeCrashed V V' ∧
      (∀ i, Named V'.now i → (st'.fs.files !! i).isSome) ∧ OsWf st⌝ ∗
    gAuth hL hL.γb Γb ∗ gAuth hL hL.γm Γm ∗ ([∗map] i ↦ f ∈ F, fileStartG hL' i f) ∗
    gAuth hL hL.γt Γt' ∗ tokRes hL st Γt' ∗
    gAuth hL hL.γd (histMap (st.fs.roots, V)) ∗ treeLeft hL' st.fs.roots V' tt)

/-- The restart's resources, and the new generation's half of the cells' view (for
`osInv_alloc`). -/
def osCrashStart (Q : OsState → OsState → Prop) (hL hL' : OsGS GF) : IProp GF :=
  iprop(gVar hL' (1 : Qp).half ((∅ : GMap Loc (Option w8 × Bool)), 0) ∗
    ∃ V', crashRest Q hL hL' [] false V')

variable (hL : OsGS GF)

theorem bytesG_lookup_runs (i : Ino) (Γb : GMap (Ino × Nat) (w8 × Bool)) :
    ∀ rs : List (Nat × DFrac × List (w8 × Bool)),
    ⊢ gAuth hL hL.γb Γb -∗ ([∗list] r ∈ rs, bytesG hL i r.1 r.2.1 r.2.2) -∗
      ⌜∀ r ∈ rs, ∀ k (hk : k < r.2.2.length), Γb !! (i, r.1 + k) = some r.2.2[k]⌝
  | [] => by
    iintro _ _
    ipureintro
    intro r hr; cases hr
  | r :: rs => by
    iintro HA Hrs
    icases BigSepL.bigSepL_cons.1 $$ Hrs with ⟨Hr, Hrs⟩
    icases bytesG_lookup hL i r.1 r.2.1 r.2.2 Γb $$ HA Hr with %h1
    icases bytesG_lookup_runs i Γb rs $$ HA Hrs with %h2
    ipureintro
    intro r' hr'
    rcases List.mem_cons.1 hr' with rfl | h
    · exact h1
    · exact h2 r' h

/-- The runs' bytes of `i` are under no change in flight that `tokRes` holds: each holds the bytes
it takes whole. -/
theorem tokRes_runs_disj {st : OsState} {Γb Γm Γf} {Γt Γt' : GMap Nat TokInfo}
    (hcoh : OsCoh st Γb Γm Γf Γt) (hsub : ∀ t ti, Γt' !! t = some ti → Γt !! t = some ti)
    (i : Ino) (rs : List (Nat × DFrac × List (w8 × Bool))) :
    ⊢ tokRes hL st Γt' -∗ ([∗list] r ∈ rs, bytesG hL i r.1 r.2.1 r.2.2) -∗
      ⌜∀ t ti, Γt' !! t = some ti → ti.c.ino = i → ∀ r ∈ rs, ∀ k < r.2.2.length,
        r.1 + k ∉ affRange st ti.c⌝ := by
  iintro Htok Hbs
  by_cases hφ : ∀ t ti, Γt' !! t = some ti → ti.c.ino = i → ∀ r ∈ rs, ∀ k < r.2.2.length,
      r.1 + k ∉ affRange st ti.c
  · ipureintro; exact hφ
  simp only [Classical.not_forall, Classical.not_not] at hφ
  obtain ⟨t, ti, hti, hp, r, hr, k, hk, hin⟩ := hφ
  obtain ⟨f, -, hsv⟩ := hcoh.tok_saved t ti (hsub t ti hti)
  have hlen : ti.saved.length = affHi st ti.c - affLo st ti.c := by
    rw [hsv, List.length_map]; simp [affRange]
  simp only [affRange, List.mem_range'_1] at hin
  obtain ⟨n, hn⟩ := List.mem_iff_getElem?.1 hr
  unfold tokRes
  icases BigSepM.bigSepM_lookup (Φ := fun (_t : Nat) (ti : TokInfo) =>
      iprop(gElem hL hL.γm ti.c.ino (DFrac.own ti.q) ti.om ∗
        bytesG hL ti.c.ino (affLo st ti.c) (DFrac.own 1) (ti.saved.map (·, false)))) hti
    $$ Htok with ⟨-, Hb⟩
  icases BigSepL.bigSepL_lookup (Φ := fun _ (r : Nat × DFrac × List (w8 × Bool)) =>
      bytesG hL i r.1 r.2.1 r.2.2) hn $$ Hbs with Hr
  unfold bytesG
  have hj : r.1 + k - affLo st ti.c < (ti.saved.map (·, false)).length := by
    rw [List.length_map, hlen]; omega
  icases BigSepL.bigSepL_lookup (Φ := fun k (x : w8 × Bool) =>
      gElem hL hL.γb (ti.c.ino, affLo st ti.c + k) (DFrac.own 1) x)
    (List.getElem?_eq_getElem hj) $$ Hb with Hb1
  icases BigSepL.bigSepL_lookup (Φ := fun k (x : w8 × Bool) => gElem hL hL.γb (i, r.1 + k) r.2.1 x)
    (List.getElem?_eq_getElem hk) $$ Hr with Hr1
  rw [hp, show affLo st ti.c + (r.1 + k - affLo st ti.c) = r.1 + k by omega]
  icases gElem_valid_2 hL _ _ _ _ _ _ $$ Hb1 Hr1 with %Hv
  exact absurd (DFrac.valid_own_op Hv.1) (by simp)

theorem crashRest_files_delete {Γb : GMap (Ino × Nat) (w8 × Bool)} {Γm : GMap Ino OsMeta}
    {F : GMap Ino OsFile} {st' : OsState} {D : List Ino} {i : Ino}
    (hrel : ∀ q m, Γm !! q = some m → q ∉ D → FileCrashedG Γb q m (F !! q))
    (hF : ∀ q, q ∉ D → F !! q = st'.fs.files !! q) :
    (∀ q m, Γm !! q = some m → q ∉ i :: D → FileCrashedG Γb q m (GMap.delete i F !! q)) ∧
    (∀ q, q ∉ i :: D → GMap.delete i F !! q = st'.fs.files !! q) := by
  refine ⟨fun q m hq hqD => ?_, fun q hqD => ?_⟩
  · have hqp : q ≠ i := fun h => hqD (h ▸ List.mem_cons_self)
    rw [GMap.lookup_delete_ne _ (Ne.symm hqp)]
    exact hrel q m hq (fun h => hqD (List.mem_cons_of_mem _ h))
  · have hqp : q ≠ i := fun h => hqD (h ▸ List.mem_cons_self)
    rw [GMap.lookup_delete_ne _ (Ne.symm hqp)]
    exact hF q (fun h => hqD (List.mem_cons_of_mem _ h))

/-- Takes the new file `i` from the files not yet taken. -/
theorem files_take (F : GMap Ino OsFile) (i : Ino) :
    ([∗map] q ↦ f ∈ F, fileStartG hL q f) ⊢
      fileStartO hL i (F !! i) ∗ [∗map] q ↦ f ∈ GMap.delete i F, fileStartG hL q f := by
  cases hF : F !! i with
  | none =>
    have : GMap.delete i F = F := GMap.ext (fun q => by
      by_cases hq : q = i
      · subst hq; rw [GMap.lookup_delete, hF]
      · rw [GMap.lookup_delete_ne _ (Ne.symm hq)])
    rw [this]; iintro H; iframe H; unfold fileStartO; iempintro
  | some f =>
    iintro H
    icases (BigSepM.bigSepM_delete (Φ := fun q f => fileStartG hL q f) hF).1 $$ H with ⟨Hf, H⟩
    iframe H; unfold fileStartO; iexact Hf

/-- **Taking a file after a crash**, with its bytes in runs, giving back the old generation's
resources it looks at (so that an invariant that held them can be closed again). -/
theorem crashRest_take_runs_keep (Q : OsState → OsState → Prop) (hL' : OsGS GF) (D : List Ino)
    (tt : Bool) (V' : Hist) (i : Ino) (hi : i ∉ D) (dq : DFrac) (m : OsMeta)
    (rs : List (Nat × DFrac × List (w8 × Bool))) :
    ⊢ crashRest Q hL hL' D tt V' -∗ gElem hL hL.γm i dq m -∗
      ([∗list] r ∈ rs, bytesG hL i r.1 r.2.1 r.2.2) -∗
      ∃ fo, ⌜FileCrashedR m rs fo ∧ (Named V'.now i → fo.isSome) ∧ CrashSeenR Q i m rs [] fo⌝ ∗
        fileStartO hL' i fo ∗ crashRest Q hL hL' (i :: D) tt V' ∗
        gElem hL hL.γm i dq m ∗ ([∗list] r ∈ rs, bytesG hL i r.1 r.2.1 r.2.2) := by
  unfold crashRest
  iintro ⟨%Γb, %Γm, %F, %st, %st', %Γf, %Γt, %Γt', %V, %hrel, Hab, Ham, Hfs, HAt, Htok, HAd, Ht⟩
    Hm Hbs
  obtain ⟨hrel, hF, hcoh, hcr, hQ, hsub, hall, hroots, htc, hnamed, hwfs⟩ := hrel
  icases gAuth_lookup hL _ _ _ _ _ $$ Ham Hm with %hmo
  icases bytesG_lookup_runs hL i Γb rs $$ Hab Hbs with %hxs
  icases tokRes_meta_frac _ $$ Htok Hm with %hq
  icases tokRes_runs_disj hL hcoh hsub i rs $$ Htok Hbs with %hd
  icases files_take hL' F i $$ Hfs with ⟨Hf, Hfs⟩
  have hFi := hF i hi
  iexists F !! i
  iframe Hf Hm Hbs
  isplitr
  · ipureintro
    refine ⟨fileCrashedR_of_g (hrel i m hmo hi) hxs, fun hn => by rw [hFi]; exact hnamed i hn,
      st, st', Γb, Γm, Γf, Γt, hcoh, hcr, hQ, hFi.symm, hmo, hxs, (fun _ h => nomatch h),
      fun t ti ht hp' => Or.inr ?_, hwfs⟩
    have ht' := hall t ti ht (hp' ▸ hi)
    exact ⟨hq t ti ht' hp', hd t ti ht' hp'⟩
  obtain ⟨h1, h2⟩ := crashRest_files_delete (i := i) hrel hF
  iexists Γb, Γm, GMap.delete i F, st, st', Γf, Γt, Γt', V
  iframe Hab Ham Hfs HAt Htok HAd Ht
  ipureintro
  exact ⟨h1, h2, hcoh, hcr, hQ, hsub,
    fun t ti h hD => hall t ti h (fun h' => hD (List.mem_cons_of_mem _ h')), hroots, htc, hnamed, hwfs⟩

/-- Taking the file a change in flight is on, with the fragment of `OsMeta` the change holds,
giving back the token. -/
theorem crashRest_take_tok_keep (Q : OsState → OsState → Prop) (hL' : OsGS GF) (D : List Ino)
    (tt : Bool) (V' : Hist) (t : Nat) (ti : TokInfo) (hi : ti.c.ino ∉ D)
    (rs : List (Nat × DFrac × List (w8 × Bool))) :
    ⊢ crashRest Q hL hL' D tt V' -∗ gElem hL hL.γt t (DFrac.own 1) ti -∗
      ([∗list] r ∈ rs, bytesG hL ti.c.ino r.1 r.2.1 r.2.2) -∗
      ∃ fo, ⌜FileCrashedR ti.om rs fo ∧ (Named V'.now ti.c.ino → fo.isSome) ∧
          CrashSeenR Q ti.c.ino ti.om rs [(t, ti)] fo⌝ ∗
        fileStartO hL' ti.c.ino fo ∗ crashRest Q hL hL' (ti.c.ino :: D) tt V' ∗
        gElem hL hL.γt t (DFrac.own 1) ti ∗
        ([∗list] r ∈ rs, bytesG hL ti.c.ino r.1 r.2.1 r.2.2) := by
  iintro Hr Ht Hbs
  unfold crashRest
  icases Hr with ⟨%Γb, %Γm, %F, %st, %st', %Γf, %Γt, %Γt', %V, %hrel, Hab, Ham, Hfs, HAt, Htok,
    HAd, Htl⟩
  obtain ⟨hrel, hF, hcoh, hcr, hQ, hsub, hall, hroots, htc, hnamed, hwfs⟩ := hrel
  icases gAuth_lookup hL _ _ _ _ _ $$ HAt Ht with %hti
  unfold tokRes
  icases (BigSepM.bigSepM_delete (Φ := fun _ (ti : TokInfo) => iprop(
      gElem hL hL.γm ti.c.ino (DFrac.own ti.q) ti.om ∗
      bytesG hL ti.c.ino (affLo st ti.c) (DFrac.own 1) (ti.saved.map (·, false)))) hti).1
    $$ Htok with ⟨⟨Hm, Hb⟩, Htok⟩
  icases gAuth_lookup hL _ _ _ _ _ $$ Ham Hm with %hmo
  icases bytesG_lookup_runs hL ti.c.ino Γb rs $$ Hab Hbs with %hxs
  have hsub' : ∀ t' ti', (GMap.delete t Γt') !! t' = some ti' → Γt !! t' = some ti' := by
    intro t' ti' h
    by_cases he : t' = t
    · subst he; simp at h
    · rw [GMap.lookup_delete_ne _ (Ne.symm he)] at h; exact hsub _ _ h
  ihave Htok : tokRes hL st (GMap.delete t Γt') $$ [Htok]
  · unfold tokRes; iexact Htok
  icases tokRes_meta_frac _ $$ Htok Hm with %hq
  icases tokRes_runs_disj hL hcoh hsub' ti.c.ino rs $$ Htok Hbs with %hd
  unfold tokRes
  icases files_take hL' F ti.c.ino $$ Hfs with ⟨Hf, Hfs⟩
  have hFi := hF ti.c.ino hi
  iexists F !! ti.c.ino
  iframe Hf Ht Hbs
  isplitr
  · ipureintro
    refine ⟨fileCrashedR_of_g (hrel _ _ hmo hi) hxs, fun hn => by rw [hFi]; exact hnamed _ hn,
      st, st', Γb, Γm, Γf, Γt, hcoh, hcr, hQ, hFi.symm, hmo, hxs, ?_, ?_, hwfs⟩
    · intro x hx
      simp only [List.mem_singleton] at hx
      subst hx
      exact hsub t ti hti
    · intro t' ti' ht' hp'
      by_cases he : t' = t
      · subst he
        have := hsub t' ti hti; rw [ht'] at this; cases this
        exact Or.inl List.mem_cons_self
      · have ht'' : (GMap.delete t Γt') !! t' = some ti' := by
          rw [GMap.lookup_delete_ne _ (Ne.symm he)]; exact hall t' ti' ht' (hp' ▸ hi)
        exact Or.inr ⟨hq t' ti' ht'' hp', hd t' ti' ht'' hp'⟩
  obtain ⟨h1, h2⟩ := crashRest_files_delete (i := ti.c.ino) hrel hF
  iexists Γb, Γm, GMap.delete ti.c.ino F, st, st', Γf, Γt, Γt', V
  iframe Hab Ham Hfs HAt HAd Htl
  isplitr
  · ipureintro
    exact ⟨h1, h2, hcoh, hcr, hQ, hsub,
      fun t' ti' h hD => hall t' ti' h (fun h' => hD (List.mem_cons_of_mem _ h')), hroots, htc,
      hnamed, hwfs⟩
  iapply (BigSepM.bigSepM_delete (Φ := fun _ (ti : TokInfo) => iprop(
      gElem hL hL.γm ti.c.ino (DFrac.own ti.q) ti.om ∗
      bytesG hL ti.c.ino (affLo st ti.c) (DFrac.own 1) (ti.saved.map (·, false)))) hti).2
  iframe

/-- **The tree after a crash**: from (a fraction of) the old generation's history `W`, the new
generation's, whole, a crash of `W` (`TreeCrashed`), on the same roots. The old fraction is given
back. -/
theorem crashRest_tree (Q : OsState → OsState → Prop) (hL' : OsGS GF) (D : List Ino) (V' : Hist)
    (dq : DFrac) (R : Roots) (W : Hist) :
    ⊢ crashRest Q hL hL' D false V' -∗ gElem hL hL.γd () dq (R, W) -∗
      ⌜TreeCrashed W V'⌝ ∗ gElem hL' hL'.γd () (DFrac.own 1) (R, V') ∗
        crashRest Q hL hL' D true V' ∗ gElem hL hL.γd () dq (R, W) := by
  unfold crashRest
  iintro ⟨%Γb, %Γm, %F, %st, %st', %Γf, %Γt, %Γt', %V, %hrel, Hab, Ham, Hfs, HAt, Htok, HAd, Htl⟩
    Hd
  icases gAuth_lookup hL _ _ _ _ _ $$ HAd Hd with %hh
  simp only [histMap, GMap.lookup_singleton_eq, Option.some.injEq, Prod.mk.injEq] at hh
  obtain ⟨rfl, rfl⟩ := hh
  unfold treeLeft
  iframe Htl Hd
  isplitr
  · ipureintro; exact hrel.2.2.2.2.2.2.2.2.1
  iexists Γb, Γm, F, st, st', Γf, Γt, Γt', V
  iframe
  ipureintro; exact hrel

/-- **The crash of the extension's ghost state**: the new generation's ghost state from the state
the crash left, and the restart's resources. -/
theorem os_local_crash (Q : OsState → OsState → Prop) (hPre : OsGpreS GF) (st st' : OsState)
    (hc : OsCrash st st') (hQ : Q st st') :
    ⊢@{IProp GF} osCtx hL st ==∗ ∃ hL' : OsGS GF, osCtx hL' st' ∗ osCrashStart Q hL hL' := by
  unfold osCtx osCtxF treeCtx
  iintro ⟨⟨%Γb, %Γm, %Γf, %Γt, %hwc, Hab, Ham, -, HAt, Htok, -⟩,
    ⟨%V, %Γdf, %Γc, %htw, HAd, -, -, -, -⟩⟩
  obtain ⟨hp, hroots, hwf', htw', V', htc', hcr, hnamed, hrel⟩ :=
    osCrash_rel hwc.1 hwc.2 htw.1 htw.2 hc
  imod os_local_initG hPre st' V' hp hwf' htw' htc' with ⟨%hL', Hctx, Hst⟩
  unfold osCtx osCtxF treeCtx
  icases osStartG_files hL' st' V' $$ Hst with ⟨Hfs, Hv, Hd⟩
  imodintro
  iexists hL'
  iframe Hctx
  unfold osCrashStart crashRest treeLeft
  iframe Hv
  iexists V', Γb, Γm, st'.fs.files, st, st', Γf, Γt, Γt, V
  rw [hroots]
  iframe Hab Ham Hfs HAt Htok HAd Hd
  ipureintro
  exact ⟨fun i m hm _ => hrel i m hm, fun _ _ => rfl, hwc.2, hc, hQ, fun _ _ h => h,
    fun _ _ h _ => h, rfl, hcr, hnamed, hwc.1⟩

/-- The crash interpretation of the Linux file extension. -/
instance fs_crash_interp : ExtCrashInterp fsExt where
  crashStart hL hL' := osCrashStart (fun _ _ => True) hL hL'
  local_crash _ hPre hL st st' hc := os_local_crash hL (fun _ _ => True) hPre st st' hc trivial

/-- The Linux file extension's semantics with crashes restricted by the premise `Q`. -/
@[instance_reducible] def fsSemWith (Q : OsState → OsState → Prop) : ExtSemantics fsExt where
  step := FsStep
  crash st st' := OsCrash st st' ∧ Q st st'

/-- The crash interpretation under the premise `Q`. -/
@[instance_reducible] def fs_crash_interpQ (Q : OsState → OsState → Prop) :
    @ExtCrashInterp fsExt (fsSemWith Q) fs_interp :=
  @ExtCrashInterp.mk fsExt (fsSemWith Q) fs_interp (fun hL hL' => osCrashStart Q hL hL')
    (fun _ hPre hL st st' (hc : OsCrash st st' ∧ Q st st') =>
      os_local_crash hL Q hPre st st' hc.1 hc.2)

end crash

/-! ## In a generation's terms -/

section gen
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF]

/-- The file `f` of inode `i` as the generation `L` starts with it (from a crash): its `OsMeta`
and its bytes, whole, as the state the crash left has them. -/
def osFileStartG [L : GooseLocalGS GF] (i : Ino) (f : OsFile) : IProp GF :=
  iprop(osMeta (L := L) i (DFrac.own 1) (metaOf f) ∗ osBytes (L := L) i 0 (DFrac.own 1) (bytesOf f))

/-- The file of inode `i`, if the crash kept it. -/
def osFileStartO [L : GooseLocalGS GF] (i : Ino) : Option OsFile → IProp GF
  | none => iprop(emp)
  | some f => osFileStartG (L := L) i f

/-- The file `f` of inode `i` as the first generation starts with it: on disk, all of it clean. -/
def osFileStart [L : GooseLocalGS GF] (i : Ino) (f : OsFile) : IProp GF :=
  iprop(osMeta (L := L) i (DFrac.own 1) (initMeta f) ∗
    osBytes (L := L) i 0 (DFrac.own 1) (f.contents.map (·, true)))

/-- After a machine crash a file is on disk: its start is the first generation's. -/
theorem osFileStartG_ofDisk [L : GooseLocalGS GF] (i : Ino) (vs : Nat → SecBytes) (sz : Nat) :
    osFileStartG (L := L) i (OsFile.ofDisk vs sz) ⊣⊢ osFileStart (L := L) i (OsFile.ofDisk vs sz) := by
  unfold osFileStartG osFileStart
  rw [metaOf_ofDisk, bytesOf_ofDisk]
  exact .rfl

theorem fileStartO_eq [L : GooseLocalGS GF] (i : Ino) (fo : Option OsFile) :
    fileStartO (gooseOsGS (L := L)) i fo ⊣⊢ osFileStartO (L := L) i fo := by
  cases fo <;> exact .rfl

/-- `crashRest_take_runs_keep` from the old generation `L` to the new one `L'`. -/
theorem osCrash_take_runs_keep (Q : OsState → OsState → Prop) (L L' : GooseLocalGS GF)
    (D : List Ino) (tt : Bool) (V' : Hist) (i : Ino) (hi : i ∉ D) (dq : DFrac) (m : OsMeta)
    (rs : List (Nat × DFrac × List (w8 × Bool))) :
    ⊢ crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D tt V' -∗ osMeta (L := L) i dq m -∗
      ([∗list] r ∈ rs, osBytes (L := L) i r.1 r.2.1 r.2.2) -∗
      ∃ fo, ⌜FileCrashedR m rs fo ∧ (Named V'.now i → fo.isSome) ∧ CrashSeenR Q i m rs [] fo⌝ ∗
        osFileStartO (L := L') i fo ∗
        crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) (i :: D) tt V' ∗
        osMeta (L := L) i dq m ∗ ([∗list] r ∈ rs, osBytes (L := L) i r.1 r.2.1 r.2.2) := by
  unfold osMeta osBytes
  iintro Hr Hm Hb
  icases crashRest_take_runs_keep _ Q _ D tt V' i hi dq m rs $$ Hr Hm Hb
    with ⟨%fo, %h, Hf, Hr, Hm, Hb⟩
  iexists fo
  iframe Hr Hm Hb
  isplitr
  · ipureintro; exact h
  iapply (fileStartO_eq (L := L') i fo).1 $$ Hf

/-- `crashRest_take_tok_keep` from the old generation `L` to the new one `L'`. -/
theorem osCrash_take_tok_keep (Q : OsState → OsState → Prop) (L L' : GooseLocalGS GF)
    (D : List Ino) (tt : Bool) (V' : Hist) (t : Nat) (ti : TokInfo) (hi : ti.c.ino ∉ D)
    (rs : List (Nat × DFrac × List (w8 × Bool))) :
    ⊢ crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D tt V' -∗ osTok (L := L) t ti -∗
      ([∗list] r ∈ rs, osBytes (L := L) ti.c.ino r.1 r.2.1 r.2.2) -∗
      ∃ fo, ⌜FileCrashedR ti.om rs fo ∧ (Named V'.now ti.c.ino → fo.isSome) ∧
          CrashSeenR Q ti.c.ino ti.om rs [(t, ti)] fo⌝ ∗
        osFileStartO (L := L') ti.c.ino fo ∗
        crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) (ti.c.ino :: D) tt V' ∗
        osTok (L := L) t ti ∗ ([∗list] r ∈ rs, osBytes (L := L) ti.c.ino r.1 r.2.1 r.2.2) := by
  unfold osTok osBytes
  iintro Hr Ht Hb
  icases crashRest_take_tok_keep _ Q _ D tt V' t ti hi rs $$ Hr Ht Hb
    with ⟨%fo, %h, Hf, Hr, Ht, Hb⟩
  iexists fo
  iframe Hr Ht Hb
  isplitr
  · ipureintro; exact h
  iapply (fileStartO_eq (L := L') _ fo).1 $$ Hf

/-- **The tree after a crash**, from the old generation `L` to the new one `L'`: from (a fraction
of) the old history `W`, the new history, whole, a crash of `W`. -/
theorem osTreeCrash_take (Q : OsState → OsState → Prop) (L L' : GooseLocalGS GF) (D : List Ino)
    (V' : Hist) (dq : DFrac) (R : Roots) (W : Hist) :
    ⊢ crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D false V' -∗
      osTree (L := L) dq R W -∗
      ⌜TreeCrashed W V'⌝ ∗ osTree (L := L') (DFrac.own 1) R V' ∗
        crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D true V' ∗
        osTree (L := L) dq R W := by
  unfold osTree
  iintro Hr Hd
  iapply crashRest_tree _ Q _ D V' dq R W $$ Hr Hd

end gen

end Fs
end Perennial

end
