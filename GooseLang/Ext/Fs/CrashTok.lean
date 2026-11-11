/-
The crash interpretation of the Linux file extension (`ExtCrashInterp fsExt`): what the restarted
boot program gets after a machine crash (a process's restart is one, by the environment's
assumption on restarts). Untrusted.

* The state a crash leaves is one a program may start in (`osCrash_rel`: `FsInit`), so the new
  generation's ghost state is allocated as the first generation's (`os_local_init`): every file
  with its `OsMeta` and bytes as on disk (`fileStart`: `initMeta`, each byte durable), and the
  tree's history, whole: a prefix of the old history replayed, nothing logged (`TreeCrashed`).
* The restart gets `crashRest Q old new [] false V'` (for the new history `V'`): the old
  generation's maps of bytes, files and changes in flight with what they hold, the old history's
  authority, the new generation's files and history, and the crash's facts (the crashed state, its
  coherence with the old maps, and the premise `Q`). A client takes from it, with what its
  invariant kept of the old generation:
  - a file (`crashRest_take_runs_keep`, with a fraction of its `OsMeta` and its bytes in runs;
    `crashRest_take_tok_keep`, with the token of the change in flight on it, which holds its
    `OsMeta` and the bytes it announced): what the crash did to it (`FileCrashedR`: on disk, a
    size within the old bounds, each byte of the runs one of its crash candidates), whether the new
    tree names it (then it is there), and the crash's facts (`CrashSeenR`);
  - the tree (`crashRest_tree`): the new history, whole, and that it is a crash of the old one.
* `Q` is a premise on crashes (`fsSemWith Q`); `Q := fun _ _ => True` for the plain interpretation
  (`fs_crash_interp`).
-/
module

public import GooseLang.Ext.Fs.CrashFiles
public import Perennial.GooseLang.CrashAdequacy

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

/-! ## A file's start resources -/

/-- The bytes of a file, each as the state has it. -/
def fileBytes (f : OsFile) : List ByteG := (List.range f.size).map (fun b => (f.cache b, f.cand b))

theorem fileBytes_ofDisk (img : Nat → w8) (sz : Nat) :
    fileBytes (OsFile.ofDisk img sz) = (OsFile.ofDisk img sz).contents.map durB := by
  simp only [fileBytes, OsFile.contents, List.map_map]
  apply List.map_congr_left
  intro b hb
  simp only [Function.comp]
  have : b < sz := by simpa [OsFile.ofDisk] using hb
  rw [ofDisk_cand_lt img sz b this]

section init
variable {GF : BundledGFunctors} (hL : OsGS GF)

/-- The start resources of the file `f` of inode `i`: its `OsMeta` and its bytes, whole. -/
def fileStartG (i : Ino) (f : OsFile) : IProp GF :=
  iprop(gElem hL hL.γm i (DFrac.own 1) (initMeta f) ∗ bytesG hL i 0 (DFrac.own 1) (fileBytes f))

/-- The start resources of the file `f` of inode `i`, on disk: its `OsMeta` and its bytes, whole,
each durable. -/
def fileStart (i : Ino) (f : OsFile) : IProp GF :=
  iprop(gElem hL hL.γm i (DFrac.own 1) (initMeta f) ∗
    bytesG hL i 0 (DFrac.own 1) (f.contents.map durB))

theorem bigSepM_insertBytesG (i : Ino) :
    ∀ (off : Nat) (ys : List ByteG) (m : GMap (Ino × Nat) ByteG),
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
      ([∗map] i ↦ m ∈ GMap.fmap initMeta F, gElem hL hL.γm i (DFrac.own 1) m) ⊢
    [∗map] i ↦ f ∈ F, fileStartG hL i f := by
  refine GMap.map_ind ?_ ?_
  · have h1 : bytesMapF (∅ : GMap Ino OsFile) = ∅ :=
      GMap.ext (fun k => by simp [bytesMapF])
    have h2 : GMap.fmap initMeta (∅ : GMap Ino OsFile) = ∅ := GMap.ext (fun k => by simp)
    rw [h1, h2]
    iintro -; iapply BigSepM.bigSepM_empty.2; iempintro
  · intro i f F hi IH
    have hm : GMap.fmap initMeta (<[i := f]> F) = <[i := initMeta f]> (GMap.fmap initMeta F) :=
      GMap.ext (fun q => by
        by_cases hq : q = i
        · subst hq; simp [GMap.lookup_fmap]
        · simp [GMap.lookup_fmap, Ne.symm hq])
    have hmp : GMap.fmap initMeta F !! i = none := by simp [GMap.lookup_fmap, hi]
    have Hins := (BigSepM.bigSepM_insert (Φ := fun i f => fileStartG hL i f) (m := F) (x := f)
      hi).2
    refine BIBase.Entails.trans ?_ Hins
    rw [hm]
    have Hmi := (BigSepM.bigSepM_insert (Φ := fun i m => gElem hL hL.γm i (DFrac.own 1) m)
      (m := GMap.fmap initMeta F) (i := i) (x := initMeta f) (by exact hmp)).1
    refine BIBase.Entails.trans (sep_mono_right Hmi) ?_
    have hb : bytesMapF (<[i := f]> F) = insertBytes i 0 (fileBytes f) (bytesMapF F) :=
      GMap.ext (fun k => by
        obtain ⟨q, b⟩ := k
        rw [lookup_insertBytes]
        by_cases hq : q = i
        · subst hq
          simp only [bytesMapF_lookup, GMap.lookup_insert, Option.bind_some, hi, Option.bind_none,
            _root_.true_and, Nat.zero_le, Nat.zero_add, Nat.sub_zero]
          by_cases hb : b < f.size
          · simp [hb, fileBytes]
          · simp [hb, fileBytes]
        · simp [bytesMapF_lookup, Ne.symm hq, hq])
    rw [hb]
    have Hb := bigSepM_insertBytesG hL i 0 (fileBytes f) (bytesMapF F)
      (fun k _ => by simp [bytesMapF_lookup, hi])
    iintro ⟨Hb', Hm, Hms⟩
    icases Hb $$ Hb' with ⟨Hb1, Hb2⟩
    isplitl [Hm Hb1]
    · unfold fileStartG; iframe
    iapply IH; iframe

/-- The start resources of the files of a state a program may start in, file by file, on disk. -/
theorem start_files {F : GMap Ino OsFile}
    (hdisk : ∀ i f, F !! i = some f → ∃ img sz, f = OsFile.ofDisk img sz) :
    ([∗map] k ↦ x ∈ bytesMapF F, gElem hL hL.γb k (DFrac.own 1) x) ∗
      ([∗map] i ↦ m ∈ GMap.fmap initMeta F, gElem hL hL.γm i (DFrac.own 1) m) ⊢
    [∗map] i ↦ f ∈ F, fileStart hL i f := by
  refine (start_filesG hL F).trans (BigSepM.bigSepM_mono (fun {i f} hf => ?_))
  obtain ⟨img, sz, rfl⟩ := hdisk i f hf
  unfold fileStartG fileStart
  rw [fileBytes_ofDisk]

end init

/-! ## The restart's resources -/

section crash
variable {GF : BundledGFunctors}

/-- The new generation's file, if the crash kept it. -/
def fileStartO (hL : OsGS GF) (i : Ino) : Option OsFile → IProp GF
  | none => iprop(emp)
  | some f => fileStart hL i f

/-- The new generation's history, until it is taken. -/
def treeLeft (hL : OsGS GF) (R : Roots) (V' : Hist) : Bool → IProp GF
  | true => iprop(emp)
  | false => gElem hL hL.γd () (DFrac.own 1) (R, V')

/-- **The restart's resources**, once the files `D` and (if `tt`) the tree are taken, the new
history being `V'`: the crashed state `st`, coherent with the old generation's ghost maps, which a
crash (and `Q`) made the new state `st'` of; the old maps' authorities and the resources of the
changes in flight; the new generation's files not taken, which are the new state's; the old
history's authority and the new history, until taken. -/
def crashRest (Q : OsState → OsState → Prop) (hL hL' : OsGS GF) (D : List Ino) (tt : Bool)
    (V' : Hist) : IProp GF :=
  iprop(∃ (Γb : GMap (Ino × Nat) ByteG) (Γm : GMap Ino OsMeta) (F : GMap Ino OsFile)
      (st st' : OsState) (Γf : GMap w64 OsFd) (Γt : GMap Nat TokInfo) (V : Hist),
    ⌜OsWf st ∧ OsCoh st Γb Γm Γf Γt ∧ OsCrash st st' ∧ Q st st' ∧
      (∀ i, i ∉ D → F !! i = st'.fs.files !! i) ∧
      st'.fs.roots = st.fs.roots ∧ TreeCrashed V V' ∧
      (∀ i, Named V'.now i → (st'.fs.files !! i).isSome)⌝ ∗
    gAuth hL hL.γb Γb ∗ gAuth hL hL.γm Γm ∗ ([∗map] i ↦ f ∈ F, fileStart hL' i f) ∗
    gAuth hL hL.γt Γt ∗ tokRes hL Γt ∗
    gAuth hL hL.γd (histMap (st.fs.roots, V)) ∗ treeLeft hL' st.fs.roots V' tt)

/-- The restart's resources, and the new generation's half of the cells' view (for
`osInv_alloc`). -/
def osCrashStart (Q : OsState → OsState → Prop) (hL hL' : OsGS GF) : IProp GF :=
  iprop(gVar hL' (1 : Qp).half ((∅ : GMap Loc (Option w8 × Bool)), 0) ∗
    ∃ V', crashRest Q hL hL' [] false V')

variable (hL : OsGS GF)

theorem bytesG_lookup_runs (i : Ino) (Γb : GMap (Ino × Nat) ByteG) :
    ∀ rs : List (Nat × DFrac × List ByteG),
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

theorem crashRest_files_delete {F : GMap Ino OsFile} {st' : OsState} {D : List Ino} {i : Ino}
    (hF : ∀ q, q ∉ D → F !! q = st'.fs.files !! q) :
    ∀ q, q ∉ i :: D → GMap.delete i F !! q = st'.fs.files !! q := by
  intro q hqD
  have hqp : q ≠ i := fun h => hqD (h ▸ List.mem_cons_self)
  rw [GMap.lookup_delete_ne _ (Ne.symm hqp)]
  exact hF q (fun h => hqD (List.mem_cons_of_mem _ h))

variable (hL' : OsGS GF) in
/-- Takes the new file `i` from the files not yet taken. -/
theorem files_take (F : GMap Ino OsFile) (i : Ino) :
    ([∗map] q ↦ f ∈ F, fileStart hL' q f) ⊢
      fileStartO hL' i (F !! i) ∗ [∗map] q ↦ f ∈ GMap.delete i F, fileStart hL' q f := by
  cases hF : F !! i with
  | none =>
    have : GMap.delete i F = F := GMap.ext (fun q => by
      by_cases hq : q = i
      · subst hq; rw [GMap.lookup_delete, hF]
      · rw [GMap.lookup_delete_ne _ (Ne.symm hq)])
    rw [this]; iintro H; iframe H; unfold fileStartO; iempintro
  | some f =>
    iintro H
    icases (BigSepM.bigSepM_delete (Φ := fun q f => fileStart hL' q f) hF).1 $$ H with ⟨Hf, H⟩
    iframe H; unfold fileStartO; iexact Hf

/-- At most one change is in flight on a file: two ghost entries of changes on one file are one. -/
theorem tok_one {st : OsState} {Γb Γm Γf} {Γt : GMap Nat TokInfo} (hwf : OsWf st)
    (hcoh : OsCoh st Γb Γm Γf Γt) {t t' : Nat} {ti ti' : TokInfo} (h : Γt !! t = some ti)
    (h' : Γt !! t' = some ti') (hp : ti'.ino = ti.ino) : t' = t ∧ ti' = ti := by
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 (by rw [← hcoh.toks t, h]; rfl)
  obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.1 (by rw [← hcoh.toks t', h']; rfl)
  have hi := (hcoh.tok_is t ti c h hc).1
  have hi' := (hcoh.tok_is t' ti' c' h' hc').1
  have htt := hwf.infl_one t' c' t c hc' hc (by rw [hi, hi', hp])
  subst htt
  rw [h] at h'; cases h'
  exact ⟨rfl, rfl⟩

/-- **Taking a file after a crash**, with a fraction of its `OsMeta` and its bytes in runs, giving
back the old generation's resources it looks at (so that an invariant that held them can be closed
again). -/
theorem crashRest_take_runs_keep (Q : OsState → OsState → Prop) (hL' : OsGS GF) (D : List Ino)
    (tt : Bool) (V' : Hist) (i : Ino) (hi : i ∉ D) (dq : DFrac) (m : OsMeta)
    (rs : List (Nat × DFrac × List ByteG)) :
    ⊢ crashRest Q hL hL' D tt V' -∗ gElem hL hL.γm i dq m -∗
      ([∗list] r ∈ rs, bytesG hL i r.1 r.2.1 r.2.2) -∗
      ∃ fo, ⌜FileCrashedR m rs fo ∧ (Named V'.now i → fo.isSome) ∧ CrashSeenR Q i m rs [] fo⌝ ∗
        fileStartO hL' i fo ∗ crashRest Q hL hL' (i :: D) tt V' ∗
        gElem hL hL.γm i dq m ∗ ([∗list] r ∈ rs, bytesG hL i r.1 r.2.1 r.2.2) := by
  unfold crashRest
  iintro ⟨%Γb, %Γm, %F, %st, %st', %Γf, %Γt, %V, %hrel, Hab, Ham, Hfs, HAt, Htok, HAd, Ht⟩
    Hm Hbs
  obtain ⟨hwf, hcoh, hcr, hQ, hF, hroots, htc, hnamed⟩ := hrel
  icases gAuth_lookup hL _ _ _ _ _ $$ Ham Hm with %hmo
  icases bytesG_lookup_runs hL i Γb rs $$ Hab Hbs with %hxs
  icases tokRes_meta_whole hL $$ Htok Hm with %hnt
  icases files_take hL' F i $$ Hfs with ⟨Hf, Hfs⟩
  have hFi := hF i hi
  have hseen : CrashSeenR Q i m rs [] (F !! i) :=
    ⟨st, st', Γb, Γm, Γf, Γt, hwf, hcoh, hcr, hQ, hFi.symm, hmo, hxs,
      fun t ti ht hp => absurd hp (hnt t ti ht), fun _ h => nomatch h⟩
  iexists F !! i
  iframe Hf Hm Hbs
  isplitr
  · ipureintro
    exact ⟨crashSeen_crashed hseen, fun hn => by rw [hFi]; exact hnamed i hn, hseen⟩
  iexists Γb, Γm, GMap.delete i F, st, st', Γf, Γt, V
  iframe Hab Ham Hfs HAt Htok HAd Ht
  ipureintro
  exact ⟨hwf, hcoh, hcr, hQ, crashRest_files_delete hF, hroots, htc, hnamed⟩

/-- **Taking the file a change in flight is on**, with its token, giving back the token: the
change holds the file's `OsMeta` and the bytes it announced below the size (a run at `ti.lo`). -/
theorem crashRest_take_tok_keep (Q : OsState → OsState → Prop) (hL' : OsGS GF) (D : List Ino)
    (tt : Bool) (V' : Hist) (t : Nat) (ti : TokInfo) (hi : ti.ino ∉ D)
    (rs : List (Nat × DFrac × List ByteG)) :
    ⊢ crashRest Q hL hL' D tt V' -∗ gElem hL hL.γt t (DFrac.own 1) ti -∗
      ([∗list] r ∈ rs, bytesG hL ti.ino r.1 r.2.1 r.2.2) -∗
      ∃ fo, ⌜FileCrashedR ti.meta ((ti.lo, DFrac.own 1, ti.saved) :: rs) fo ∧
          (Named V'.now ti.ino → fo.isSome) ∧
          CrashSeenR Q ti.ino ti.meta ((ti.lo, DFrac.own 1, ti.saved) :: rs) [(t, ti)] fo⌝ ∗
        fileStartO hL' ti.ino fo ∗ crashRest Q hL hL' (ti.ino :: D) tt V' ∗
        gElem hL hL.γt t (DFrac.own 1) ti ∗
        ([∗list] r ∈ rs, bytesG hL ti.ino r.1 r.2.1 r.2.2) := by
  iintro Hr Ht Hbs
  unfold crashRest
  icases Hr with ⟨%Γb, %Γm, %F, %st, %st', %Γf, %Γt, %V, %hrel, Hab, Ham, Hfs, HAt, Htok,
    HAd, Htl⟩
  obtain ⟨hwf, hcoh, hcr, hQ, hF, hroots, htc, hnamed⟩ := hrel
  icases gAuth_lookup hL _ _ _ _ _ $$ HAt Ht with %hti
  unfold tokRes
  icases (BigSepM.bigSepM_delete (Φ := fun _ (ti : TokInfo) => iprop(
      gElem hL hL.γm ti.ino (DFrac.own 1) ti.meta ∗
      bytesG hL ti.ino ti.lo (DFrac.own 1) ti.saved)) hti).1
    $$ Htok with ⟨⟨Hm, Hb⟩, Htok⟩
  icases gAuth_lookup hL _ _ _ _ _ $$ Ham Hm with %hmo
  icases bytesG_lookup_runs hL ti.ino Γb ((ti.lo, DFrac.own 1, ti.saved) :: rs) $$ Hab [Hb Hbs]
    with %hxs
  · iapply BigSepL.bigSepL_cons.2; iframe
  icases files_take hL' F ti.ino $$ Hfs with ⟨Hf, Hfs⟩
  have hFi := hF ti.ino hi
  have hseen : CrashSeenR Q ti.ino ti.meta ((ti.lo, DFrac.own 1, ti.saved) :: rs) [(t, ti)]
      (F !! ti.ino) := by
    refine ⟨st, st', Γb, Γm, Γf, Γt, hwf, hcoh, hcr, hQ, hFi.symm, hmo, hxs,
      fun t' ti' ht' hp => ?_, fun x hx => ?_⟩
    · obtain ⟨rfl, rfl⟩ := tok_one hwf hcoh hti ht' hp
      exact List.mem_singleton.2 rfl
    · rw [List.mem_singleton] at hx; subst hx; exact hti
  iexists F !! ti.ino
  iframe Hf Ht Hbs
  isplitr
  · ipureintro
    exact ⟨crashSeen_crashed hseen, fun hn => by rw [hFi]; exact hnamed _ hn, hseen⟩
  iexists Γb, Γm, GMap.delete ti.ino F, st, st', Γf, Γt, V
  iframe Hab Ham Hfs HAt HAd Htl
  isplitr
  · ipureintro
    exact ⟨hwf, hcoh, hcr, hQ, crashRest_files_delete hF, hroots, htc, hnamed⟩
  iapply (BigSepM.bigSepM_delete (Φ := fun _ (ti : TokInfo) => iprop(
      gElem hL hL.γm ti.ino (DFrac.own 1) ti.meta ∗
      bytesG hL ti.ino ti.lo (DFrac.own 1) ti.saved)) hti).2
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
  iintro ⟨%Γb, %Γm, %F, %st, %st', %Γf, %Γt, %V, %hrel, Hab, Ham, Hfs, HAt, Htok, HAd, Htl⟩
    Hd
  icases gAuth_lookup hL _ _ _ _ _ $$ HAd Hd with %hh
  simp only [histMap, GMap.lookup_singleton_eq, Option.some.injEq, Prod.mk.injEq] at hh
  obtain ⟨rfl, rfl⟩ := hh
  unfold treeLeft
  iframe Htl Hd
  isplitr
  · ipureintro; exact hrel.2.2.2.2.2.2.1
  iexists Γb, Γm, F, st, st', Γf, Γt, V
  iframe
  ipureintro; exact hrel

/-- **The crash of the extension's ghost state**: the new generation's ghost state from the state
the crash left (one a program may start in), and the restart's resources. -/
theorem os_local_crash (Q : OsState → OsState → Prop) (hPre : OsGpreS GF) (st st' : OsState)
    (hc : OsCrash st st') (hQ : Q st st') :
    ⊢@{IProp GF} osCtx hL st ==∗ ∃ hL' : OsGS GF, osCtx hL' st' ∗ osCrashStart Q hL hL' := by
  unfold osCtx osCtxF treeCtx
  iintro ⟨⟨%Γb, %Γm, %Γf, %Γt, %hwc, Hab, Ham, -, HAt, Htok, -⟩,
    ⟨%V, %Γdf, %Γc, %htw, HAd, -, -, -, -⟩⟩
  obtain ⟨hinit, hroots, hcr, hnamed⟩ := osCrash_rel htw.1 htw.2 hc
  have hdisk : ∀ i f, st'.fs.files !! i = some f → ∃ img sz, f = OsFile.ofDisk img sz :=
    fun i f hf => (hinit.2.2.2.2.2.2.1 i f hf).2
  imod os_local_init hPre st' hinit with ⟨%hL', Hctx, Hst⟩
  unfold osStart osStartF treeStart bytesMap metaMap
  icases Hst with ⟨⟨Hb, Hm, Hv⟩, Hd⟩
  ihave Hfs := start_files hL' hdisk $$ [Hb Hm]
  · iframe
  unfold osCtx osCtxF treeCtx
  imodintro
  iexists hL'
  iframe Hctx
  unfold osCrashStart crashRest treeLeft
  iframe Hv
  iexists (st'.fs.treeDur, []), Γb, Γm, st'.fs.files, st, st', Γf, Γt, V
  rw [hroots]
  iframe Hab Ham Hfs HAt Htok HAd Hd
  ipureintro
  exact ⟨hwc.1, hwc.2, hc, hQ, fun _ _ => rfl, rfl, hcr, hnamed⟩

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

/-- The file `f` of inode `i` as a generation starts with it (at the first start, or after a
crash): on disk, its `OsMeta` as `initMeta` says, its bytes whole, each durable. -/
def osFileStart [L : GooseLocalGS GF] (i : Ino) (f : OsFile) : IProp GF :=
  iprop(osMeta (L := L) i (DFrac.own 1) (initMeta f) ∗
    osBytes (L := L) i 0 (DFrac.own 1) (f.contents.map durB))

/-- The file of inode `i`, if the crash kept it. -/
def osFileStartO [L : GooseLocalGS GF] (i : Ino) : Option OsFile → IProp GF
  | none => iprop(emp)
  | some f => osFileStart (L := L) i f

theorem fileStart_eq [L : GooseLocalGS GF] (i : Ino) (f : OsFile) :
    fileStart (gooseOsGS (L := L)) i f ⊣⊢ osFileStart (L := L) i f := .rfl

theorem fileStartO_eq [L : GooseLocalGS GF] (i : Ino) (fo : Option OsFile) :
    fileStartO (gooseOsGS (L := L)) i fo ⊣⊢ osFileStartO (L := L) i fo := by
  cases fo <;> exact .rfl

/-- `crashRest_take_runs_keep` from the old generation `L` to the new one `L'`. -/
theorem osCrash_take_runs_keep (Q : OsState → OsState → Prop) (L L' : GooseLocalGS GF)
    (D : List Ino) (tt : Bool) (V' : Hist) (i : Ino) (hi : i ∉ D) (dq : DFrac) (m : OsMeta)
    (rs : List (Nat × DFrac × List ByteG)) :
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
    (D : List Ino) (tt : Bool) (V' : Hist) (t : Nat) (ti : TokInfo) (hi : ti.ino ∉ D)
    (rs : List (Nat × DFrac × List ByteG)) :
    ⊢ crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) D tt V' -∗ osTok (L := L) t ti -∗
      ([∗list] r ∈ rs, osBytes (L := L) ti.ino r.1 r.2.1 r.2.2) -∗
      ∃ fo, ⌜FileCrashedR ti.meta ((ti.lo, DFrac.own 1, ti.saved) :: rs) fo ∧
          (Named V'.now ti.ino → fo.isSome) ∧
          CrashSeenR Q ti.ino ti.meta ((ti.lo, DFrac.own 1, ti.saved) :: rs) [(t, ti)] fo⌝ ∗
        osFileStartO (L := L') ti.ino fo ∗
        crashRest Q (gooseOsGS (L := L)) (gooseOsGS (L := L')) (ti.ino :: D) tt V' ∗
        osTok (L := L) t ti ∗ ([∗list] r ∈ rs, osBytes (L := L) ti.ino r.1 r.2.1 r.2.2) := by
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
