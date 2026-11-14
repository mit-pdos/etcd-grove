/-
WP specs of `open(2)` (`Impl.lean`'s `Open`): of a directory (a directory fd, which holds the call's
fraction of the tree's history until its close), of an existing file (with or without `O_CREAT`:
the retry of a create that made the file), and with `O_CREAT` of a new name (a new file of a fresh
inode, its `create` logged: the whole history). `O_TRUNC` is not covered here. Every open is a call
on a path (`osCall`), whose step ends it. Untrusted.
-/
module

public import GooseLang.Ext.Fs.TreeSpecsDirFd
public import GooseLang.Ext.Fs.Specs

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

/-! ## Pure facts -/

/-- `O_RDONLY | O_CLOEXEC`, as `os.OpenFile`'s model passes `O_RDONLY`. -/
abbrev flRO : w64 := W64 0x80000
/-- `O_RDWR | O_CREAT | O_CLOEXEC`. -/
abbrev flCreat : w64 := W64 0x80042

theorem flRO_ok : OpenFlagsOk flRO.toNat := by
  simp only [OpenFlagsOk, O_CREAT, O_TRUNC, O_CLOEXEC]; decide
theorem flCreat_ok : OpenFlagsOk flCreat.toNat := by
  simp only [OpenFlagsOk, O_CREAT, O_TRUNC, O_CLOEXEC]; decide

/-- The fd an open with the flags `fl` gives on the file `i`. -/
def openFd (i : Ino) (fl : w64) : OsFd :=
  ⟨i, decide (fl.toNat % 4 ≠ O_WRONLY), decide (fl.toNat % 4 ≠ O_RDONLY)⟩

theorem fsTreeWf_metaEnd {st : OsState} (hw : FsTreeWf st) (k : Nat) : FsTreeWf (st.metaEnd k) :=
  ⟨hw.roots, hw.hist, hw.dfds, hw.disj, hw.files_lt⟩

/-- A call ended: the coherence, without its entry. -/
theorem treeCoh_metaEnd {st : OsState} {V Γdf Γc} (hc : TreeCoh st V Γdf Γc) (k : Nat) :
    TreeCoh (st.metaEnd k) V Γdf (GMap.delete k Γc) := by
  refine ⟨hc.hist, hc.seq, hc.fds, hc.ph, hc.rd, fun t0 => ?_, fun t0 x hx => ?_⟩
  · show _ = (GMap.delete k st.proc.calls) !! t0
    by_cases h0 : k = t0
    · subst h0; simp
    · rw [GMap.lookup_delete_ne _ h0, GMap.lookup_delete_ne _ h0]; exact hc.calls t0
  · by_cases h0 : k = t0
    · subst h0; simp at hx
    · rw [GMap.lookup_delete_ne _ h0] at hx; exact hc.start t0 x hx

theorem filesSame_metaEnd (st : OsState) (k : Nat) : FilesSame st (st.metaEnd k) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The whole tree is well formed now. -/
theorem treeWf_now {st : OsState} (hw : FsTreeWf st) : TreeWf st.fs.roots st.tree := by
  have := (hw.hist st.fs.metaLog.length (Nat.le_refl _)).1
  rw [List.take_length] at this; exact this

/-- A directory a path names is one of the tree's. -/
theorem mem_of_lookup_dir {st : OsState} (hw : FsTreeWf st) {p : GoString} {j : Ino}
    (h : st.lookup p = some (.dir j)) : j ∈ st.tree :=
  (treeWf_now hw).1 j (reach_of_lookup h)

/-- A file a path names is one of `files`. -/
theorem file_of_lookup {st : OsState} (hw : FsTreeWf st) {p : GoString} {i : Ino}
    (h : st.lookup p = some (.file i)) : ∃ f, st.file i = some f := by
  have := (hw.hist st.fs.metaLog.length (Nat.le_refl _)).2.1
  rw [List.take_length] at this
  exact this i (named_of_lookup h)

/-! ## A file created -/

/-- The ghost `OsMeta` of a file just created: empty, durable, zeros from offset 0 on. -/
abbrev newMeta : OsMeta := initMeta newFile

theorem newFile_size : newFile.size = 0 := rfl
theorem newFile_contents : newFile.contents = [] := rfl

theorem newMeta_zf : newMeta.zf = some 0 := rfl

section create
variable {st : OsState} {n : Ino}

theorem sizes_create (hn : st.file n = none) : ∀ q, (st.setFile n newFile).size q = st.size q := by
  intro q; rw [size_setFile]; split
  · subst_vars; simp [OsState.size, hn, newFile, OsFile.ofBytes, OsFile.ofDisk]
  · rfl

theorem osWf_create (hwf : OsWf st) (hn : st.file n = none) : OsWf (st.setFile n newFile) := by
  have hex : ∀ q f0, st.file q = some f0 → ∃ f1, (st.setFile n newFile).file q = some f1 := by
    intro q f0 h0; rw [file_setFile]; split
    · exact ⟨_, rfl⟩
    · exact ⟨_, h0⟩
  refine ⟨fun fd d h => ?_, fun b m h => ?_, hwf.maps_disj, fun t c h => ?_, hwf.infl_one, ?_, ?_⟩
  · obtain ⟨f0, h0⟩ := hwf.fds fd d h; exact hex _ _ h0
  · obtain ⟨⟨f0, h0⟩, h1, h2, h3⟩ := hwf.maps b m h; exact ⟨hex _ _ h0, h1, h2, h3⟩
  · obtain ⟨f0, h0⟩ := hwf.infl t c h; exact hex _ _ h0
  · intro q f1 h1
    rw [file_setFile] at h1; split at h1
    · cases h1; simp [newFile, OsFile.ofBytes, OsFile.ofDisk]
    · exact hwf.sizes q f1 h1
  · intro q f1 b p h1 hp
    rw [file_setFile] at h1; split at h1
    · cases h1; simp only [newFile, OsFile.ofBytes, OsFile.ofDisk, List.mem_singleton] at hp
      subst hp; simp
    · exact hwf.stamps q f1 b p h1 hp

theorem cellView_create (hwf : OsWf st) (hn : st.file n = none) :
    cellView (st.setFile n newFile) = cellView st := by
  have hI : ∀ q i, InflightAt (st.setFile n newFile) q i = InflightAt st q i :=
    inflightAt_congr rfl
  refine cellView_congr' hwf (osWf_create hwf hn) rfl (fun q i => ?_) hI
  by_cases hpq : n = q
  · subst hpq; unfold cellByte; rw [file_setFile_eq, hn]
    simp [newFile, OsFile.ofBytes, OsFile.ofDisk, OsFile.contents]
  · unfold cellByte; rw [file_setFile_ne _ _ hpq, hI]

theorem osCoh_create {Γb Γm Γf Γt} (hwf : OsWf st) (hcoh : OsCoh st Γb Γm Γf Γt)
    (hn : st.file n = none) :
    OsCoh (st.setFile n newFile) Γb (<[n := newMeta]> Γm) Γf Γt := by
  have hnt : ∀ t c, st.proc.inflight !! t = some c → c.ino ≠ n := by
    intro t c ht hcp
    obtain ⟨f, hf⟩ := hwf.infl t c ht
    rw [hcp, hn] at hf; cases hf
  have hnt' : ∀ t ti, Γt !! t = some ti → ti.ino ≠ n := by
    intro t ti h hp
    have := hcoh.tok_file t ti h
    obtain ⟨f, hf, -⟩ := this
    rw [hp, hn] at hf; cases hf
  refine ⟨fun q => ?_, fun q m hm => ?_, fun q i x hx => ?_, fun q f1 i h1 hi => ?_,
    hcoh.fds, hcoh.toks, hcoh.tok_is, fun t ti h => ?_, fun t ti h => ?_, fun t ti h => ?_,
    fun t ti h hk => ?_, fun q m c hm hc => ?_⟩
  · rw [files_setFile, GMap.lookup_insert_eq_iff]; split
    · simp
    · exact hcoh.meta_dom q
  · rw [GMap.lookup_insert_eq_iff] at hm
    split at hm
    · subst_vars; cases hm
      refine ⟨newFile, by rw [files_setFile, if_pos rfl], ?_⟩
      have := metaOk_ofDisk (st := st.setFile q newFile) (i := q) (fun _ => 0) 0
        (fun b m h => by
          intro hp
          obtain ⟨⟨f0, hf0⟩, -⟩ := hwf.maps b m h
          rw [hp] at hf0; rw [hn] at hf0; cases hf0)
        (fun t c ht hc => hnt t c ht hc)
      exact this
    · rename_i hpq
      obtain ⟨f1, h1, hm1⟩ := hcoh.meta_some q m hm
      exact ⟨f1, by rw [files_setFile, if_neg hpq]; exact h1, MetaOk.transfer (st := st) (st' := st.setFile n newFile) rfl rfl hm1⟩
  · obtain ⟨f1, h1, hb, hx1⟩ := hcoh.bytes q i x hx
    have hpq : n ≠ q := fun e => by subst e; rw [hn] at h1; cases h1
    refine ⟨f1, by rw [file_setFile_ne _ _ hpq]; exact h1, hb, ?_⟩
    rw [cutOf_insert, if_neg hpq]; exact hx1
  · rw [file_setFile] at h1; split at h1
    · cases h1; simp [newFile, OsFile.ofBytes, OsFile.ofDisk] at hi
    · exact hcoh.bytes_full q f1 i h1 hi
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm (hnt' t ti h))]; exact hcoh.tok_meta t ti h
  · obtain ⟨f1, h1, hrest⟩ := hcoh.tok_file t ti h
    exact ⟨f1, by rw [file_setFile_ne _ _ (Ne.symm (hnt' t ti h))]; exact h1, hrest⟩
  · obtain ⟨f1, h1, hrest⟩ := hcoh.tok_cand t ti h
    exact ⟨f1, by rw [file_setFile_ne _ _ (Ne.symm (hnt' t ti h))]; exact h1, hrest⟩
  · obtain ⟨f1, h1, hrest⟩ := hcoh.tok_rz t ti h hk
    exact ⟨f1, by rw [file_setFile_ne _ _ (Ne.symm (hnt' t ti h))]; exact h1, hrest⟩
  · rw [GMap.lookup_insert_eq_iff] at hm
    split at hm
    · cases hm; simp [newMeta, initMeta] at hc
    · exact hcoh.cut_le q m c hm hc

end create

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [GoGlobalContext]
  [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

/-- The tree's world, from its parts. -/
theorem treeWorld_mk {st st' : OsState} {V : Hist} {Γdf : GMap w64 (Ino × DirPh)}
    {Γc : GMap Nat (Nat × Qp)} (hroots : st'.fs.roots = st.fs.roots) (hw' : FsTreeWf st')
    (hc' : TreeCoh st' V Γdf Γc) :
    ⊢ gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γd (histMap (st.fs.roots, V)) -∗
      gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γdf Γdf -∗
      gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γc Γc -∗
      rdRes (gooseOsGS (L := L)) Γdf -∗ callRes (gooseOsGS (L := L)) Γc -∗
      treeWorld (L := L) st' V Γdf Γc := by
  iintro HAd HAdf HAc Hrd Hcr
  unfold treeWorld
  rw [hroots]
  iframe
  ipureintro; exact ⟨hw', hc'⟩

/-- The files' world after a step that adds the fd `fd` on an existing file and otherwise leaves
the files alone (`st0`, then `fd` added). -/
theorem osWorld_addFd {st st0 : OsState} {Γb Γm Γf Γt} {h h' : GMap Loc (NonAtomic val)}
    (hs : FilesSame st st0) {fd : w64} {d : OsFd} (hfd : st.proc.fds !! fd = none)
    (hfd0 : 0 ≤ fd.toInt) (hfile : ∃ f, st.file d.ino = some f)
    (hr : HeapRendered st (st0.setProc { st0.proc with fds := <[fd := d]> st0.proc.fds }) h h')
    (hfr : MapsFresh st (st0.setProc { st0.proc with fds := <[fd := d]> st0.proc.fds }) h) :
    ⊢ osWorld (L := L) st Γb Γm Γf Γt h ==∗
      osWorld (L := L) (st0.setProc { st0.proc with fds := <[fd := d]> st0.proc.fds }) Γb Γm
        (<[fd := d]> Γf) Γt h' ∗ osFd (L := L) fd (DFrac.own 1) d := by
  unfold osWorld
  iintro ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  have hwf0 := osWf_filesSame hs hwf
  have hcoh0 := osCoh_filesSame hs hcoh
  have hf0 : ∀ i, st0.file i = st.file i := filesSame_file hs
  have hwf' : OsWf (st0.setProc { st0.proc with fds := <[fd := d]> st0.proc.fds }) := by
    refine osWf_fds hwf0 _ (fun fd' d' h' => ?_)
    rw [GMap.lookup_insert_eq_iff] at h'; split at h'
    · cases h'; rw [hf0]; exact hfile
    · exact hwf0.fds fd' d' h'
  have hΓf : Γf = st0.proc.fds := by rw [hcoh.fds, hs.2.1]
  have hcoh' : OsCoh (st0.setProc { st0.proc with fds := <[fd := d]> st0.proc.fds }) Γb Γm
      (<[fd := d]> Γf) Γt := by
    rw [hΓf]; exact osCoh_fds hcoh0 _
  have hΓfn : Γf !! fd = none := by rw [hcoh.fds]; exact hfd
  imod gFdElem_insert _ _ _ fd d hfd0 hΓfn $$ HAf with ⟨HAf, Hfd⟩
  have hcv : cellView (st0.setProc { st0.proc with fds := <[fd := d]> st0.proc.fds }) =
      cellView st := cellView_congr hwf hwf' hs.2.2.2.1 (fun i => congrArg _ (hf0 i)) hs.2.2.1
  imod cells_same hwf hwf' hr hfr hs.2.2.2.1 hcv $$ [Hσ Hcells] with ⟨Hσ, Hcells⟩
  · iframe
  imodintro
  unfold osFd
  iframe
  ipureintro; exact ⟨hwf', hcoh'⟩

/-- **`open(2)` of a directory**, read-only, a call `k` with a fraction of the history in which
the path names the directory `j`: a new directory fd, not read, which holds the call's fraction
until its close; or an errno, the call's fraction back. -/
theorem wp_osOpenDir (p : GoString) (R : Roots) (V : Hist) (q1 q : Qp) (k s0 : Nat) (j : Ino)
    (hl : lookupH R V p = some (.dir j)) (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osTree (L := L) (DFrac.own q1) R V -∗ osCall (L := L) k s0 q -∗
      (∀ fd : w64, ∀ e : w64, ⌜(e = 0 ∧ 0 ≤ fd.toInt) ∨ (e ≠ 0 ∧ fd = -1)⌝ -∗
        (if e = 0 then osTree (L := L) (DFrac.own q1) R V ∗
            osDirFd (L := L) fd (DFrac.own 1) (j, .idle (dview V j) q)
          else osTree (L := L) (DFrac.own (q1 + q)) R V) -∗
        Φ (PairV (#fd) (#e))) -∗
      WP (ExternalOp fsExt.name "Open" (Val (PairV (osTokV k) (PairV (#p) (#flRO))))) @ s; E
        {{ Φ }} := by
  iintro #Hinv Hh Hk HΦ
  iapply wp_fs_stepT "Open" _ Φ (by simp [val.isPanic]) hE _ (legacyWit_call _ _ _) $$ Hinv Hk
  iintro Hk %st %Γb %Γm %Γf %Γt %V0 %Γdf %Γc %h Hw Hn
  unfold treeWorld
  icases Hn with ⟨%Hns, HAd, HAdf, HAc, Hrd, Hcr⟩
  obtain ⟨hw, hc⟩ := Hns
  icases osTree_auth _ _ _ _ _ $$ HAd Hh with %Heq
  obtain ⟨rfl, rfl⟩ := Heq
  icases osCall_auth Γc k s0 q $$ HAc Hk with %hk
  have hcall : st.proc.calls !! k = some s0 := by rw [← hc.calls k, hk]; rfl
  have hV := hc.hist
  subst hV
  have hl' : st.lookup p = some (.dir j) := hl
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hcr : decide ((flRO.toNat / O_CREAT) % 2 = 1) = false := by decide
  have htr : decide ((flRO.toNat / O_TRUNC) % 2 = 1) = false := by decide
  have hacc : flRO.toNat % 4 = O_RDONLY := by decide
  imodintro
  isplitr
  · ipureintro
    obtain ⟨hfr, hr⟩ := step_filesSame (h := h) Hwc.1 (filesSame_metaEnd st k) Hag
    exact ⟨_, h, _, .inl ⟨p, flRO, k, s0, rfl, treePath_of_lookup hl', flRO_ok, hcall,
      ⟨fun h => (Bool.false_ne_true (htr.symm.trans h)).elim, .inr ⟨1, by decide, fun h => absurd h (by decide), rfl, .inl rfl⟩⟩⟩, hfr, hr⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsFsStep] at Hst
  replace Hst := open_inTree Hst (treePath_of_lookup hl')
  obtain ⟨p', fl, k', s', hv, -, -, hk', hres⟩ := Hst
  injection hv with hv1 hv2
  have hkk : k' = k := by injection hv1 with h1; exact (extVal_inj h1).symm
  subst hkk
  injection hv2 with hv3 hv4
  cases go.intoVal_inj hv3; cases go.intoVal_inj hv4
  rw [hcall] at hk'; cases hk'
  simp only [hcr, htr, hacc, Bool.false_eq_true, ↓reduceIte] at hres
  have hl0 : (st.metaEnd k').lookup p = some (.dir j) := hl'
  imod call_end _ _ Γc k' s0 q $$ HAd HAc Hcr Hk with ⟨%hk2, HAd, HAc, Hcr, Hq⟩
  ihave Hw : osWorld (L := L) st Γb Γm Γf Γt h $$ [HAb HAm HAf HAt Htok Hcells Hσ]
  · unfold osWorld; iframe; ipureintro; exact Hwc
  obtain ⟨-, hres⟩ := hres
  rcases hres with ⟨st1, tgt, fd, heff, hfree, hst, rfl⟩ | ⟨e, he, -, rfl, hst⟩
  · unfold OpenEffect at heff
    rw [hl0] at heff
    obtain ⟨-, -, -, hst1, rfl⟩ := heff
    subst st1
    obtain ⟨hfd0, hfdn, hdfn, -⟩ := hfree
    have hΓ : Γdf !! fd = none := by
      have := hc.fds fd; rw [hdfn] at this
      cases h0 : Γdf !! fd with
      | none => rfl
      | some x => rw [h0] at this; cases this
    imod gFdElem_insert _ _ _ fd (j, DirPh.idle (dview (st.fs.treeDur, st.fs.metaLog) j) q) hfd0 hΓ $$ HAdf
      with ⟨HAdf, Hfd⟩
    have hst'' : st' = setDfd (st.metaEnd k') fd ⟨j, .idle⟩ := hst
    subst hst''
    have hs : FilesSame st (setDfd (st.metaEnd k') fd ⟨j, .idle⟩) := ⟨rfl, rfl, rfl, rfl, rfl⟩
    have hw' := fsTreeWf_setDfd (fsTreeWf_metaEnd hw k') (fd := fd) (df' := ⟨j, .idle⟩) hfdn
      (mem_of_lookup_dir hw hl')
    have hc' := treeCoh_setDfd (fd := fd) (df' := ⟨j, .idle⟩)
      (x := (j, DirPh.idle (dview (st.fs.treeDur, st.fs.metaLog) j) q)) (treeCoh_metaEnd hc k')
      rfl trivial rfl
    ihave Hrd : rdRes (gooseOsGS (L := L))
        (<[fd := (j, DirPh.idle (dview (st.fs.treeDur, st.fs.metaLog) j) q)]> Γdf) $$ [Hrd Hq]
    · unfold rdRes
      iapply (BigSepM.bigSepM_insert (M := GMap w64)
        (Φ := fun (_ : w64) (x : Ino × DirPh) => rdPart (gooseOsGS (L := L)) x) hΓ).2
      iframe Hrd; unfold rdPart osTree; dsimp only [DirPh.q, DirPh.g]
      iexists (st.fs.roots, (st.fs.treeDur, st.fs.metaLog))
      iframe Hq
      ipureintro; rfl
    imod worlds_close hs Hr Hfr rfl hw' hc' $$ Hw HAd HAdf HAc Hrd Hcr with ⟨Hw, Hn⟩
    imodintro
    iexists Γb, Γm, Γf, Γt, (st.fs.treeDur, st.fs.metaLog), _, _
    try unfold osWorld
    try unfold treeWorld
    try unfold osDirFd
    try unfold rdRes
    try unfold osFd
    isplitl [Hw]
    · iexact Hw
    isplitl [Hn]
    · iexact Hn
    iapply wp_value'
    iapply HΦ $$ %fd %0 %(.inl ⟨rfl, hfd0⟩)
    rw [if_pos rfl]; iframe Hh; (try unfold osDirFd); iexact Hfd
  · have hst' : st' = st.metaEnd k' := by
      rcases hst with rfl | ⟨tgt, heff⟩
      · rfl
      · unfold OpenEffect at heff; rw [hl0] at heff; exact heff.2.2.2.1
    subst hst'
    imod worlds_close (filesSame_metaEnd st k') Hr Hfr rfl (fsTreeWf_metaEnd hw k')
      (treeCoh_metaEnd hc k') $$ Hw HAd HAdf HAc Hrd Hcr with ⟨Hw, Hn⟩
    imodintro
    iexists Γb, Γm, Γf, Γt, (st.fs.treeDur, st.fs.metaLog), Γdf, _
    try unfold osWorld
    try unfold treeWorld
    try unfold osDirFd
    try unfold rdRes
    try unfold osFd
    isplitl [Hw]
    · iexact Hw
    isplitl [Hn]
    · iexact Hn
    iapply wp_value'
    iapply HΦ $$ %(-1) %e %(.inr ⟨he, rfl⟩)
    rw [if_neg he]
    iapply (osTree_split q1 q _ _).2
    iframe

/-- **`open(2)` of an existing file**, without `O_TRUNC` (with or without `O_CREAT`: the retry of a
create that made the file), a call `k` with a fraction of the history in which the path names the
file `i`: a new fd on `i`; or an errno. Either way the call's fraction comes back. -/
theorem wp_osOpenFile (p : GoString) (fl : w64) (R : Roots) (V : Hist) (q1 q : Qp) (k s0 : Nat)
    (i : Ino) (hfl : OpenFlagsOk fl.toNat) (htr : fl.toNat / O_TRUNC % 2 = 0)
    (hl : lookupH R V p = some (.file i)) (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osTree (L := L) (DFrac.own q1) R V -∗ osCall (L := L) k s0 q -∗
      (∀ fd : w64, ∀ e : w64, ⌜(e = 0 ∧ 0 ≤ fd.toInt) ∨ (e ≠ 0 ∧ fd = -1)⌝ -∗
        osTree (L := L) (DFrac.own (q1 + q)) R V -∗
        (if e = 0 then osFd (L := L) fd (DFrac.own 1) (openFd i fl) else emp) -∗
        Φ (PairV (#fd) (#e))) -∗
      WP (ExternalOp fsExt.name "Open" (Val (PairV (osTokV k) (PairV (#p) (#fl))))) @ s; E
        {{ Φ }} := by
  iintro #Hinv Hh Hk HΦ
  iapply wp_fs_stepT "Open" _ Φ (by simp [val.isPanic]) hE _ (legacyWit_call _ _ _) $$ Hinv Hk
  iintro Hk %st %Γb %Γm %Γf %Γt %V0 %Γdf %Γc %h Hw Hn
  unfold treeWorld
  icases Hn with ⟨%Hns, HAd, HAdf, HAc, Hrd, Hcr⟩
  obtain ⟨hw, hc⟩ := Hns
  icases osTree_auth _ _ _ _ _ $$ HAd Hh with %Heq
  obtain ⟨rfl, rfl⟩ := Heq
  icases osCall_auth Γc k s0 q $$ HAc Hk with %hk
  have hcall : st.proc.calls !! k = some s0 := by rw [← hc.calls k, hk]; rfl
  have hV := hc.hist
  subst hV
  have hl' : st.lookup p = some (.file i) := hl
  obtain ⟨f, hfi⟩ := file_of_lookup hw hl'
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have htr' : decide ((fl.toNat / O_TRUNC) % 2 = 1) = false := by simp [htr]
  imodintro
  isplitr
  · ipureintro
    obtain ⟨hfr, hr⟩ := step_filesSame (h := h) Hwc.1 (filesSame_metaEnd st k) Hag
    exact ⟨_, h, _, .inl ⟨p, fl, k, s0, rfl, treePath_of_lookup hl', hfl, hcall,
      ⟨fun h => absurd h (by simp [htr']), .inr ⟨1, by decide, fun h => absurd h (by decide), rfl, .inl rfl⟩⟩⟩, hfr, hr⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsFsStep] at Hst
  replace Hst := open_inTree Hst (treePath_of_lookup hl')
  obtain ⟨p', fl, k', s', hv, -, -, hk', hres⟩ := Hst
  injection hv with hv1 hv2
  have hkk : k' = k := by injection hv1 with h1; exact (extVal_inj h1).symm
  subst hkk
  injection hv2 with hv3 hv4
  cases go.intoVal_inj hv3; cases go.intoVal_inj hv4
  rw [hcall] at hk'; cases hk'
  simp only [htr', Bool.false_eq_true, ↓reduceIte] at hres
  have hl0 : (st.metaEnd k').lookup p = some (.file i) := hl'
  imod call_end _ _ Γc k' s0 q $$ HAd HAc Hcr Hk with ⟨%hk2, HAd, HAc, Hcr, Hq⟩
  ihave Hh : osTree (L := L) (DFrac.own (q1 + q)) st.fs.roots (st.fs.treeDur, st.fs.metaLog)
    $$ [Hh Hq]
  · iapply (osTree_split q1 q _ _).2; iframe
  ihave Hw : osWorld (L := L) st Γb Γm Γf Γt h $$ [HAb HAm HAf HAt Htok Hcells Hσ]
  · unfold osWorld; iframe; ipureintro; exact Hwc
  obtain ⟨-, hres⟩ := hres
  rcases hres with ⟨st1, tgt, fd, heff, hfree, hst, rfl⟩ | ⟨e, he, -, rfl, hst⟩
  · unfold OpenEffect at heff
    rw [hl0] at heff
    obtain ⟨⟨f', -, hst1⟩, rfl⟩ := heff
    simp only [htr', Bool.false_eq_true, ↓reduceIte] at hst1
    subst st1
    obtain ⟨hfd0, hfdn, hdfn, -⟩ := hfree
    have hst'' : st' = (st.metaEnd k').setProc { (st.metaEnd k').proc with
        fds := <[fd := openFd i fl]> (st.metaEnd k').proc.fds } := hst
    subst hst''
    imod osWorld_addFd (filesSame_metaEnd st k') hfdn hfd0 ⟨f, hfi⟩ Hr Hfr $$ Hw with ⟨Hw, Hfd⟩
    have hw' : FsTreeWf ((st.metaEnd k').setProc { (st.metaEnd k').proc with
        fds := <[fd := openFd i fl]> (st.metaEnd k').proc.fds }) := by
      refine ⟨hw.roots, hw.hist, hw.dfds, fun fd' h' => ?_, fun i' hi' => hw.files_lt i' hi'⟩
      show st.proc.dfds !! fd' = none
      by_cases he : fd = fd'
      · subst he; exact hdfn
      · apply hw.disj fd'
        have h'' : (<[fd := openFd i fl]> st.proc.fds) !! fd' ≠ none := h'
        rwa [GMap.lookup_insert_ne _ _ he] at h''
    have hc' : TreeCoh ((st.metaEnd k').setProc { (st.metaEnd k').proc with
        fds := <[fd := openFd i fl]> (st.metaEnd k').proc.fds })
        (st.fs.treeDur, st.fs.metaLog) Γdf (GMap.delete k' Γc) :=
      (treeCoh_metaEnd hc k').congr rfl rfl rfl rfl
    ihave Hn := treeWorld_mk (st := st) (by rfl) hw' hc' $$ HAd HAdf HAc Hrd Hcr
    imodintro
    iexists Γb, Γm, _, Γt, (st.fs.treeDur, st.fs.metaLog), Γdf, _
    try unfold osWorld
    try unfold treeWorld
    try unfold osDirFd
    try unfold rdRes
    try unfold osFd
    isplitl [Hw]
    · iexact Hw
    isplitl [Hn]
    · iexact Hn
    iapply wp_value'
    iapply HΦ $$ %fd %0 %(.inl ⟨rfl, hfd0⟩) Hh
    rw [if_pos rfl]; iexact Hfd
  · have hst' : st' = st.metaEnd k' := by
      rcases hst with rfl | ⟨tgt, heff⟩
      · rfl
      · unfold OpenEffect at heff; rw [hl0] at heff
        obtain ⟨⟨f', -, h1⟩, -⟩ := heff
        simpa [htr'] using h1
    subst hst'
    imod worlds_close (filesSame_metaEnd st k') Hr Hfr rfl (fsTreeWf_metaEnd hw k')
      (treeCoh_metaEnd hc k') $$ Hw HAd HAdf HAc Hrd Hcr with ⟨Hw, Hn⟩
    imodintro
    iexists Γb, Γm, Γf, Γt, (st.fs.treeDur, st.fs.metaLog), Γdf, _
    try unfold osWorld
    try unfold treeWorld
    try unfold osDirFd
    try unfold rdRes
    try unfold osFd
    isplitl [Hw]
    · iexact Hw
    isplitl [Hn]
    · iexact Hn
    iapply wp_value'
    iapply HΦ $$ %(-1) %e %(.inr ⟨he, rfl⟩) Hh
    rw [if_neg he]; iempintro


theorem fmap_empty_dfds (f : OsDirFd → OsDirFd) : GMap.fmap f (∅ : GMap w64 OsDirFd) = ∅ := by
  apply GMap.ext; intro k; simp

/-- The state after `open(2)` with `O_CREAT` created `b` in the directory `j` (before its fd): the
call ended, the file of the fresh inode `nextIno` made, its `create` logged. -/
abbrev createdSt (st : OsState) (k : Nat) (j : Ino) (b : GoString) (s0 : Nat) : OsState :=
  (((st.metaEnd k).setFile (st.metaEnd k).fs.nextIno newFile).takeIno).metaDo
    (.create j b (st.metaEnd k).fs.nextIno) s0

theorem filesSame_created (st : OsState) (k : Nat) (j : Ino) (b : GoString) (s0 : Nat) :
    FilesSame ((st.metaEnd k).setFile st.fs.nextIno newFile) (createdSt st k j b s0) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **What creating `b` in the directory `j` keeps**, from a state where the call `k` holds the rest
of the whole history (no directory fd, no other call). -/
theorem create_facts {st : OsState} {Γb Γm Γf Γt} {V : Hist} {Γc : GMap Nat (Nat × Qp)}
    {k : Nat} {j : Ino} {b : GoString} {s0 : Nat} {q : Qp}
    (hwf : OsWf st) (hcoh : OsCoh st Γb Γm Γf Γt) (hw : FsTreeWf st) (hc : TreeCoh st V ∅ Γc)
    (hk : Γc !! k = some (s0, q)) (hΓc : GMap.delete k Γc = ∅)
    (hj : Reach st.fs.roots st.tree j) (hb : NameOk b) (he : st.tree.entry j b = none) :
    let n := st.fs.nextIno
    st.file n = none ∧ Γm !! n = none ∧
    OsWf (createdSt st k j b s0) ∧ OsCoh (createdSt st k j b s0) Γb (<[n := newMeta]> Γm) Γf Γt ∧
    cellView (createdSt st k j b s0) = cellView st ∧
    (∀ q, (createdSt st k j b s0).size q = st.size q) ∧
    FsTreeWf (createdSt st k j b s0) ∧
    TreeCoh (createdSt st k j b s0) (V.push ⟨.create j b n, s0⟩) ∅ ∅ ∧
    (createdSt st k j b s0).file n = some newFile ∧ (createdSt st k j b s0).proc.dfds = ∅ := by
  intro n
  have hnn' : n = st.fs.nextIno := rfl
  have hdf0 : st.proc.dfds = ∅ := dfds_empty hc
  have hnf : st.fs.files !! n = none := by
    cases h0 : st.fs.files !! n with
    | none => rfl
    | some f =>
      exact absurd (hw.files_lt n (by rw [GMap.mem_iff, h0]; rfl)) (Nat.lt_irrefl _)
  have hfn : st.file n = none := hnf
  have hs0 := filesSame_metaEnd st k
  have hfn0 : (st.metaEnd k).file n = none := hfn
  have hwf0 := osWf_filesSame hs0 hwf
  have hcoh0 := osCoh_filesSame hs0 hcoh
  have hsA := filesSame_created st k j b s0
  have hΓm : Γm !! n = none := (hcoh.meta_dom n).2 hnf
  -- the tree
  have hnn : ¬ Named st.tree n := by
    intro hnm
    have := (hw.hist st.fs.metaLog.length (Nat.le_refl _)).2.1
    rw [List.take_length] at this
    obtain ⟨f, hf⟩ := this n hnm
    rw [hnf] at hf; cases hf
  have hjm : j ∈ st.tree := (treeWf_now hw).1 j hj
  have htw := treeWf_create (treeWf_now hw) hj hb he hnn
  have hfilesC : ∀ i, (createdSt st k j b s0).fs.files !! i =
      if n = i then some newFile else st.fs.files !! i := fun i => files_setFile _ _ _ _
  have hwC : FsTreeWf (createdSt st k j b s0) := by
    refine fsTreeWf_meta hw rfl rfl rfl (fun i f hf => ?_) (Nat.le_succ _) htw (fun i hi => ?_)
      (fun j' hj' => ?_) (fun fd df h => ?_) (fun fd h => ?_) (fun i hi => ?_)
    · rw [hfilesC]; split
      · exact ⟨_, rfl⟩
      · exact ⟨f, hf⟩
    · rw [hfilesC]; split
      · exact ⟨_, rfl⟩
      · rename_i hni
        obtain ⟨j0, b0, hb0⟩ := hi
        simp only [MetaOp.apply] at hb0
        rw [entry_upd] at hb0
        split at hb0
        · rename_i hjj; subst hjj
          rw [GMap.lookup_insert_eq_iff] at hb0; split at hb0
          · cases hb0; exact absurd rfl hni
          · have := (hw.hist st.fs.metaLog.length (Nat.le_refl _)).2.1
            rw [List.take_length] at this
            exact this i ⟨_, b0, by unfold Tree.entry; rw [← getD_lookup]; exact hb0⟩
        · have := (hw.hist st.fs.metaLog.length (Nat.le_refl _)).2.1
          rw [List.take_length] at this
          exact this i ⟨j0, b0, hb0⟩
    · simp only [MetaOp.apply] at hj'
      rw [mem_upd] at hj'
      show j' < st.fs.nextIno + 1
      rcases hj' with rfl | hj'
      · have := (hw.hist st.fs.metaLog.length (Nat.le_refl _)).2.2 _ (by
          rw [List.take_length]; exact hjm)
        exact Nat.lt_succ_of_lt this
      · have := (hw.hist st.fs.metaLog.length (Nat.le_refl _)).2.2 j' (by
          rw [List.take_length]; exact hj')
        exact Nat.lt_succ_of_lt this
    · have h' : (GMap.fmap (·.note (.create j b n)) st.proc.dfds) !! fd = some df := h
      rw [hdf0, fmap_empty_dfds] at h'; simp at h'
    · show (GMap.fmap (·.note (.create j b n)) st.proc.dfds) !! fd = none
      rw [hdf0, fmap_empty_dfds]; simp
    · show i < st.fs.nextIno + 1
      have hi' : (<[n := newFile]> st.fs.files) !! i ≠ none := by
        have hi2 : i ∈ (<[n := newFile]> st.fs.files) := hi
        rw [GMap.mem_iff] at hi2; intro h0; rw [h0] at hi2; cases hi2
      rw [GMap.lookup_insert_eq_iff] at hi'; split at hi'
      · rename_i hni; subst hni; exact Nat.lt_succ_self _
      · have := hw.files_lt i (by rw [GMap.mem_iff]; cases h0 : st.fs.files !! i with
          | none => exact absurd h0 hi'
          | some _ => rfl)
        exact Nat.lt_succ_of_lt this
  have hdfC : (createdSt st k j b s0).proc.dfds = ∅ := by
    show GMap.fmap (·.note (.create j b n)) st.proc.dfds = ∅
    rw [hdf0, fmap_empty_dfds]
  have hcC : TreeCoh (createdSt st k j b s0) (V.push ⟨.create j b n, s0⟩) ∅ ∅ :=
    treeCoh_meta hc rfl hk hΓc rfl rfl hdfC rfl
  have hszA := sizes_create (st := st.metaEnd k) hfn0
  refine ⟨hfn, hΓm, osWf_filesSame hsA (osWf_create hwf0 hfn0),
    osCoh_filesSame hsA (osCoh_create hwf0 hcoh0 hfn0), ?_, fun q => hszA q, hwC, hcC,
    file_setFile_eq _ _ _, hdfC⟩
  rw [cellView_filesSame hsA (osWf_create hwf0 hfn0), cellView_create hwf0 hfn0]
  exact cellView_filesSame hs0 hwf

/-- **`open(2)` with `O_RDWR | O_CREAT` of a new name `b` of the directory `d`** (of inode `j`), a call
`k` whose fraction with the caller's is the whole history: on success a new file of a fresh inode
`i`, its `create` logged, its `OsMeta` whole and an fd on it; on failure the file may have been
created. Either way the roots are well formed (`RootsOk`, which a retry needs to find the file). -/
theorem wp_osOpenCreate (d b : GoString) (R : Roots) (V : Hist) (q1 q : Qp) (k s0 : Nat) (j : Ino)
    (hb : NameOk b) (hd : lookupH R V d = some (.dir j)) (hn : lookupH R V (child d b) = none)
    (hq : q1 + q = 1) (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osTree (L := L) (DFrac.own q1) R V -∗ osCall (L := L) k s0 q -∗
      (∀ fd : w64, ∀ e : w64, ⌜RootsOk R⌝ -∗
        ((⌜e = 0 ∧ 0 ≤ fd.toInt⌝ ∗ ∃ i, osTree (L := L) (DFrac.own 1) R (V.push ⟨.create j b i, V.2.length⟩) ∗
            osMeta (L := L) i (DFrac.own 1) newMeta ∗ osFd (L := L) fd (DFrac.own 1) ⟨i, true, true⟩) ∨
         (⌜e ≠ 0 ∧ fd = -1⌝ ∗ (osTree (L := L) (DFrac.own 1) R V ∨ ∃ i,
            osTree (L := L) (DFrac.own 1) R (V.push ⟨.create j b i, V.2.length⟩) ∗
            osMeta (L := L) i (DFrac.own 1) newMeta))) -∗
        Φ (PairV (#fd) (#e))) -∗
      WP (ExternalOp fsExt.name "Open" (Val (PairV (osTokV k) (PairV (#(child d b)) (#flCreat)))))
        @ s; E {{ Φ }} := by
  iintro #Hinv Hh Hk HΦ
  iapply wp_fs_stepT "Open" _ Φ (by simp [val.isPanic]) hE _ (legacyWit_call _ _ _) $$ Hinv Hk
  iintro Hk %st %Γb %Γm %Γf %Γt %V0 %Γdf %Γc %h Hw Hn
  unfold treeWorld
  icases Hn with ⟨%Hns, HAd, HAdf, HAc, Hrd, Hcr⟩
  obtain ⟨hw, hc⟩ := Hns
  icases osTree_auth _ _ _ _ _ $$ HAd Hh with %Heq
  obtain ⟨rfl, rfl⟩ := Heq
  icases osCall_auth Γc k s0 q $$ HAc Hk with %hk
  have hcall : st.proc.calls !! k = some s0 := by rw [← hc.calls k, hk]; rfl
  have hs0 : s0 = st.fs.metaLog.length := hc.start k _ hk
  have hV := hc.hist
  subst hV
  have hl : st.lookup d = some (.dir j) := hd
  have hn' : st.lookup (child d b) = none := hn
  have hpar : st.parent (child d b) = some (j, b) := parent_child hl hb
  have hent : st.tree.entry j b = none := by rw [← lookup_child hw.roots hl hb]; exact hn'
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hcr : decide ((flCreat.toNat / O_CREAT) % 2 = 1) = true := by decide
  have htr : decide ((flCreat.toNat / O_TRUNC) % 2 = 1) = false := by decide
  have hacc : flCreat.toNat % 4 = 2 := by decide
  imodintro
  isplitr
  · ipureintro
    obtain ⟨hfr, hr⟩ := step_filesSame (h := h) hwf (filesSame_metaEnd st k) Hag
    exact ⟨_, h, _, .inl ⟨child d b, flCreat, k, s0, rfl, .inr (treeName_child hl hb), flCreat_ok, hcall,
      ⟨fun h => (Bool.false_ne_true (htr.symm.trans h)).elim, .inr ⟨1, by decide, fun h => absurd h (by decide), rfl, .inl rfl⟩⟩⟩, hfr, hr⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsFsStep] at Hst
  replace Hst := open_inTree Hst (.inr (treeName_child hl hb))
  obtain ⟨p', fl', k', s', hv, -, -, hk', hres⟩ := Hst
  injection hv with hv1 hv2
  have hkk : k' = k := by injection hv1 with h1; exact (extVal_inj h1).symm
  subst hkk
  injection hv2 with hv3 hv4
  cases go.intoVal_inj hv3; cases go.intoVal_inj hv4
  rw [hcall] at hk'; cases hk'
  simp only [hcr, htr, hacc] at hres
  -- the whole history, and what it tells
  imod call_end _ _ Γc k' s0 q $$ HAd HAc Hcr Hk with ⟨%hk2, HAd, HAc, Hcr, Hq⟩
  ihave Hh : osTree (L := L) (DFrac.own 1) st.fs.roots (st.fs.treeDur, st.fs.metaLog) $$ [Hh Hq]
  · rw [← hq]; iapply (osTree_split q1 q _ _).2; iframe
  icases whole_alone _ _ Γdf (GMap.delete k' Γc) $$ Hh Hrd Hcr with ⟨%Hal, Hh, Hrd, Hcr⟩
  obtain ⟨hΓdf, hΓc⟩ := Hal
  subst hΓdf
  rw [hΓc]
  have hj := reach_of_lookup hl
  obtain ⟨hfn, hΓm, hwfC, hcohC, hcvC, hszC, hwC, hcC, hfC, hdfC⟩ :=
    create_facts hwf hcoh hw hc hk hΓc hj hb hent (s0 := s0) (k := k')
  -- an effect is the creation of `b` under `nextIno`
  have heffect : ∀ st1 tgt, OpenEffect (st.metaEnd k') (child d b) 2 true false s0 st1 tgt →
      st1 = createdSt st k' j b s0 ∧ tgt = .file st.fs.nextIno := by
    intro st1 tgt heff
    unfold OpenEffect at heff
    rw [show (st.metaEnd k').lookup (child d b) = none from hn'] at heff
    obtain ⟨-, j', b', hp', rfl, rfl⟩ := heff
    have : (j', b') = (j, b) := by
      have h2 : (st.metaEnd k').parent (child d b) = some (j, b) := hpar
      rw [hp'] at h2; cases h2; rfl
    cases this
    exact ⟨rfl, rfl⟩
  have hl1 : st.fs.metaLog.length = (st.fs.treeDur, st.fs.metaLog).2.length := rfl
  -- the ghost state of a creation
  have hghost : ⊢ gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γm Γm -∗
        gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γd
          (histMap (st.fs.roots, (st.fs.treeDur, st.fs.metaLog))) -∗
        osTree (L := L) (DFrac.own 1) st.fs.roots (st.fs.treeDur, st.fs.metaLog) ==∗
      gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γm (<[st.fs.nextIno := newMeta]> Γm) ∗
        gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γd
          (histMap (st.fs.roots, Hist.push (st.fs.treeDur, st.fs.metaLog)
            ⟨.create j b st.fs.nextIno, s0⟩)) ∗
        osTree (L := L) (DFrac.own 1) st.fs.roots
          (Hist.push (st.fs.treeDur, st.fs.metaLog) ⟨.create j b st.fs.nextIno, s0⟩) ∗
        osMeta (L := L) st.fs.nextIno (DFrac.own 1) newMeta := by
    iintro HAm HAd Hh
    imod gAuth_insert _ _ _ st.fs.nextIno newMeta hΓm $$ HAm with ⟨HAm, Hm⟩
    imod osTree_update _ _ (Hist.push (st.fs.treeDur, st.fs.metaLog) ⟨.create j b st.fs.nextIno, s0⟩)
      _ _ $$ HAd Hh with ⟨HAd, Hh⟩
    imodintro
    unfold osMeta
    iframe
  -- the files' world of the created state, from the old one's parts
  obtain ⟨-, hres⟩ := hres
  rcases hres with ⟨st1, tgt, fd, heff, hfree, hst, rfl⟩ | ⟨e, he, -, rfl, hst | ⟨tgt, heff⟩⟩
  · -- success
    obtain ⟨rfl, rfl⟩ := heffect st1 tgt heff
    obtain ⟨hfd0, hfdn, hdfn, -⟩ := hfree
    have hst'' : st' = (createdSt st k' j b s0).setProc { (createdSt st k' j b s0).proc with
        fds := <[fd := ⟨st.fs.nextIno, true, true⟩]> (createdSt st k' j b s0).proc.fds } := by
      rw [hst]; simp [O_WRONLY, O_RDONLY]
    subst hst''
    imod hghost $$ HAm HAd Hh with ⟨HAm, HAd, Hh, Hm⟩
    ihave Hwc : osWorld (L := L) (createdSt st k' j b s0) Γb (<[st.fs.nextIno := newMeta]> Γm) Γf Γt h
      $$ [HAb HAm HAf HAt Htok Hcells Hσ]
    · unfold osWorld; rw [hcvC]; iframe; ipureintro; exact ⟨hwfC, hcohC⟩
    imod osWorld_addFd (st := createdSt st k' j b s0) (filesSame_refl _) (fd := fd)
      (d := ⟨st.fs.nextIno, true, true⟩) hfdn hfd0 ⟨_, hfC⟩ Hr Hfr $$ Hwc with ⟨Hwc, Hfd⟩
    have hw' : FsTreeWf ((createdSt st k' j b s0).setProc { (createdSt st k' j b s0).proc with
        fds := <[fd := ⟨st.fs.nextIno, true, true⟩]> (createdSt st k' j b s0).proc.fds }) := by
      refine ⟨hwC.roots, hwC.hist, hwC.dfds, fun fd' _ => ?_, hwC.files_lt⟩
      show (createdSt st k' j b s0).proc.dfds !! fd' = none
      rw [hdfC]; simp
    have hc' := hcC.congr (st' := (createdSt st k' j b s0).setProc { (createdSt st k' j b s0).proc with
        fds := <[fd := ⟨st.fs.nextIno, true, true⟩]> (createdSt st k' j b s0).proc.fds }) rfl rfl rfl rfl
    ihave Hn := treeWorld_mk (st := st) (by rfl) hw' hc' $$ HAd HAdf HAc Hrd Hcr
    imodintro
    iexists Γb, _, _, Γt, _, ∅, ∅
    try unfold osWorld
    try unfold treeWorld
    try unfold rdRes
    try unfold osFd
    isplitl [Hwc]
    · iexact Hwc
    isplitl [Hn]
    · iexact Hn
    iapply wp_value'
    iapply HΦ $$ %fd %0 %hw.roots
    ileft
    isplitr
    · ipureintro; exact ⟨rfl, hfd0⟩
    iexists st.fs.nextIno
    rw [← hs0]
    iframe
  · -- failure, no effect
    subst hst
    have hc0 : TreeCoh (st.metaEnd k') (st.fs.treeDur, st.fs.metaLog) ∅ ∅ := by
      have := treeCoh_metaEnd hc k'; rwa [hΓc] at this
    imod worlds_close (filesSame_metaEnd st k') Hr Hfr rfl (fsTreeWf_metaEnd hw k')
      hc0 $$ [HAb HAm HAf HAt Htok Hcells Hσ] HAd HAdf HAc Hrd Hcr with ⟨Hw, Hn⟩
    · (try unfold osWorld); iframe; ipureintro; exact ⟨hwf, hcoh⟩
    imodintro
    iexists Γb, Γm, Γf, Γt, _, _, _
    try unfold osWorld
    try unfold treeWorld
    try unfold rdRes
    try unfold osFd
    isplitl [Hw]
    · iexact Hw
    isplitl [Hn]
    · iexact Hn
    iapply wp_value'
    iapply HΦ $$ %(-1) %e %hw.roots
    iright
    isplitr
    · ipureintro; exact ⟨he, rfl⟩
    ileft; iexact Hh
  · -- failure, created
    obtain ⟨rfl, -⟩ := heffect st' tgt heff
    imod hghost $$ HAm HAd Hh with ⟨HAm, HAd, Hh, Hm⟩
    imod cells_same hwf hwfC Hr Hfr rfl hcvC $$ [Hσ Hcells] with ⟨Hσ, Hcells⟩
    · iframe
    ihave Hn := treeWorld_mk (st := st) (by rfl) hwC hcC $$ HAd HAdf HAc Hrd Hcr
    ihave Hwc : osWorld (L := L) (createdSt st k' j b s0) Γb (<[st.fs.nextIno := newMeta]> Γm) Γf Γt h'
      $$ [HAb HAm HAf HAt Htok Hcells Hσ]
    · (try unfold osWorld); iframe; ipureintro; exact ⟨hwfC, hcohC⟩
    imodintro
    iexists Γb, _, Γf, Γt, _, ∅, ∅
    try unfold osWorld
    try unfold treeWorld
    try unfold rdRes
    try unfold osFd
    isplitl [Hwc]
    · iexact Hwc
    isplitl [Hn]
    · iexact Hn
    iapply wp_value'
    iapply HΦ $$ %(-1) %e %hw.roots
    iright
    isplitr
    · ipureintro; exact ⟨he, rfl⟩
    iright
    iexists st.fs.nextIno
    rw [← hs0]
    iframe

end specs

end Fs
end Perennial

end
