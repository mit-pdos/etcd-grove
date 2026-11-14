/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/client/pkg/v3/fileutil/TouchDirAllDir.lean`
(`fileutil.TouchDirAll.specDir`: `TouchDirAll` of a name already holding a directory of files), as
`fileutil.TouchDirAll.wp_proof` (`TouchDirAll.lean`) but `Exist(d)` answering either way, over
`CheckDirPermission`'s spec, `os.MkdirAll.specDirS` and the probe on what `.touch` holds
(`wp_isDirWriteableAny`: `IsDirWriteable.spec` or `specFile`). Lean-first (`wal-leaf5`).
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.TouchDirAllDir
public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.CheckDirPermission
public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.IsDirWriteableFile
public import LinuxFs.Proof.os.MkdirAllDir
public import LinuxFs.Spec.go_uber_org.zap.Error
public import LinuxFs.Spec.go_uber_org.zap.Logger__Warn
public import LinuxFs.Proof.go_etcd_io.etcd.client.pkg.v3.fileutil.TouchDirAll

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Fs WalFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]
variable [os_sem : os.Assumptions] [os.file.FieldAssumptions] [os.fileStat.FieldAssumptions]

/-- **A spine to `d/b` borrowed** from fractions of the spine to `d` and of the claim on `b` (holding
the directory `J`), with what gives them back. -/
theorem osPathS_child_borrow (R : Roots) (d b : GoString) (j J : Ino) (qd qn : Qp) (h : NamesH)
    (hb : NameOk b) (hJ : h.cur !! b = some (.dir J)) :
    osPathS (GF := GF) R d (DFrac.own qd) j ∗ osNames j (.only [b]) (DFrac.own qn) h ⊢
      ∃ ε : Qp, osPathS R (child d b) (DFrac.own ε) J ∗
        (osPathS R (child d b) (DFrac.own ε) J -∗
          osPathS R d (DFrac.own qd) j ∗ osNames j (.only [b]) (DFrac.own qn) h) := by
  iintro ⟨Hp, Hn⟩
  obtain ⟨ε, a', b', hqd, hqq⟩ := os.qp_common qd qn
  subst hqd hqq
  icases (osPathS_frac R d ε a' j).1 $$ Hp with ⟨Hpe, Hpa⟩
  icases (osNames_frac j (.only [b]) ε b' h).1 $$ Hn with ⟨Hne, Hnb⟩
  ihave Hpc := osPathS_child R d b (DFrac.own ε) j J h hb hJ $$ Hpe Hne
  iexists ε
  iframe Hpc
  iintro Hpc
  icases os.osPathS_unchild R d b j J ε a' hb $$ [Hpc Hpa] with ⟨%h'', Hp, Hne, %-⟩
  · iframe
  icases osNames_agree j (.only [b]) _ _ h'' h $$ Hne Hnb with %he
  subst he
  iframe Hp
  iapply (osNames_frac j (.only [b]) ε b' h'').2
  iframe

/-- `os.Stat(d/b)` of the directory `J` at `b`, its result dropped (the form `Exist.spec` takes). -/
theorem wp_statChildDir_err (d b : GoString) (R : Roots) (j J : Ino) (qd qn : Qp) (h : NamesH)
    (qc : Qp) (hb : NameOk b) (hJ : h.cur !! b = some (.dir J)) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d (DFrac.own qd) j ∗
        osNames j (.only [b]) (DFrac.own qn) h ∗ osCallPerm qc }}
      (App (Val (@! os.Stat)) (Val #(child d b)))
    {{ (fi : GoInterface) (err : GoInterface), RET (PairV #fi #err); osPathS R d (DFrac.own qd) j ∗
        osNames j (.only [b]) (DFrac.own qn) h ∗ osCallPerm qc }} := by
  iintro %Φ Hpre HΦ
  wp_apply os.Stat.wp_childDirS d b R j J qd qn h qc hb hJ $$ Hpre as %fi %err ⟨Hp, Hn, Hperm, -⟩
  iapply HΦ
  iframe

/-- **The probe on whatever `.touch` holds** (nothing: `IsDirWriteable.spec`; a leftover file, held
whole: `specFile`): nothing or a file at `.touch` after, the file whole, nothing on success. -/
theorem wp_isDirWriteableAny
    (wpA : go_etcd_io.etcd.client.pkg.v3.fileutil.IsDirWriteable.spec (GF := GF) (hG := hG))
    (wpF : go_etcd_io.etcd.client.pkg.v3.fileutil.IsDirWriteable.specFile (GF := GF) (hG := hG))
    (dir : GoString) (R : Roots) (J : Ino) (dq : DFrac) (hT : NamesH) (qc : Qp)
    (hlen : dir.length < 2 ^ 60) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.fileutil ∗ osInv (GF := GF) ∗
        osSharedInv R ∗ osPathS R dir dq J ∗ osCallPerm qc ∗
        osNames J (.only [go!".touch"]) (DFrac.own 1) hT ∗ tmpEnt (hT.cur !! go!".touch") }}
      (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.IsDirWriteable)) (Val #dir))
    {{ (err : GoInterface), RET #err; osPathS R dir dq J ∗ osCallPerm qc ∗
        ∃ hT', osNames J (.only [go!".touch"]) (DFrac.own 1) hT' ∗
          (⌜hT'.cur !! go!".touch" = none⌝ ∨
            ∃ i, ⌜hT'.cur !! go!".touch" = some (.file i)⌝ ∗ trFile i False) ∗
          ⌜err = interface.nil → hT'.cur !! go!".touch" = none⌝ }} := by
  iintro %Φ ⟨#Hpkg, #Hinv, #Hsi, Hp, Hperm, Hn, HT⟩ HΦ
  rcases hc : hT.cur !! go!".touch" with _ | ⟨i | J'⟩
  · wp_apply wpA dir R J dq hT qc hlen hc $$ [Hp Hperm Hn] as %err H
    · iframe; iframe #
    iapply HΦ $$ H
  · iunfold tmpEnt at HT
    wp_apply wpF dir R J i dq hT qc hlen hc $$ [Hp Hperm Hn HT]
      as %err ⟨Hp, Hperm, %hT', Hn, Hd, %hok⟩
    · iframe; iframe #
    iapply HΦ
    iframe Hp Hperm
    iexists hT'
    iframe Hn
    isplitl [Hd]
    · icases Hd with (%h0 | ⟨%h1, Ht⟩)
      · ileft; ipureintro; exact h0
      · iright; iexists i; iframe; ipureintro; exact h1
    ipureintro; exact hok
  · iunfold tmpEnt at HT
    icases HT with %hf
    exact hf.elim

/-- **`TouchDirAll`'s probe of an existing directory** (`J` at `name`, files only, its claims whole with
`.touch`'s file): `specDir`'s post. -/
theorem wp_touchProbe
    (wpA : go_etcd_io.etcd.client.pkg.v3.fileutil.IsDirWriteable.spec (GF := GF) (hG := hG))
    (wpF : go_etcd_io.etcd.client.pkg.v3.fileutil.IsDirWriteable.specFile (GF := GF) (hG := hG))
    (R : Roots) (parent name : GoString) (jp J : Ino) (qp : Qp) (h hJ : NamesH) (hname : NameOk name)
    (hlen : (child parent name).length < 2 ^ 60) (hcur : h.cur !! name = some (.dir J))
    (hfo : FilesOnly hJ.cur) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.fileutil ∗ osInv (GF := GF) ∗
        osSharedInv R ∗ osPathS R parent (DFrac.own qp) jp ∗ osCallPerm 1 ∗
        osNames jp (.only [name]) (DFrac.own 1) h ∗ osNames J (.except []) (DFrac.own 1) hJ ∗
        tmpEnt (hJ.cur !! go!".touch") }}
      (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.IsDirWriteable)) (Val #(child parent name)))
    {{ (err : GoInterface), RET #err; osPathS R parent (DFrac.own qp) jp ∗ osCallPerm 1 ∗
        ((⌜err ≠ interface.nil⌝ ∗ ∃ h', tmpDirH jp name h') ∨
          (⌜err = interface.nil⌝ ∗ ∃ hJ' : NamesH,
            ⌜FilesOnly hJ'.cur ∧ hJ'.cur !! go!".touch" = none⌝ ∗
            osNames jp (.only [name]) (DFrac.own 1) h ∗ osNames J (.except []) (DFrac.own 1) hJ')) }} := by
  iintro %Φ ⟨#Hpkg, #Hinv, #Hsi, Hp, Hperm, Hn, HJ, HT⟩ HΦ
  icases osPathS_child_borrow R parent name jp J qp 1 h hname hcur $$ [Hp Hn] with ⟨%ε, Hpc, Hback⟩
  · iframe
  imod osNames_split R J (.except []) [go!".touch"] hJ CoPset.subseteq_top $$ Hsi HJ with ⟨Ht, Hrest⟩
  rw [show (NameSet.except []).inter [go!".touch"] = .only [go!".touch"] by simp [NameSet.inter],
    show (NameSet.except []).diff [go!".touch"] = .except [go!".touch"] by simp [NameSet.diff]]
  have hTt : (hJ.restrict J (.only [go!".touch"])).cur !! go!".touch" = hJ.cur !! go!".touch" := by
    simp only [NamesH.restrict]; rw [restrictN_lookup _ _ _ (by simp [NameSet.Mem])]
  rw [← hTt]
  iapply wp_fupd
  wp_apply wp_isDirWriteableAny wpA wpF (child parent name) R J (DFrac.own ε) _ 1 hlen
    $$ [Hpc Hperm Ht HT] as %err ⟨Hpc, Hperm, %hT, HT, Hd, %hTn⟩
  · iframe; iframe #
  icases Hback $$ Hpc with ⟨Hp, Hn⟩
  icases touchOut_tmpEnt _ $$ Hd with ⟨%hTd, Hd⟩
  imod osNames_merge R J (.only [go!".touch"]) (.except [go!".touch"]) (.except []) hT _
    (by intro b; simp only [NameSet.Mem]; by_cases hb : b = go!".touch" <;> simp [hb])
    CoPset.subseteq_top $$ Hsi HT Hrest with ⟨%hM, HM, %hMf⟩
  have hMc := fun c => merged_cur hM hT _ J go!".touch" c hMf.1 hMf.2.1
  have hRc : ∀ c, c ≠ go!".touch" →
      (hJ.restrict J (.except [go!".touch"])).cur !! c = hJ.cur !! c := by
    intro c hc; simp only [NamesH.restrict]; rw [restrictN_lookup _ _ _ (by simp [NameSet.Mem, hc])]
  have hnoM : ∀ (c : GoString) J', hM.cur !! c ≠ some (.dir J') := by
    intro c J' hc
    rw [hMc c] at hc
    split at hc
    · subst_vars; exact hTd J' hc
    · rename_i hne
      rw [hRc c hne] at hc
      obtain ⟨i, hi⟩ := hfo c _ hc
      cases hi
  imodintro
  iapply HΦ
  iframe Hp Hperm
  cases err with
  | ok e =>
    ileft
    isplitr
    · ipureintro; intro hc; cases hc
    iexists h
    iapply tmpDirH_dir jp name h J hM hcur hnoM $$ [Hn HM Hd]
    iframe Hn HM
    rw [hMc go!".touch", if_pos rfl]
    iexact Hd
  | nil =>
    iclear Hd
    iright
    isplitr
    · ipureintro; rfl
    iexists hM
    iframe Hn HM
    ipureintro
    refine ⟨fun c n hc => ?_, ?_⟩
    · cases n with
      | file i => exact ⟨i, rfl⟩
      | dir J' => exact absurd hc (hnoM c J')
    · rw [hMc, if_pos rfl]; exact hTn rfl

/-- `Exist` of the path of the first `k` components of `full = rcs ++ cs ++ [name]` (`/rcs` a root,
`cs` the spine's, `name` holding the directory `J`): some answer, nothing changed. -/
theorem wp_existAncDir (wp_Exist : go_etcd_io.etcd.client.pkg.v3.fileutil.Exist.spec (GF := GF) (hG := hG))
    (hStatAbove : os.Stat.specAboveRoot (GF := GF) (hG := hG))
    (R : Roots) (rcs cs : List GoString) (name : GoString) (full : List GoString) (j0 jp J : Ino)
    (qp : Qp) (h : NamesH) (k : Nat) (hfull : full = (rcs ++ cs) ++ [name]) (hR : RootsOk R)
    (hm : (joinPath [] rcs, j0) ∈ R) (hrcs : rcs ≠ []) (hcs : ∀ c ∈ cs, NameOk c) (hname : NameOk name)
    (hcur : h.cur !! name = some (.dir J)) (hk : k ≤ full.length) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osSpine j0 cs (DFrac.own qp) jp ∗
        osNames jp (.only [name]) (DFrac.own 1) h ∗ osCallPerm 1 }}
      (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.Exist)) (Val #(os.ancPath (full.take k))))
    {{ (b : Bool), RET #b; osSpine j0 cs (DFrac.own qp) jp ∗ osNames jp (.only [name]) (DFrac.own 1) h ∗
        osCallPerm 1 }} := by
  iintro %Φ ⟨#Hinv, #Hsi, Hs, Hn, Hperm⟩ HΦ
  by_cases hkn : k = full.length
  · subst hkn
    have hdir : os.ancPath (full.take full.length) = child (joinPath (joinPath [] rcs) cs) name := by
      rw [List.take_length, ancPath_ne (by subst hfull; simp), hfull, joinPath_snoc, joinPath_joinPath]
    rw [hdir]
    ihave Hp := (os.osPathS_joinPath R (joinPath [] rcs) j0 cs (DFrac.own qp) jp hR hm hcs).2 $$ Hs
    wp_apply wp_Exist (child (joinPath (joinPath [] rcs) cs) name) _ _
      (wp_statChildDir_err _ name R jp J qp 1 h 1 hname hcur) $$ [Hp Hn Hperm]
      as %b ⟨%err, %hb, Hp, Hn, Hperm⟩
    · iframe; isplitl [] <;> iassumption
    ihave Hs := (os.osPathS_joinPath R (joinPath [] rcs) j0 cs (DFrac.own qp) jp hR hm hcs).1 $$ Hp
    iapply HΦ
    iframe
  · have hk' : k ≤ (rcs ++ cs).length := by subst hfull; simp at hk hkn ⊢; omega
    rw [show full.take k = (rcs ++ cs).take k by subst hfull; rw [List.take_append_of_le_length hk']]
    wp_apply wp_Exist _ _ _ (wp_statAnc hStatAbove R rcs cs j0 jp (DFrac.own qp) 1 k hR hm hrcs hcs hk')
      $$ [Hs Hperm] as %b ⟨%err, %hb, Hs, Hperm⟩
    · iframe; isplitl [] <;> iassumption
    iapply HΦ
    iframe

/-- `filepath.Dir` of `d/b`: `d`. -/
theorem dir_child_parent {d b : GoString} (hd : filepath.CleanAbs d) (hb : NameOk b) :
    path.dirModel (child d b) = d := by
  have h := filepath.dirModel_name d b hd (cleanSeg_of_nameOk hb)
  have e : d ++ [path.slash] ++ b = child d b := by simp [child]; rfl
  rw [e] at h
  exact h

/-- A directory of files with its claims and `.touch`'s file: `tmpDirH` of the name holding it. -/
theorem tmpDirH_of (j : Ino) (b : GoString) (h : NamesH) (J : Ino) (hJ : NamesH)
    (hb : h.cur !! b = some (.dir J)) (hfo : FilesOnly hJ.cur) :
    osNames (GF := GF) j (.only [b]) (DFrac.own 1) h ∗ osNames J (.except []) (DFrac.own 1) hJ ∗
      tmpEnt (hJ.cur !! go!".touch") ⊢ tmpDirH j b h :=
  tmpDirH_dir j b h J hJ hb (fun c J' hc => by obtain ⟨i, hi⟩ := hfo c _ hc; cases hi)

theorem fileutil.TouchDirAll.wp_proofDir
    (wp_Exist : go_etcd_io.etcd.client.pkg.v3.fileutil.Exist.spec (GF := GF) (hG := hG))
    (wp_Clean : filepath.Clean.spec (GF := GF) (hG := hG))
    (wp_Dir : filepath.Dir.spec (GF := GF) (hG := hG))
    (wp_MkdirAll : os.MkdirAll.specDirS (GF := GF) (hG := hG))
    (wpA : go_etcd_io.etcd.client.pkg.v3.fileutil.IsDirWriteable.spec (GF := GF) (hG := hG))
    (wpF : go_etcd_io.etcd.client.pkg.v3.fileutil.IsDirWriteable.specFile (GF := GF) (hG := hG))
    (hSync : go_etcd_io.etcd.client.pkg.v3.fileutil.syncDir.spec (GF := GF) (hG := hG))
    (hSyncAbove : go_etcd_io.etcd.client.pkg.v3.fileutil.syncDir.specAboveRoot (GF := GF) (hG := hG))
    (hStatAbove : os.Stat.specAboveRoot (GF := GF) (hG := hG))
    (wp_Check : go_etcd_io.etcd.client.pkg.v3.fileutil.CheckDirPermission.spec (GF := GF) (hG := hG))
    (wp_Error : zap.Error.spec (GF := GF) (hG := hG))
    (wp_Warn : zap.Logger.Warn.spec (GF := GF) (hG := hG)) :
    fileutil.TouchDirAll.specDir (GF := GF) := by
  intro lg R jp d parent name qp h J hd hname hlen hcur
  wp_start as ⟨#Hlg, #Hinv, #Hsi, Hp, Hperm, Ht⟩
  iunfold tmpDirH at Ht
  icases Ht with ⟨Hn, Hs⟩
  rw [hcur]
  iunfold tmpSub at Hs
  icases Hs with ⟨%hJ, %hfo, HJ, HT⟩
  wp_auto
  ihave %hlgnn := zapLoggerOk_ne_null lg $$ Hlg
  simp only [hlgnn, decide_false, Bool.not_false]
  wp_apply wp_verifyAssert_true as -
  subst hd
  icases osPathS_cleanAbs_keep R parent _ jp $$ Hp with ⟨Hp, %hclean⟩
  imod osLogLb_0 with #Hlb
  wp_apply wp_Exist (child parent name) _ _ (wp_statChildDir_err parent name R jp J qp 1 h 1 hname hcur)
    $$ [Hp Hn Hperm] as %b ⟨%err, %hb, Hp, Hn, Hperm⟩
  · iframe; isplitl [] <;> iassumption
  subst hb
  by_cases he : err = GoInterface.nil
  · -- `Exist` found it: `CheckDirPermission` (logged), `syncDir(parent)`, the probe
    rw [decide_eq_true he]
    wp_auto
    icases osPathS_child_borrow R parent name jp J qp 1 h hname hcur $$ [Hp Hn] with ⟨%ε, Hpc, Hback⟩
    · iframe
    wp_apply wp_Check (child parent name) _ R J (DFrac.own ε) 1 $$ [Hpc Hperm] as %e ⟨Hpc, Hperm⟩
    · iframe; iframe #
    icases Hback $$ Hpc with ⟨Hp, Hn⟩
    rcases e with _ | ie <;> wp_auto
    -- the error logged (the first goal: `ok`)
    wp_apply wp_Error as %f1 -
    wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1]
    isplitr
    · ipureintro; rfl
    iintro %fsl ⟨-, -⟩
    try wp_auto
    wp_apply wp_Warn lg _ _ $$ []
    · iframe #
    try wp_auto
    all_goals
      wp_apply wp_Clean (child parent name)
      iintro %cl %hcl
      rw [abs_child hclean hname] at hcl
      subst hcl
      try wp_auto
      wp_apply wp_Dir (child parent name)
      iintro %dr %hdr
      rw [dir_child_parent hclean hname] at hdr
      subst dr
      try wp_auto
      wp_apply hSync parent R jp (DFrac.own qp) 1 0 $$ [Hp Hperm] as %e2 ⟨Hp, Hperm, -⟩
      · iframe; iframe #
      cases e2 with
      | ok ie2 =>
        wp_auto
        iapply HΦ
        iframe Hp Hperm
        ileft
        isplitr
        · ipureintro; intro hc; cases hc
        iexists h
        iapply tmpDirH_of jp name h J hJ hcur hfo $$ [Hn HJ HT]
        iframe
      | nil =>
        wp_auto
        wp_apply wp_touchProbe wpA wpF R parent name jp J qp h hJ hname hlen hcur hfo
          $$ [Hp Hperm Hn HJ HT] as %e3 H
        · iframe; iframe #
        try wp_auto
        iapply HΦ $$ H
  · -- `Exist` missed it (a `Stat` error): the climbing loop, `MkdirAll` (no effect), the syncs, the
    -- probe
    rw [decide_eq_false he]
    wp_auto
    wp_apply wp_Clean (child parent name)
    iintro %cl %hcl
    rw [abs_child hclean hname] at hcl
    subst hcl
    iunfold osPathS at Hp
    icases Hp with ⟨%r, %j0, %cs, %hpp, Hs⟩
    obtain ⟨hR, hm, hcs, hpar⟩ := hpp
    obtain ⟨rcs, hrcs, hrcsok, hr⟩ := (hR.2.2 _ hm).1
    subst hr hpar
    wp_auto
    obtain ⟨full, hfull⟩ : ∃ full, full = (rcs ++ cs) ++ [name] := ⟨_, rfl⟩
    have hfok : ∀ c ∈ full, NameOk c := by
      intro c hc
      subst hfull
      simp only [List.mem_append, List.mem_singleton] at hc
      rcases hc with (hc | hc) | rfl
      · exact hrcsok c hc
      · exact hcs c hc
      · exact hname
    have hflen : full.length = (rcs ++ cs).length + 1 := by subst hfull; simp; omega
    have hdir : os.ancPath (full.take full.length) = child (joinPath (joinPath [] rcs) cs) name := by
      rw [List.take_length, ancPath_ne (by subst hfull; simp), hfull, joinPath_snoc, joinPath_joinPath]
    ihave IH : iprop(∃ (k : Nat) (sl : GoSlice),
        "d" ∷ d_ptr ↦ os.ancPath (full.take k) ∗ "created" ∷ created_ptr ↦ sl ∗
        "Hsl" ∷ sl ↦* touchC full (k + 1) ∗ "Hs" ∷ osSpine j0 cs (DFrac.own qp) jp ∗
        "Hn" ∷ osNames jp (.only [name]) (DFrac.own 1) h ∗ "Hperm" ∷ osCallPerm 1 ∗
        "%hk" ∷ ⌜k ≤ full.length⌝) $$ [d created Hs Hn Hperm]
    · iexists full.length, slice.nil
      rw [hdir, touchC_end]
      iframe
      isplitl []
      · iapply ownSlice_nil
      ipureintro; exact Nat.le_refl _
    wp_join iprop(∃ (j : Nat) (sl : GoSlice), created_ptr ↦ sl ∗ sl ↦* touchC full j ∗
        osSpine j0 cs (DFrac.own qp) jp ∗ osNames jp (.only [name]) (DFrac.own 1) h ∗ osCallPerm 1 ∗
        ⌜j ≤ full.length + 1⌝)
      at (App (App (App (Val doFor) _) _) _) with [IH] as ⟨%j, %sl, created, Hsl, Hs, Hn, Hperm, %hj⟩
    · wp_for IH
      wp_apply wp_existAncDir wp_Exist hStatAbove R rcs cs name full j0 jp J qp h k hfull hR hm hrcs hcs
        hname hcur hk $$ [Hs Hn Hperm] as %b ⟨Hs, Hn, Hperm⟩
      · iframe; isplitl [] <;> iassumption
      cases b with
      | true =>
        simp only [Bool.not_true]
        rw [if_neg (by simp only [decide_eq_true_eq]; intro h; exact Bool.false_ne_true (go.intoVal_inj h)),
          if_pos (by simp)]
        isplitr
        · itrivial
        iexists k + 1, sl
        iframe
        ipureintro; omega
      | false =>
        simp only [Bool.not_false]
        rw [if_pos (by simp)]
        wp_auto
        wp_apply wp_slice_literal (V := GoString) [os.ancPath (full.take k)]
        isplitr
        · ipureintro; rfl
        iintro %jsl ⟨Hjsl, Hcap⟩
        wp_auto
        wp_apply wp_slice_append _ [os.ancPath (full.take k)] sl (touchC full (k + 1)) (DFrac.own 1)
          $$ [Hjsl Hcap Hsl] as %s' ⟨Hs', -, -⟩
        · iframe
        rw [List.singleton_append, ← touchC_cons full k hk]
        wp_apply wp_Dir (os.ancPath (full.take k))
        iintro %dr %hdr
        rw [dir_take full hfok k hk] at hdr
        subst hdr
        wp_auto
        by_cases hk0 : k = 0
        · subst hk0
          rw [decide_eq_true (by rfl)]
          wp_auto
          iapply wp_for_post_break
          isplitr
          · ipureintro; rfl
          iexists 0, s'
          iframe
          ipureintro; omega
        · rw [decide_eq_false (by rw [← dir_take full hfok k hk]; exact dir_take_ne full hfok k (by omega) hk)]
          wp_auto
          wp_for_post
          wp_apply wp_Dir (os.ancPath (full.take k))
          iintro %dr %hdr
          rw [dir_take full hfok k hk] at hdr
          subst hdr
          wp_auto
          iexists k - 1, s'
          rw [show k - 1 + 1 = k by omega]
          iframe
          ipureintro; omega
    ihave Hp := (os.osPathS_joinPath R (joinPath [] rcs) j0 cs (DFrac.own qp) jp hR hm hcs).2 $$ Hs
    wp_apply wp_MkdirAll (joinPath (joinPath [] rcs) cs) name (W32 448) R jp J qp 1 h 1 hname hcur
      $$ [Hp Hperm Hn] as %err ⟨Hp, Hperm, Hn⟩
    · iframe; isplitl [] <;> iassumption
    cases err with
    | ok e =>
      wp_auto
      iapply HΦ
      iframe Hp Hperm
      ileft
      isplitr
      · ipureintro; intro hc; cases hc
      iexists h
      iapply tmpDirH_of jp name h J hJ hcur hfo $$ [Hn HJ HT]
      iframe
    | nil =>
    ihave Hs := (os.osPathS_joinPath R (joinPath [] rcs) j0 cs (DFrac.own qp) jp hR hm hcs).1 $$ Hp
    ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
    have hCl := touchC_length full j
    wp_auto
    ihave IH : iprop(∃ (i : w64) (dv : GoString),
        "i" ∷ i_ptr ↦ i ∗ "d" ∷ d_ptr ↦ dv ∗ "err" ∷ err_ptr ↦ GoInterface.nil ∗
        "Hs" ∷ osSpine j0 cs (DFrac.own qp) jp ∗ "Hperm" ∷ osCallPerm 1 ∗
        "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.nat i ≤ (touchC full j).length⌝) $$ [i d err Hs Hperm]
    · iexists W64 0, _
      iframe
      ipureintro
      refine ⟨by decide, ?_⟩
      rw [show sint.nat (W64 0) = 0 from rfl]; omega
    wp_for IH
    obtain ⟨hi0, hil⟩ := Hi
    wp_if_destruct
    · have Hlt : sint.nat i < (touchC full j).length := by rw [Hlen.1]; word
      have Hbnd : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sl.len := ⟨hi0, Hif⟩
      simp only [Hbnd, _root_.and_self, ↓reduceIte]
      have He : (touchC full j)[(sint.Z i).toNat]? = some (os.ancPath (full.take (j + sint.nat i))) := by
        rw [show (sint.Z i).toNat = sint.nat i by word, List.getElem?_eq_getElem Hlt, touchC_get]
      have hji : j + sint.nat i ≤ full.length := by omega
      wp_apply wp_load_slice_index sl (sint.Z i) _ (DFrac.own 1) _ hi0 $$ [Hsl] as Hsl
      · iframe; ipureintro; exact He
      wp_apply wp_Dir (os.ancPath (full.take (j + sint.nat i)))
      iintro %dr %hdr
      rw [dir_take full hfok _ hji] at hdr
      subst hdr
      have hk' : j + sint.nat i - 1 ≤ (rcs ++ cs).length := by omega
      rw [show full.take (j + sint.nat i - 1) = (rcs ++ cs).take (j + sint.nat i - 1) by
        rw [hfull, List.take_append_of_le_length hk']]
      wp_apply wp_syncDirAnc hSync hSyncAbove R rcs cs j0 jp (DFrac.own qp) 1 0 (j + sint.nat i - 1)
        hR hm hrcs hcs hk' $$ [Hs Hperm] as %e ⟨Hs, Hperm, -⟩
      · iframe; isplitl [] <;> try iassumption
        isplitl [] <;> iassumption
      cases e with
      | ok e =>
        wp_auto
        wp_for_post
        iapply HΦ
        ihave Hp := (os.osPathS_joinPath R (joinPath [] rcs) j0 cs (DFrac.own qp) jp hR hm hcs).2 $$ Hs
        iframe Hp Hperm
        ileft
        isplitr
        · ipureintro; intro hc; cases hc
        iexists h
        iapply tmpDirH_of jp name h J hJ hcur hfo $$ [Hn HJ HT]
        iframe
      | nil =>
        wp_auto
        wp_for_post
        iframe
        iexists i + W64 1, _
        iframe
        have hi1 : sint.nat (i + W64 1) = sint.nat i + 1 := by word
        rw [hi1]
        ipureintro
        refine ⟨by word, by omega⟩
    · ihave Hp := (os.osPathS_joinPath R (joinPath [] rcs) j0 cs (DFrac.own qp) jp hR hm hcs).2 $$ Hs
      wp_apply wp_touchProbe wpA wpF R _ name jp J qp h hJ hname hlen hcur hfo
        $$ [Hp Hperm Hn HJ HT] as %e3 H
      · iframe; iframe #
      try wp_auto
      iapply HΦ $$ H

end proof

end EtcdGrove
end Perennial
