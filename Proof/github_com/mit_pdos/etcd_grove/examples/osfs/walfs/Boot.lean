/-
The proofs of `examples/osfs/walfs`'s `segdir.go` (one generation) over the file extension's shared
view: the specs of `Boot` and its helpers.

The crash invariant (`bootInv`, `BootClaims.lean`) holds half of the claim on `seg` and `seg.tmp` of
the root `dir` (inode `j`), a ghost variable recording the key `ko` and the claim's history, the
facts every crash keeps (`BInv`: `SafeT` of what a crash leaves), and the invariant's half of the
key's file (`DS.keyRes`: every crash of it `DataGood`). The program holds the other half (`bHalf`).
`Boot` reads the names through its half (`wp_readNamesS`), removes `seg.tmp` (`wp_removeTmp`, the
`unlink` with the invariant opened), and either checks `seg` (`DS.wp_check`) or commits: creates
`seg.tmp` (`wp_openTmp`), writes and syncs the data, deposits the file under the key
(`boot_deposit`), renames it onto `seg` (`wp_renameSeg`), syncs the directory and checks.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.walfs.BootClaims
public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.walfs.DSCheck
public import Spec.os.File__WriteAt
public import Spec.os.File__Fd
public import Spec.syscall.Fdatasync
public import Proof.os.IgnoringEINTR

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace osfs_walfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
  github_com.mit_pdos.etcd_grove.examples.osfs.walfs
open Fs BC

theorem dataC_length : dataC.length = 8 := rfl

theorem create_flag :
    OpenFlagsOk (W64 66 ||| W64 0x80000).toNat ∧ (W64 66 ||| W64 0x80000).toNat / O_CREAT % 2 = 1 ∧
      (W64 66 ||| W64 0x80000).toNat / O_TRUNC % 2 = 0 := by
  unfold OpenFlagsOk O_CREAT O_TRUNC O_CLOEXEC
  decide

theorem create_openFd (i : Ino) : openFd i (W64 66 ||| W64 0x80000) = ⟨i, true, true, none, none⟩ := rfl

/-- The data written and synced, as `check` needs it. -/
theorem checkOk_synced (m : OsMeta) (hsz : m.size = 8) (ys : List ByteG)
    (hys : ys.map Prod.fst = DSBase.dataC) : DS.CheckOk m.synced (ys.map (fun x => durB x.1)) := by
  have hl : ys.length = 8 := by
    have := congrArg List.length hys; simp only [List.length_map] at this; rw [this]; rfl
  refine ⟨by simp [OsMeta.synced, hsz], by simp [hl], ?_⟩
  simp only [List.map_map]
  rw [← hys]; rfl

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

theorem bHalf_eq (j : Ino) (γ : GName) (ko : Option Ino) (h : NamesH) :
    bHalf (L := L) j γ ko h ⊣⊢
      iprop(ghostVar γ (1 : Qp).half (ko, h) ∗ osNames (L := L) j bN (DFrac.own (1 : Qp).half) h) := by
  unfold bHalf; exact .rfl

/-- The log is at least as long as the program's half knows. -/
theorem bHalf_next (R : Roots) (j : Ino) (γ : GName) (ko : Option Ino) (h : NamesH) :
    ⊢ osSharedInv (L := L) R -∗ bHalf (L := L) j γ ko h ={⊤}=∗
      bHalf (L := L) j γ ko h ∗ osLogLb (L := L) h.next := by
  iintro #Hsi Hh
  unfold bHalf
  icases Hh with ⟨Hv, Hw⟩
  imod osNames_next R j bN _ h CoPset.subseteq_top $$ Hsi Hw with ⟨Hw, Hlb⟩
  imodintro
  iframe

end res

/-! ## `os` calls on `seg.tmp` and `seg` -/

section oscalls
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [go.BasicIntoValInj]
variable [sem : go.Semantics] [os.Assumptions]

/-- The unlink loop's state in `wp_removeTmp`: `seg.tmp` still the file it was, or gone. -/
def rmSt (j : Ino) (γ : GName) (ko : Option Ino) (h : NamesH) : IProp GF :=
  iprop((bHalf (GF := GF) j γ ko h ∗ ⌜∃ i, h.cur !! tmpB = some (.file i)⌝) ∨
      ∃ h1, bHalf (GF := GF) j γ ko h1 ∗ ⌜h1.cur !! tmpB = none ∧ h1.cur !! segB = h.cur !! segB⌝)

/-- **`os.Remove(d/seg.tmp)`**, `d` the root of `j`, with the program's half: `seg` as it was; on
success nothing at `seg.tmp`. `os.Remove` is Go's: `ignoringEINTR` around `syscall.Unlink` (the
stub `fsUnlink`; while `seg.tmp` is still the file, the unlink opens the invariant, `wp_unlinkTmp`),
then for an error `ignoringEINTR` around `syscall.Rmdir` (each attempt failing, no directory there). -/
theorem wp_removeTmp (R : Roots) (d : GoString) (j : Ino) (hrj : (d, j) ∈ R) (γ : GName)
    (ko : Option Ino) (h : NamesH) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ bootInv (GF := GF) j γ ∗ osCallPerm (callKey R d) 1 ∗
        bHalf (GF := GF) j γ ko h }}
      (App (Val (@! os.Remove)) (Val #(child d tmpB)))
    {{ (err : GoInterface), RET #err; osCallPerm (callKey R d) 1 ∗ ∃ h', bHalf (GF := GF) j γ ko h' ∗
        ⌜h'.cur !! segB = h.cur !! segB ∧ (err = interface.nil → h'.cur !! tmpB = none)⌝ }} := by
  wp_start as ⟨#Hos, #Hsi, #Hinv, Hperm, Hh⟩
  imod boot_facts R j γ ko h $$ Hinv Hsi Hh with ⟨Hh, %hnow⟩
  imod bHalf_next R j γ ko h $$ Hsi Hh with ⟨Hh, #Hlb⟩
  ihave HSt : rmSt (GF := GF) j γ ko h $$ [Hh]
  · unfold rmSt
    cases hct : h.cur !! tmpB with
    | none => iright; iexists h; iframe Hh; ipureintro; simp [hct]
    | some n =>
      cases n with
      | file i => ileft; iframe Hh; ipureintro; simp
      | dir J => exact absurd hct (hnow.2.1 J)
  try wp_auto
  rw [recv_eq_func_mk]
  -- the unlink loop
  wp_apply (os.wp_ignoringEINTR _
    iprop(name_ptr ↦ child d tmpB ∗ osCallPerm (callKey R d) 1 ∗ rmSt (GF := GF) j γ ko h)
    (fun e => iprop(name_ptr ↦ child d tmpB ∗ osCallPerm (callKey R d) 1 ∗
      ∃ h1, bHalf (GF := GF) j γ ko h1 ∗ ⌜h1.cur !! segB = h.cur !! segB ∧
        (∀ J, h1.cur !! tmpB ≠ some (.dir J)) ∧ (e = 0 → h1.cur !! tmpB = none)⌝)))
    $$ [name Hperm HSt] as %e ⟨Hname, Hperm, %h1, Hh, %hh1⟩
  · iframe
    iintro !>
    unfold os.eintrCall
    iintro %Φ' ⟨Hname, Hperm, HSt⟩ HΦ'
    rw [← recv_eq_func_mk]
    wp_call
    try wp_auto
    irename : (_ ↦ (_ : GoInterface) : IProp GF) => Hres0c
    wp_func_call; wp_call
    try wp_auto
    irename «$res0» => Hres0u
    imod osPathS_root R d j (DFrac.own 1) hrj CoPset.subseteq_top $$ Hsi with Hp
    icases osCallPerm_child R d tmpB _ _ _ $$ Hp Hperm with ⟨Hp, Hperm⟩
    wp_stub syscall.fsUnlink.impl
    wp_apply +noauto wp_osCallBeginS R _ 1 h.next CoPset.subseteq_top CoPset.subseteq_top
      $$ Hos Hsi Hperm Hlb as %t %s0 %hs Hk Hls
    iclear Hls
    unfold rmSt
    icases HSt with (⟨Hh, %hi⟩ | ⟨%h1, Hh, %hn1⟩)
    · obtain ⟨i, hi⟩ := hi
      wp_apply +noauto wp_unlinkTmp R d (DFrac.own 1) j γ ko h i t s0 1 hi hs $$ Hos Hsi Hinv Hp Hh Hk
        as %e Hperm - Hres
      try wp_auto
      wp_apply wp_errnoErr
      try wp_auto
      iapply HΦ'
      try dsimp only
      icases Hres with (⟨%he, Hh⟩ | ⟨%h', Hh, %hh'⟩)
      · by_cases he4 : e = W64 4
        · ileft
          isplitr
          · ipureintro; exact he4
          iframe Hname Hperm
          ileft; iframe Hh; ipureintro; exact ⟨i, hi⟩
        · iright
          isplitr
          · ipureintro; exact he4
          iframe Hname Hperm
          iexists h
          iframe Hh
          ipureintro
          exact ⟨rfl, (fun J hJ => by rw [hi] at hJ; cases hJ), fun h0 => absurd h0 he⟩
      · by_cases he4 : e = W64 4
        · ileft
          isplitr
          · ipureintro; exact he4
          iframe Hname Hperm
          iright; iexists h'; iframe Hh; ipureintro; exact hh'
        · iright
          isplitr
          · ipureintro; exact he4
          iframe Hname Hperm
          iexists h'
          iframe Hh
          ipureintro
          exact ⟨hh'.2, (fun J hJ => by rw [hh'.1] at hJ; cases hJ), fun _ => hh'.1⟩
    · icases (bHalf_eq (L := hG.goose_localGS) j γ ko _).1 $$ Hh with ⟨Hv, Hw⟩
      wp_apply +noauto wp_osUnlinkSN_none R d tmpB j bN (DFrac.own 1) (DFrac.own (1 : Qp).half) h1
        t s0 1 tmpB_ok bN_tmp (fun i hi => by rw [hn1.1] at hi; cases hi) CoPset.subseteq_top
        CoPset.subseteq_top $$ Hos Hsi Hp Hw Hk as %e %he Hperm - Hw
      ihave Hh := (bHalf_eq (L := hG.goose_localGS) j γ ko h1).2 $$ [Hv Hw]
      · iframe
      try wp_auto
      wp_apply wp_errnoErr
      try wp_auto
      iapply HΦ'
      try dsimp only
      by_cases he4 : e = W64 4
      · ileft
        isplitr
        · ipureintro; exact he4
        iframe Hname Hperm
        iright; iexists h1; iframe Hh; ipureintro; exact hn1
      · iright
        isplitr
        · ipureintro; exact he4
        iframe Hname Hperm
        iexists h1
        iframe Hh
        ipureintro
        exact ⟨hn1.2, (fun J hJ => by rw [hn1.1] at hJ; cases hJ), fun _ => hn1.1⟩
  -- after the unlink loop
  obtain ⟨hseg, hnd, h0e⟩ := hh1
  by_cases h0 : e = 0
  · subst h0
    simp only [errnoErr, ↓reduceIte]
    try wp_auto
    iapply HΦ
    iframe Hperm
    iexists h1
    iframe Hh
    ipureintro; exact ⟨hseg, fun _ => h0e rfl⟩
  simp only [errnoErr, h0, ↓reduceIte]
  try wp_auto
  rw [recv_eq_func_mk]
  -- the rmdir loop
  wp_apply (os.wp_ignoringEINTR _
    iprop(name_ptr ↦ child d tmpB ∗ osCallPerm (callKey R d) 1 ∗ bHalf (GF := GF) j γ ko h1)
    (fun e1 => iprop(⌜e1 ≠ W64 0⌝ ∗ name_ptr ↦ child d tmpB ∗ osCallPerm (callKey R d) 1 ∗
      bHalf (GF := GF) j γ ko h1)))
    $$ [Hname Hperm Hh] as %e1 ⟨%he1, Hname, Hperm, Hh⟩
  · iframe
    iintro !>
    unfold os.eintrCall
    iintro %Φ' ⟨Hname, Hperm, Hh⟩ HΦ'
    rw [← recv_eq_func_mk]
    wp_call
    try wp_auto
    irename : (_ ↦ (_ : GoInterface) : IProp GF) => Hres0c
    wp_func_call; wp_call
    try wp_auto
    irename «$res0» => Hres0u
    imod osPathS_root R d j (DFrac.own 1) hrj CoPset.subseteq_top $$ Hsi with Hp
    icases osCallPerm_child R d tmpB _ _ _ $$ Hp Hperm with ⟨Hp, Hperm⟩
    wp_stub syscall.fsRmdir.impl
    wp_apply +noauto wp_osCallBeginS R _ 1 h.next CoPset.subseteq_top CoPset.subseteq_top
      $$ Hos Hsi Hperm Hlb as %t1 %s1 %hs1 Hk1 Hls1
    iclear Hls1
    icases (bHalf_eq (L := hG.goose_localGS) j γ ko _).1 $$ Hh with ⟨Hv, Hw⟩
    wp_apply +noauto wp_osRmdirSN_none R d tmpB j bN (DFrac.own 1) (DFrac.own (1 : Qp).half) h1
      t1 s1 1 tmpB_ok bN_tmp hnd CoPset.subseteq_top CoPset.subseteq_top $$ Hos Hsi Hp Hw Hk1
      as %e1 %he1 Hperm - Hw
    ihave Hh := (bHalf_eq (L := hG.goose_localGS) j γ ko h1).2 $$ [Hv Hw]
    · iframe
    try wp_auto
    wp_apply wp_errnoErr
    try wp_auto
    iapply HΦ'
    try dsimp only
    by_cases he4 : e1 = W64 4
    · ileft
      isplitr
      · ipureintro; exact he4
      iframe
    · iright
      isplitr
      · ipureintro; exact he4
      iframe
      ipureintro; exact he1
  have he1' : ¬ e1 = 0 := he1
  simp only [errnoErr, he1', ↓reduceIte]
  try wp_auto
  by_cases h20 : e1 = W64 20
  · subst h20
    try simp only [decide_true, Bool.not_true]
    try wp_auto
    try wp_alloc pe as Hpe
    try wp_auto
    iapply HΦ
    iframe Hperm
    iexists h1
    iframe Hh
    ipureintro; exact ⟨hseg, fun hc => by cases hc⟩
  · try simp only [decide_eq_false h20, Bool.not_false]
    try wp_auto
    try wp_alloc pe as Hpe
    try wp_auto
    iapply HΦ
    iframe Hperm
    iexists h1
    iframe Hh
    ipureintro; exact ⟨hseg, fun hc => by cases hc⟩

/-- What a retried create of `seg.tmp` sees: nothing there, or the file it made. -/
def crState (j : Ino) (γ : GName) (ko : Option Ino) (h : NamesH) : Option Ino → IProp GF
  | none => bHalf (GF := GF) j γ ko h
  | some i => iprop(∃ h', bHalf (GF := GF) j γ ko h' ∗
      ⌜h'.cur !! tmpB = some (.file i) ∧ h'.cur !! segB = h.cur !! segB⌝ ∗
      osMeta (GF := GF) i (DFrac.own 1) newMeta)

/-- **`os.OpenFile(d/seg.tmp, O_RDWR|O_CREATE, perm)`**, `seg.tmp` absent: on success a new file
`seg.tmp` names; `seg` as it was in any case. -/
theorem wp_openTmp (R : Roots) (d : GoString) (j : Ino) (hrj : (d, j) ∈ R) (γ : GName)
    (ko : Option Ino) (h : NamesH) (hn : h.cur !! tmpB = none) (perm : w32) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.os ∗ osInv (GF := GF) ∗ osSharedInv R ∗ bootInv (GF := GF) j γ ∗ osCallPerm (callKey R d) 1 ∗
        bHalf (GF := GF) j γ ko h }}
      (App (App (App (Val (@! os.OpenFile)) (Val #(child d tmpB))) (Val #(W64 66))) (Val #perm))
    {{ (f : Loc) (err : GoInterface), RET (PairV #f #err); osCallPerm (callKey R d) 1 ∗
        ((∃ (fd : w64) (i : Ino) (h' : NamesH),
            ⌜err = interface.nil ∧ h'.cur !! tmpB = some (.file i) ∧ h'.cur !! segB = h.cur !! segB⌝ ∗
            os.ownFile f fd (child d tmpB) (DFrac.own 1) ∗ osFd fd (DFrac.own 1) ⟨i, true, true, none, none⟩ ∗
            osMeta i (DFrac.own 1) newMeta ∗ bHalf (GF := GF) j γ ko h') ∨
         (⌜err ≠ interface.nil⌝ ∗ ∃ h', bHalf (GF := GF) j γ ko h' ∗
            ⌜h'.cur !! segB = h.cur !! segB⌝)) }} := by

  wp_start as ⟨#Hos, #Hsi, #Hinv, Hperm, Hh⟩
  ihave #Hsys0 : isPkgInit (PROP := IProp GF) pkg_id.syscall $$ []
  · iPkgInit
  ihave #Hsys := syscall.errnoOk_of_isPkgInit $$ Hsys0
  imod bHalf_next R j γ ko h $$ Hsi Hh with ⟨Hh, #Hlb⟩
  obtain ⟨hfl, hcr, htr⟩ := create_flag
  obtain ⟨o, ho⟩ : ∃ o : Option Ino, o = none := ⟨none, rfl⟩
  ihave Hh := (show bHalf (GF := GF) j γ ko h ⊢ crState j γ ko h o by rw [ho]; exact .rfl) $$ Hh
  clear ho
  wp_for_bind
  iloeb as IH generalizing %o Hperm Hh HΦ
  wp_for_step
  imod osPathS_root R d j (DFrac.own 1) hrj CoPset.subseteq_top $$ Hsi with Hp
  icases osCallPerm_child R d tmpB _ _ _ $$ Hp Hperm with ⟨Hp, Hperm⟩
  try wp_auto
  wp_open_stub
  wp_apply wp_osCallBeginS R _ 1 h.next CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hperm Hlb as %t %s0 %hs Hk Hls
  iclear Hls
  try rw [os.file_ty_eq]
  try rw [os.File_ty_eq]
  (try wp_auto)
  cases o with
  | none =>
    unfold crState
    wp_apply wp_createTmp R d (DFrac.own 1) j γ ko h t s0 1 (W64 66 ||| W64 0x80000) hfl hcr hn hs
      $$ Hos Hsi Hinv Hp Hh Hk as %fd %e Hperm - Hres
    icases Hres with (⟨%he, Hh⟩ | ⟨%i, %h', Hh, %hh', Hm, (%he | ⟨%he, Hfd⟩)⟩)
    rotate_right
    · -- created and opened
      obtain ⟨rfl, hfd0⟩ := he
      rw [create_openFd]
      (try rw [decide_eq_true (show (0 : w64) = W64 0 from rfl)])
      try wp_auto
      os_newfile
      wp_for_post_core
      iapply wp_fupd
      try wp_auto
      ipersist name
      ipersist f
      ipersist nonblock
      ipersist appendMode
      imodintro
      iapply HΦ
      iframe Hperm
      ileft
      iexists fd, i, h'
      iframe Hfd Hm Hh
      isplitr
      · ipureintro; exact ⟨rfl, hh'⟩
      unfold os.ownFile
      iexists _
      iframe
      (repeat' isplitl []) <;> iassumption
    all_goals
      obtain ⟨he0, rfl⟩ := he
      rw [decide_eq_false (show e ≠ W64 0 from he0)]
      try wp_auto
    · -- no effect
      by_cases he4 : e = W64 4
      · rw [decide_eq_true he4]
        try wp_auto
        try rw [os.file_ty_eq]
        try rw [os.File_ty_eq]
        wp_for_post
        inext
        iapply IH $$ %none Hperm Hh HΦ [$] [$] [$] [$] [$]
      · rw [decide_eq_false he4]
        try wp_auto
        wp_apply os.wp_modelErrno
        try wp_auto
        wp_apply os.wp_modelPathError
        iintro %pe
        try wp_auto
        wp_for_post
        iapply HΦ
        iframe Hperm
        iright
        isplitr
        · ipureintro; intro h; cases h
        iexists h; iframe Hh; ipureintro; rfl
    · -- created, the open failed
      by_cases he4 : e = W64 4
      · rw [decide_eq_true he4]
        try wp_auto
        try rw [os.file_ty_eq]
        try rw [os.File_ty_eq]
        wp_for_post
        inext
        iapply IH $$ %(some i) Hperm [Hh Hm] HΦ [$] [$] [$] [$] [$]
        try dsimp only
        iexists h'; iframe Hh Hm; ipureintro; exact hh'
      · rw [decide_eq_false he4]
        try wp_auto
        wp_apply os.wp_modelErrno
        try wp_auto
        wp_apply os.wp_modelPathError
        iintro %pe
        try wp_auto
        wp_for_post
        iapply HΦ
        iframe Hperm
        iright
        isplitr
        · ipureintro; intro h; cases h
        iexists h'; iframe Hh; ipureintro; exact hh'.2
  | some i =>
    unfold crState
    icases Hh with ⟨%h', Hh, %hh', Hm⟩
    icases (bHalf_eq (L := hG.goose_localGS) j γ ko _).1 $$ Hh with ⟨Hv, Hw⟩
    wp_apply wp_osOpenFileS R d tmpB j i bN (DFrac.own 1) (DFrac.own (1 : Qp).half) h' t s0 1
      (W64 66 ||| W64 0x80000) hfl htr tmpB_ok bN_tmp hh'.1 CoPset.subseteq_top
      CoPset.subseteq_top $$ Hos Hsi Hp Hw Hk as %fd %e %hres Hperm - Hw Hfd
    ihave Hh := (bHalf_eq (L := hG.goose_localGS) j γ ko h').2 $$ [Hv Hw]
    · iframe
    by_cases he0 : e = W64 0
    · subst he0
      rw [decide_eq_true rfl]
      ihave Hfd := (show (if W64 0 = (0 : w64) then osFd (GF := GF) fd (DFrac.own 1)
          (openFd i (W64 66 ||| W64 0x80000)) else emp) ⊢
            osFd fd (DFrac.own 1) ⟨i, true, true, none, none⟩
        by split
           · rw [create_openFd]
           · exact absurd rfl ‹_›) $$ Hfd
      try wp_auto
      os_newfile
      wp_for_post_core
      iapply wp_fupd
      try wp_auto
      ipersist name
      ipersist f
      ipersist nonblock
      ipersist appendMode
      imodintro
      iapply HΦ
      iframe Hperm
      ileft
      iexists fd, i, h'
      iframe Hfd Hm Hh
      isplitr
      · ipureintro; exact ⟨rfl, hh'⟩
      unfold os.ownFile
      iexists _
      iframe
      (repeat' isplitl []) <;> iassumption
    · rw [decide_eq_false he0]
      iclear Hfd
      try wp_auto
      by_cases he4 : e = W64 4
      · rw [decide_eq_true he4]
        try wp_auto
        try rw [os.file_ty_eq]
        try rw [os.File_ty_eq]
        wp_for_post
        inext
        iapply IH $$ %(some i) Hperm [Hh Hm] HΦ [$] [$] [$] [$] [$]
        try dsimp only
        iexists h'; iframe Hh Hm; ipureintro; exact hh'
      · rw [decide_eq_false he4]
        try wp_auto
        wp_apply os.wp_modelErrno
        try wp_auto
        wp_apply os.wp_modelPathError
        iintro %pe
        try wp_auto
        wp_for_post
        iapply HΦ
        iframe Hperm
        iright
        isplitr
        · ipureintro; intro h; cases h
        iexists h'; iframe Hh; ipureintro; exact hh'.2

set_option hygiene false in
/-- `os.Rename`'s error after a failed attempt `e` (`he : e ≠ 0`, `he4 : e ≠ 4`), the model's
`&LinkError{"rename", old, new, modelErrno(e)}`: `post` after `iapply HΦ`. -/
local macro "ren_err" " => " post:tacticSeq : tactic => `(tactic| (
  (try rw [decide_eq_false (show e ≠ W64 4 from he4)])
  try wp_auto
  (try rw [decide_eq_false (show ¬ e = W64 0 from he)])
  try wp_auto
  wp_apply os.wp_modelErrno
  (try wp_auto)
  wp_alloc le as Hle
  iclear Hle
  (try wp_auto)
  wp_for_post
  iapply HΦ
  ($post)))

/-- **`os.Rename(d/seg.tmp, d/seg)`**, `seg.tmp` the file of the invariant's key `i`, `seg` absent:
on success `seg` names `i`. -/
theorem wp_renameSeg (R : Roots) (d : GoString) (j : Ino) (hrj : (d, j) ∈ R) (γ : GName)
    (h : NamesH) (i : Ino) (hi : h.cur !! tmpB = some (.file i)) (hsn : h.cur !! segB = none) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ bootInv (GF := GF) j γ ∗ osCallPerm (callKey R d) 1 ∗
        bHalf (GF := GF) j γ (some i) h }}
      (App (App (Val (@! os.Rename)) (Val #(child d tmpB))) (Val #(child d segB)))
    {{ (err : GoInterface), RET #err; osCallPerm (callKey R d) 1 ∗ ∃ h',
        bHalf (GF := GF) j γ (some i) h' ∗ ⌜err = interface.nil → h'.cur !! segB = some (.file i)⌝ }} := by
  wp_start as ⟨#Hos, #Hsi, #Hinv, Hperm, Hh⟩
  imod bHalf_next R j γ (some i) h $$ Hsi Hh with ⟨Hh, #Hlb⟩
  imod osPathS_root R d j (DFrac.own 1) hrj CoPset.subseteq_top $$ Hsi with Hp
  -- `lstat(seg)`: not a directory
  icases osCallPerm_child R d segB _ _ _ $$ Hp Hperm with ⟨Hp, Hperm⟩
  try wp_auto
  wp_stub os.fsLstatDir.impl
  wp_apply wp_osCallBeginS R _ 1 h.next CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hperm Hlb as %t %s0 %hs0 Hk Hls
  iclear Hls
  icases (bHalf_eq (L := hG.goose_localGS) j γ (some i) h).1 $$ Hh with ⟨Hv, Hw⟩
  wp_apply wp_osLstatDirS_mem R d segB j bN (DFrac.own 1) (DFrac.own (1 : Qp).half) h t s0 1
    segB_ok bN_seg CoPset.subseteq_top CoPset.subseteq_top $$ Hos Hsi Hp Hw Hk
    as %isDir %e0 %hd Hperm - Hw
  have hd1 : isDir ≠ W64 1 := fun h1 => by
    obtain ⟨⟨J', hJ'⟩, -⟩ := hd h1
    rw [hsn] at hJ'; cases hJ'
  (try rw [decide_eq_false hd1])
  try wp_auto
  ihave Hh := (bHalf_eq (L := hG.goose_localGS) j γ (some i) h).2 $$ [Hv Hw]
  · iframe
  -- the rename loop: before the rename, or after it
  ihave HSt : iprop(bHalf (GF := GF) j γ (some i) h ∨
      ∃ h', bHalf (GF := GF) j γ (some i) h' ∗
        ⌜h'.cur !! tmpB = none ∧ h'.cur !! segB = some (.file i)⌝) $$ [Hh]
  · ileft; iexact Hh
  wp_for_bind
  iloeb as IH generalizing Hperm HSt HΦ
  wp_for_step
  imod osPathS_root R d j (DFrac.own 1) hrj CoPset.subseteq_top $$ Hsi with Hp
  icases osCallPerm_child R d tmpB _ _ _ $$ Hp Hperm with ⟨Hp, Hperm⟩
  try wp_auto
  wp_stub os.fsRename.impl
  wp_apply wp_osCallBeginS R _ 1 h.next CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hperm Hlb as %t1 %s1 %hs1 Hk1 Hls1
  iclear Hls1
  icases HSt with (Hh | ⟨%h', Hh, %hh'⟩)
  · wp_apply wp_renameTmp R d (DFrac.own 1) j γ h i t1 s1 1 hi hsn hs1
      $$ Hos Hsi Hinv Hp Hh Hk1 as %e Hperm - Hr
    icases Hr with (⟨%he, Hh⟩ | ⟨%h', Hh, %hh'⟩)
    · by_cases he4 : e = W64 4
      · (try rw [decide_eq_true he4])
        try wp_auto
        wp_for_post
        inext
        iapply IH $$ Hperm [Hh] HΦ [$] [$] [$]
        ileft; iexact Hh
      ren_err =>
        iframe Hperm
        iexists h; iframe Hh; ipureintro; intro hc; cases hc
    · by_cases he4 : e = W64 4
      · (try rw [decide_eq_true he4])
        try wp_auto
        wp_for_post
        inext
        iapply IH $$ Hperm [Hh] HΦ [$] [$] [$]
        iright; iexists h'; iframe Hh; ipureintro; exact hh'
      by_cases he0 : e = W64 0
      · (try rw [decide_eq_false (show e ≠ W64 4 from he4)])
        try wp_auto
        (try rw [decide_eq_true he0])
        try wp_auto
        wp_for_post
        iapply HΦ
        iframe Hperm
        iexists h'; iframe Hh; ipureintro; exact fun _ => hh'.2
      have he : e ≠ W64 0 := he0
      ren_err =>
        iframe Hperm
        iexists h'; iframe Hh; ipureintro; exact fun _ => hh'.2
  · icases (bHalf_eq (L := hG.goose_localGS) j γ (some i) h').1 $$ Hh with ⟨Hv, Hw⟩
    imod osPathS_root R d j (DFrac.own 1) hrj CoPset.subseteq_top $$ Hsi with Hp'
    icases osPathS_sameRoot R d tmpB segB _ j $$ Hp' with ⟨Hp', %hsr⟩
    wp_apply wp_osRenameAbsentS R d tmpB d segB j j bN (DFrac.own 1) (DFrac.own 1)
      (DFrac.own (1 : Qp).half) h' t1 s1 1 tmpB_ok segB_ok bN_tmp hh'.1 hsr CoPset.subseteq_top
      CoPset.subseteq_top $$ Hos Hsi Hp Hp' Hw Hk1 as %e %he Hperm - - Hw
    ihave Hh := (bHalf_eq (L := hG.goose_localGS) j γ (some i) h').2 $$ [Hv Hw]
    · iframe
    by_cases he4 : e = W64 4
    · (try rw [decide_eq_true he4])
      try wp_auto
      wp_for_post
      inext
      iapply IH $$ Hperm [Hh] HΦ [$] [$] [$]
      iright; iexists h'; iframe Hh; ipureintro; exact hh'
    ren_err =>
      iframe Hperm
      iexists h'; iframe Hh; ipureintro; exact fun _ => hh'.2

end oscalls

/-! ## `commit` and `Boot` -/

section prog
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [go.BasicIntoValInj]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.osfs.walfs.Assumptions]
variable [os.Assumptions]

/-- `commit(d)`, `d` the root of `j`, nothing at `seg.tmp` or `seg` now: it does not panic. -/
theorem wp_commit (wp_SyncDirS : os.File.Sync.specDirS (GF := GF) (hG := hG))
    (wp_ReadAt : os.File.ReadAt.spec (GF := GF) (hG := hG))
    (wp_Close : os.File.Close.spec (GF := GF) (hG := hG))
    (wp_WriteAt : os.File.WriteAt.spec (GF := GF) (hG := hG))
    (wp_Fd : os.File.Fd.spec (GF := GF) (hG := hG))
    (wp_Fdatasync : syscall.Fdatasync.spec (GF := GF) (hG := hG))
    (R : Roots) (d : GoString) (j : Ino) (hrj : (d, j) ∈ R) (γ : GName) (ko : Option Ino)
    (h : NamesH) (hn : h.cur !! tmpB = none) (hs : h.cur !! segB = none) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.os ∗ osInv (GF := GF) ∗ osSharedInv R ∗ bootInv (GF := GF) j γ ∗ osCallPerm (callKey R d) 1 ∗
        bHalf (GF := GF) j γ ko h }}
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.osfs.walfs.commit)) (Val #d))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hos, #Hsi, #Hinv, Hperm, Hh⟩
  try wp_auto
  rw [show d ++ go!"/seg.tmp" = child d tmpB from rfl, show (W64 2 ||| W64 64) = W64 66 from by decide]
  wp_apply wp_openTmp R d j hrj γ ko h hn (W32 438) $$ [Hperm Hh] as %f %err ⟨Hperm, Hr⟩
  · iframe; iframe #
  icases Hr with (⟨%fd, %i, %h2, %hek, Hf, Hfd, Hm, Hh⟩ | ⟨%herr, -⟩)
  rotate_left
  · cases err with
    | nil => exact absurd rfl herr
    | ok ie =>
    (try wp_auto)
    iapply HΦ
    itrivial
  obtain ⟨rfl, hk2, hs2⟩ := hek
  rw [hs] at hs2
  (try wp_auto)
  -- the data at 0
  wp_apply DSBase.wp_newData as %sl Hsl
  (try wp_auto)
  ihave Hb0 : osBytes (GF := GF) i (W64 0).toNat (DFrac.own 1) [] $$ []
  · unfold osBytes; iapply (bytesG_nil _ _ _ _).2; iempintro
  ihave Hmc : mcellsAny (GF := GF) newMeta.maps (W64 0).toNat ((W64 0).toNat + DSBase.dataC.length) $$ []
  · unfold mcellsAny; rw [show newMeta.maps = ∅ from rfl]
    iapply BigSepM.bigSepM_empty.2; iempintro
  wp_apply wp_WriteAt f fd (child d tmpB) (DFrac.own 1) sl DSBase.dataC (DFrac.own 1) (W64 0)
      (DFrac.own 1) ⟨i, true, true, none, none⟩ newMeta [] rfl (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) $$ [Hos Hf Hsl Hfd Hm Hb0 Hmc]
    as %n %err ⟨Hf, Hsl, Hfd, %k, %ys, %Hres, Hm, Hys, -⟩
  · iframe; iexact Hos
  obtain ⟨hj, hys, -, ⟨rfl, rfl, rfl⟩ | ⟨rfl, hne, -⟩⟩ := Hres
  rotate_left
  · cases err with
    | nil => exact absurd rfl hne
    | ok ie =>
    (try wp_auto)
    wp_apply wp_Close f fd (child d tmpB) ⟨i, true, true, none, none⟩ $$ [Hos Hf Hfd] as %e -
    · iframe; isplitr; iexact Hos; iapply lockToks_unlocked <;> rfl
    (try wp_auto)
    iapply HΦ
    itrivial
  have hys' : ys.map Prod.fst = DSBase.dataC := DS.pwOut_data hys
  have hysl : ys.length = (pwPost newMeta (W64 0).toNat DSBase.dataC.length DSBase.dataC.length).size := by
    rw [hys.1]; rfl
  (try wp_auto)
  -- `fdatasync`
  wp_apply wp_Fd f fd (child d tmpB) (DFrac.own 1) $$ Hf as Hf
  (try wp_auto)
  wp_apply wp_Fdatasync fd (DFrac.own 1) ⟨i, true, true, none, none⟩ _ 0 ys (OsMeta.covers_whole _ hysl)
      $$ [Hos Hfd Hm Hys]
    as %e ⟨Hfd, Hr⟩
  · iframe; iexact Hos
  icases Hr with (⟨%he, Hm, Hys⟩ | ⟨%he, -, -⟩)
  rotate_left
  · rw [show errnoErr e = interface.mkOk syscall.Errno.ty #e from if_neg he.1]
    dsimp only
    (try wp_auto)
    wp_apply wp_Close f fd (child d tmpB) ⟨i, true, true, none, none⟩ $$ [Hos Hf Hfd] as %e' -
    · iframe; isplitr; iexact Hos; iapply lockToks_unlocked <;> rfl
    (try wp_auto)
    iapply HΦ
    itrivial
  subst he
  rw [show errnoErr 0 = interface.nil from if_pos rfl]
  dsimp only
  (try wp_auto)
  wp_apply wp_Close f fd (child d tmpB) ⟨i, true, true, none, none⟩ $$ [Hos Hf Hfd] as %e' -
  · iframe; isplitr; iexact Hos; iapply lockToks_unlocked <;> rfl
  (try wp_auto)
  -- the file, durable, goes into the invariant under the key `i`
  icases (osMeta_halves (L := hG.goose_localGS) i _).1 $$ Hm with ⟨Hm, Hmi⟩
  icases (osBytes_halves (L := hG.goose_localGS) i 0 _).1 $$ Hys with ⟨Hys, Hysi⟩
  ihave Hk : DS.keyRes (L := hG.goose_localGS) (some i) $$ [Hmi Hysi]
  · unfold DS.keyRes
    iexists _, _
    iframe Hmi Hysi
    ipureintro; exact DS.synced_good _ rfl ys hys'
  imod boot_deposit j γ ko h2 i hs2 $$ Hinv Hh Hk with Hh
  -- the rename
  try rw [show d ++ go!"/seg" = child d segB from rfl]
  try rw [show d ++ go!"/seg.tmp" = child d tmpB from rfl]
  wp_apply wp_renameSeg R d j hrj γ h2 i hk2 hs2 $$ [Hperm Hh] as %err ⟨Hperm, %h3, Hh, %hh3⟩
  · iframe; iframe #
  cases err with
  | ok ie =>
    (try wp_auto)
    iapply HΦ
    itrivial
  | nil =>
  have hk3 := hh3 rfl
  (try wp_auto)
  -- the directory's sync
  imod osPathS_root R d j (DFrac.own 1) hrj CoPset.subseteq_top $$ Hsi with Hp
  wp_apply DS.wp_syncDir wp_SyncDirS R d (DFrac.own 1) j 1 $$ [Hp Hperm] as %ok ⟨Hp, Hperm⟩
  · iframe; iframe #
  cases ok with
  | false =>
    (try wp_auto)
    iapply HΦ
    itrivial
  | true =>
  (try wp_auto)
  icases (bHalf_eq (L := hG.goose_localGS) j γ (some i) h3).1 $$ Hh with ⟨-, Hw⟩
  wp_apply DS.wp_check wp_ReadAt wp_Close R d (DFrac.own 1) j bN (DFrac.own (1 : Qp).half) h3 1 i
      bN_seg hk3 _ _
      (checkOk_synced (pwPost newMeta (W64 0).toNat DSBase.dataC.length DSBase.dataC.length) rfl ys hys')
      $$ [Hp Hw Hperm Hm Hys]
  · iframe; iframe #
  (try wp_auto)
  iapply HΦ
  itrivial

/-- `Boot(d)`, `d` the root of `j`, with the program's half of the claim (history `h0`, key `ko0`)
and of the key's file: it does not panic. -/
theorem wp_Boot (wp_SyncDirS : os.File.Sync.specDirS (GF := GF) (hG := hG))
    (wp_ReadAt : os.File.ReadAt.spec (GF := GF) (hG := hG))
    (wp_Close : os.File.Close.spec (GF := GF) (hG := hG))
    (wp_WriteAt : os.File.WriteAt.spec (GF := GF) (hG := hG))
    (wp_Fd : os.File.Fd.spec (GF := GF) (hG := hG))
    (wp_Fdatasync : syscall.Fdatasync.spec (GF := GF) (hG := hG))
    (R : Roots) (d : GoString) (j : Ino) (hrj : (d, j) ∈ R) (γ : GName) (ko0 : Option Ino)
    (h0 : NamesH) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.os ∗ osInv (GF := GF) ∗ osSharedInv R ∗ bootInv (GF := GF) j γ ∗ osCallPerm (callKey R d) 1 ∗
        bHalf (GF := GF) j γ ko0 h0 ∗ DS.segRes (GF := GF) ko0 }}
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.osfs.walfs.Boot)) (Val #d))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hos, #Hsi, #Hinv, Hperm, Hh, Hs⟩
  imod boot_facts R j γ ko0 h0 $$ Hinv Hsi Hh with ⟨Hh, %hnow⟩
  try wp_auto
  imod osPathS_root R d j (DFrac.own 1) hrj CoPset.subseteq_top $$ Hsi with Hp
  icases (bHalf_eq (L := hG.goose_localGS) j γ ko0 h0).1 $$ Hh with ⟨Hv, Hw⟩
  wp_apply DSBase.wp_readNamesS d R j (DFrac.own 1) 1 bN (DFrac.own (1 : Qp).half) h0
    $$ [Hp Hperm Hw] as %sl %ok ⟨-, Hperm, Hw, Hr⟩
  · iframe; iframe #
  ihave Hh := (bHalf_eq (L := hG.goose_localGS) j γ ko0 h0).2 $$ [Hv Hw]
  · iframe
  icases Hr with (%hok | ⟨%names, %hn, Hsl⟩)
  · subst hok
    (try wp_auto)
    iapply HΦ
    itrivial
  obtain ⟨rfl, -, hmem, -⟩ := hn
  (try wp_auto)
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  ihave IH : iprop(∃ (i : w64) (nv : GoString) (hv : Bool) (h : NamesH),
      "i" ∷ i_ptr ↦ i ∗ "n" ∷ n_ptr ↦ nv ∗ "Hhv" ∷ have_ptr ↦ hv ∗
      "Hperm" ∷ osCallPerm (GF := GF) (callKey R d) 1 ∗
      "Hh" ∷ bHalf (GF := GF) j γ ko0 h ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.nat i ≤ names.length ∧
        hv = decide (segB ∈ names.take (sint.nat i)) ∧
        h.cur !! segB = h0.cur !! segB ∧
        (tmpB ∈ names.take (sint.nat i) → h.cur !! tmpB = none) ∧
        (tmpB ∉ names.take (sint.nat i) → h = h0)⌝) $$ [i n «have» Hperm Hh]
  · iexists W64 0, _, false, h0
    iframe
    ipureintro
    refine ⟨by decide, ?_, ?_, rfl, ?_, fun _ => rfl⟩ <;>
      rw [show sint.nat (W64 0) = 0 from rfl] <;> simp
  wp_for IH
  obtain ⟨hi0, hil, hhv, hseg, htmp, hsame⟩ := Hi
  wp_if_destruct
  · have Hlt : sint.nat i < names.length := by word
    have Hbnd : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sl.len := ⟨hi0, Hif⟩
    simp only [Hbnd, _root_.and_self, ↓reduceIte]
    obtain ⟨b, hb⟩ : ∃ b, names[sint.nat i]? = some b := ⟨_, List.getElem?_eq_getElem Hlt⟩
    wp_apply wp_load_slice_index sl (sint.Z i) names (DFrac.own 1) b hi0 $$ [Hsl] as Hsl
    · iframe; ipureintro; exact hb
    have htake : names.take (sint.nat (i + W64 1)) = names.take (sint.nat i) ++ [b] := by
      rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word]
      rw [List.take_add_one, hb]; rfl
    (try wp_auto)
    by_cases hbs : b = segB
    · subst hbs
      rw [decide_eq_true (show segB = go!"seg" from rfl)]
      try wp_auto
      wp_for_post
      iframe
      iexists i + W64 1, segB, true, h
      iframe
      ipureintro
      refine ⟨by word, by word, ?_, hseg, ?_, ?_⟩
      · rw [htake]; simp
      · rw [htake]; intro h
        simp only [List.mem_append, List.mem_singleton, tmp_ne_seg, or_false] at h
        exact htmp h
      · rw [htake]; intro h
        simp only [List.mem_append, List.mem_singleton, tmp_ne_seg, or_false] at h
        exact hsame h
    rw [decide_eq_false (show ¬ b = go!"seg" from hbs)]
    try wp_auto
    by_cases hbt : b = tmpB
    · subst hbt
      rw [decide_eq_true (show tmpB = go!"seg.tmp" from rfl)]
      try wp_auto
      rw [show d ++ go!"/seg.tmp" = child d tmpB from rfl]
      wp_apply wp_removeTmp R d j hrj γ ko0 h $$ [Hperm Hh] as %err ⟨Hperm, %h', Hh, %hh'⟩
      · iframe; iframe #
      cases err with
      | ok ie =>
        (try wp_auto)
        wp_for_post
        iapply HΦ
        itrivial
      | nil =>
      (try wp_auto)
      wp_for_post
      iframe
      iexists i + W64 1, tmpB, hv, h'
      iframe
      ipureintro
      refine ⟨by word, by word, ?_, hh'.1.trans hseg, fun _ => hh'.2 rfl, ?_⟩
      · rw [htake, hhv]; simp [Ne.symm tmp_ne_seg]
      · rw [htake]; simp
    rw [decide_eq_false (show ¬ b = go!"seg.tmp" from hbt)]
    try wp_auto
    wp_for_post
    iframe
    iexists i + W64 1, b, hv, h
    iframe
    ipureintro
    refine ⟨by word, by word, ?_, hseg, ?_, ?_⟩
    · rw [htake, hhv]; simp [Ne.symm hbs]
    · rw [htake]; intro h; simp [Ne.symm hbt] at h; exact htmp h
    · rw [htake]; intro h; simp [Ne.symm hbt] at h; exact hsame h
  · -- the loop is done
    have hie : sint.nat i = names.length := by word
    rw [hie, List.take_length] at hhv htmp hsame
    subst hhv
    by_cases hsin : segB ∈ names
    · rw [decide_eq_true hsin]
      (try wp_auto)
      have hsome := (hmem segB bN_seg).2 hsin
      obtain ⟨-, -, hn | ⟨k, rfl, hk⟩⟩ := hnow
      · rw [hn] at hsome; cases hsome
      unfold DS.segRes
      icases Hs with ⟨%m, %bs, Hm, Hb, %hok⟩
      imod osPathS_root R d j (DFrac.own 1) hrj CoPset.subseteq_top $$ Hsi with Hp
      icases (bHalf_eq (L := hG.goose_localGS) j γ _ h).1 $$ Hh with ⟨-, Hw⟩
      wp_apply DS.wp_check wp_ReadAt wp_Close R d (DFrac.own 1) j bN (DFrac.own (1 : Qp).half) h 1 k
          bN_seg (hseg.trans hk) m bs hok $$ [Hp Hw Hperm Hm Hb]
      · iframe; iframe #
      (try wp_auto)
      iapply HΦ
      itrivial
    · rw [decide_eq_false hsin]
      (try wp_auto)
      have hs0 : h0.cur !! segB = none := by
        cases hc : h0.cur !! segB with
        | none => rfl
        | some x => exact absurd ((hmem segB bN_seg).1 (by rw [hc]; rfl)) hsin
      have hn : h.cur !! tmpB = none := by
        by_cases ht : tmpB ∈ names
        · exact htmp ht
        · rw [hsame ht]
          cases hc : h0.cur !! tmpB with
          | none => rfl
          | some x => exact absurd ((hmem tmpB bN_tmp).1 (by rw [hc]; rfl)) ht
      wp_apply wp_commit wp_SyncDirS wp_ReadAt wp_Close wp_WriteAt wp_Fd wp_Fdatasync R d j hrj γ ko0 h hn
          (hseg.trans hs0) $$ [Hperm Hh]
      · iframe; iframe #
      (try wp_auto)
      iapply HΦ
      itrivial

end prog

end osfs_walfs
end EtcdGrove
end Perennial

end
