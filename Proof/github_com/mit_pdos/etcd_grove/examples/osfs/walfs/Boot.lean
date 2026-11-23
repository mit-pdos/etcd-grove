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
variable [sem : go.Semantics] [os.Assumptions] [os.file.FieldAssumptions]

set_option hygiene false in
/-- `Remove`'s `rmdir(2)` loop on `seg.tmp`, no directory in the history `hc` (`Hh`): each attempt
a nonzero errno with no effect, `EINTR` retried; then `post` after `iapply HΦ`. -/
local macro "rmdir_loop" hc:term ", " hnd:term " => " post:tacticSeq : tactic => `(tactic| (
  iloeb as IH2 generalizing Hperm Hh
  imod osPathS_root R d j (DFrac.own 1) hrj CoPset.subseteq_top $$ Hsi with Hp
  icases osCallPerm_child R d tmpB _ _ _ $$ Hp Hperm with ⟨Hp, Hperm⟩
  wp_apply wp_osCallBeginS R _ 1 h.next CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hperm Hlb as %t1 %s1 %hs1 Hk1 Hls1
  iclear Hls1
  icases (bHalf_eq (L := hG.goose_localGS) j γ ko _).1 $$ Hh with ⟨Hv, Hw⟩
  wp_apply wp_osRmdirSN_none R d tmpB j bN (DFrac.own 1) (DFrac.own (1 : Qp).half) $hc t1 s1 1
    tmpB_ok bN_tmp $hnd CoPset.subseteq_top CoPset.subseteq_top $$ Hos Hsi Hp Hw Hk1
    as %e1 %he1 Hperm - Hw
  ihave Hh := (bHalf_eq (L := hG.goose_localGS) j γ ko $hc).2 $$ [Hv Hw]
  · iframe
  by_cases he14 : e1 = W64 4
  · rw [decide_eq_true he14]
    wp_auto
    iapply IH2 $$ Hperm Hh HΦ
  rw [decide_eq_false he14]
  wp_auto
  rw [decide_eq_false (show e1 ≠ W64 0 from he1)]
  wp_auto
  unfold os.model.pathError
  by_cases h20 : e1 = W64 20
  · rw [decide_eq_true h20]
    wp_auto
    wp_apply wp_errno
    iapply HΦ
    ($post)
  · rw [decide_eq_false h20]
    wp_auto
    wp_apply wp_errno
    iapply HΦ
    ($post)))

/-- **`os.Remove(d/seg.tmp)`**, `d` the root of `j`, with the program's half: `seg` as it was; on
success nothing at `seg.tmp`. -/
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
  ihave HSt : iprop((bHalf (GF := GF) j γ ko h ∗ ⌜∃ i, h.cur !! tmpB = some (.file i)⌝) ∨
      ∃ h1, bHalf (GF := GF) j γ ko h1 ∗ ⌜h1.cur !! tmpB = none ∧ h1.cur !! segB = h.cur !! segB⌝)
    $$ [Hh]
  · cases hct : h.cur !! tmpB with
    | none => iright; iexists h; iframe Hh; ipureintro; simp [hct]
    | some n =>
      cases n with
      | file i => ileft; iframe Hh; ipureintro; simp
      | dir J => exact absurd hct (hnow.2.1 J)
  iloeb as IH generalizing Hperm HSt
  imod osPathS_root R d j (DFrac.own 1) hrj CoPset.subseteq_top $$ Hsi with Hp
  icases osCallPerm_child R d tmpB _ _ _ $$ Hp Hperm with ⟨Hp, Hperm⟩
  wp_apply wp_osCallBeginS R _ 1 h.next CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hperm Hlb as %t %s0 %hs Hk Hls
  iclear Hls
  icases HSt with (⟨Hh, %hi⟩ | ⟨%h1, Hh, %hn1⟩)
  · obtain ⟨i, hi⟩ := hi
    wp_apply wp_unlinkTmp R d (DFrac.own 1) j γ ko h i t s0 1 hi hs $$ Hos Hsi Hinv Hp Hh Hk
      as %e Hperm - Hres
    icases Hres with (⟨%he, Hh⟩ | ⟨%h', Hh, %hh'⟩)
    · by_cases he4 : e = W64 4
      · rw [decide_eq_true he4]
        wp_auto
        iapply IH $$ Hperm [Hh] HΦ
        ileft; iframe Hh; ipureintro; exact ⟨i, hi⟩
      rw [decide_eq_false he4]
      wp_auto
      rw [decide_eq_false (show e ≠ W64 0 from he)]
      wp_auto
      rmdir_loop h, (fun J hJ => by rw [hi] at hJ; cases hJ) =>
        iframe Hperm
        iexists h
        iframe Hh
        ipureintro; exact ⟨rfl, fun h => by cases h⟩
    · by_cases he4 : e = W64 4
      · rw [decide_eq_true he4]
        wp_auto
        iapply IH $$ Hperm [Hh] HΦ
        iright; iexists h'; iframe Hh; ipureintro; exact hh'
      rw [decide_eq_false he4]
      wp_auto
      by_cases he0 : e = W64 0
      · rw [decide_eq_true he0]
        wp_auto
        iapply HΦ
        iframe Hperm
        iexists h'
        iframe Hh
        ipureintro; exact ⟨hh'.2, fun _ => hh'.1⟩
      rw [decide_eq_false he0]
      wp_auto
      rmdir_loop h', (fun J hJ => by rw [hh'.1] at hJ; cases hJ) =>
        iframe Hperm
        iexists h'
        iframe Hh
        ipureintro; exact ⟨hh'.2, fun h => by cases h⟩
  · icases (bHalf_eq (L := hG.goose_localGS) j γ ko _).1 $$ Hh with ⟨Hv, Hw⟩
    wp_apply wp_osUnlinkSN_none R d tmpB j bN (DFrac.own 1) (DFrac.own (1 : Qp).half) h1 t s0 1
      tmpB_ok bN_tmp (fun i hi => by rw [hn1.1] at hi; cases hi) CoPset.subseteq_top
      CoPset.subseteq_top $$ Hos Hsi Hp Hw Hk as %e %he Hperm - Hw
    ihave Hh := (bHalf_eq (L := hG.goose_localGS) j γ ko h1).2 $$ [Hv Hw]
    · iframe
    by_cases he4 : e = W64 4
    · rw [decide_eq_true he4]
      wp_auto
      iapply IH $$ Hperm [Hh] HΦ
      iright; iexists h1; iframe Hh; ipureintro; exact hn1
    rw [decide_eq_false he4]
    wp_auto
    rw [decide_eq_false (show e ≠ W64 0 from he)]
    wp_auto
    rmdir_loop h1, (fun J hJ => by rw [hn1.1] at hJ; cases hJ) =>
      iframe Hperm
      iexists h1
      iframe Hh
      ipureintro; exact ⟨hn1.2, fun _ => hn1.1⟩

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
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ bootInv (GF := GF) j γ ∗ osCallPerm (callKey R d) 1 ∗
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
  imod bHalf_next R j γ ko h $$ Hsi Hh with ⟨Hh, #Hlb⟩
  obtain ⟨hfl, hcr, htr⟩ := create_flag
  obtain ⟨o, ho⟩ : ∃ o : Option Ino, o = none := ⟨none, rfl⟩
  ihave Hh := (show bHalf (GF := GF) j γ ko h ⊢ crState j γ ko h o by rw [ho]; exact .rfl) $$ Hh
  clear ho
  iloeb as IH generalizing %o Hperm Hh HΦ
  imod osPathS_root R d j (DFrac.own 1) hrj CoPset.subseteq_top $$ Hsi with Hp
  icases osCallPerm_child R d tmpB _ _ _ $$ Hp Hperm with ⟨Hp, Hperm⟩
  wp_apply wp_osCallBeginS R _ 1 h.next CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hperm Hlb as %t %s0 %hs Hk Hls
  iclear Hls
  rw [os.file_ty_eq, os.File_ty_eq]
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
      rw [decide_eq_true (show (0 : w64) = W64 0 from rfl)]
      wp_auto
      iStructNamed inner
      iapply wp_fupd
      wp_auto
      ipersist name
      ipersist f
      imodintro
      iapply HΦ
      iframe Hperm
      ileft
      iexists fd, i, h'
      iframe Hfd Hm Hh
      isplitr
      · ipureintro; exact ⟨rfl, hh'⟩
      unfold os.ownFile
      iexists inner_ptr
      iframe
      isplitl [] <;> iassumption
    all_goals
      obtain ⟨he0, rfl⟩ := he
      rw [decide_eq_false (show e ≠ W64 0 from he0)]
      wp_auto
    · -- no effect
      by_cases he4 : e = W64 4
      · rw [decide_eq_true he4]
        wp_auto
        try rw [os.file_ty_eq]
        try rw [os.File_ty_eq]
        iapply IH $$ %none Hperm Hh HΦ
      · rw [decide_eq_false he4]
        wp_auto
        unfold os.model.pathError
        wp_apply wp_errno
        iapply HΦ
        iframe Hperm
        iright
        isplitr
        · ipureintro; intro h; cases h
        iexists h; iframe Hh; ipureintro; rfl
    · -- created, the open failed
      by_cases he4 : e = W64 4
      · rw [decide_eq_true he4]
        wp_auto
        try rw [os.file_ty_eq]
        try rw [os.File_ty_eq]
        iapply IH $$ %(some i) Hperm [Hh Hm] HΦ
        try dsimp only
        iexists h'; iframe Hh Hm; ipureintro; exact hh'
      · rw [decide_eq_false he4]
        wp_auto
        unfold os.model.pathError
        wp_apply wp_errno
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
      wp_auto
      iStructNamed inner
      iapply wp_fupd
      wp_auto
      ipersist name
      ipersist f
      imodintro
      iapply HΦ
      iframe Hperm
      ileft
      iexists fd, i, h'
      iframe Hfd Hm Hh
      isplitr
      · ipureintro; exact ⟨rfl, hh'⟩
      unfold os.ownFile
      iexists inner_ptr
      iframe
      isplitl [] <;> iassumption
    · rw [decide_eq_false he0]
      iclear Hfd
      wp_auto
      by_cases he4 : e = W64 4
      · rw [decide_eq_true he4]
        wp_auto
        try rw [os.file_ty_eq]
        try rw [os.File_ty_eq]
        iapply IH $$ %(some i) Hperm [Hh Hm] HΦ
        try dsimp only
        iexists h'; iframe Hh Hm; ipureintro; exact hh'
      · rw [decide_eq_false he4]
        wp_auto
        unfold os.model.pathError
        wp_apply wp_errno
        iapply HΦ
        iframe Hperm
        iright
        isplitr
        · ipureintro; intro h; cases h
        iexists h'; iframe Hh; ipureintro; exact hh'.2

end oscalls

end osfs_walfs
end EtcdGrove
end Perennial

end
