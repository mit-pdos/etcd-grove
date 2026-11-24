/-
The proof of `Spec/os/OpenFileS.lean`: the model's `EINTR` loop by Löb induction, each attempt a
`CallBegin` (the log's length at least the claim's last change, `osNames_next`) and the
extension's `Open`. Before the file was created, an attempt opens the atomic update around the
step (`wp_au_step`; the claim whole, `wp_osOpenCreateS`): an `EINTR` with no effect aborts, any
other result commits. After an attempt created it and returned `EINTR`, the caller's fraction of
the claim names the new file, and the retry opens it (`wp_osOpenFileS`).
-/
module

public import Proof.os.ErrorOk
public import Spec.os.OpenFileS
public import GooseLang.Ext.Fs.NoErrSpecsOpenFile
public import Proof.os.IgnoringEINTR
public import Proof.os.ForLoeb

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions]

theorem os.OpenFile.wp_proofCreateSnc : os.OpenFile.specCreateSnc (GF := GF) (hG := hG) := by
  intro d b flag perm R j dq h q r qc Q hfl hcr htr hb hnd hq
  generalize hfl' : flag ||| W64 0x80000 = fl at hfl hcr htr ⊢
  wp_start as ⟨#Hos, #Hsi, Hp, Hperm, Hn, Hau⟩
  imod osNames_next R j _ _ h CoPset.subseteq_top $$ Hsi Hn with ⟨Hn, #Hlb⟩
  ihave HSt : iprop((osAUnc (osNames j (.only [b]) (DFrac.own r) h) (crOut j b h (DFrac.own r)) Q ∗
      osNames j (.only [b]) (DFrac.own q) h) ∨
    (∃ xs, Q (some xs) ∗ crOut j b h (DFrac.own q) (some xs) ∗ crMeta (some xs)))
    $$ [Hau Hn]
  · ileft; iframe
  wp_for_bind
  iloeb as IH generalizing Hperm Hp HSt HΦ
  wp_for_step
  icases osCallPerm_child R d b _ _ _ $$ Hp Hperm with ⟨Hp, Hperm⟩
  try wp_auto
  wp_open_stub
  wp_apply wp_osCallBeginS R _ qc h.next CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hperm Hlb as %t %s0 %hs Hk Hls
  iclear Hls
  try rw [os.file_ty_eq]
  try rw [os.File_ty_eq]
  try rw [show flag ||| W64 524288 = fl from hfl']
  (try wp_auto)
  icases HSt with (⟨Hau, Hn⟩ | ⟨%xs, HQ, Hout, Hm⟩)
  · wp_apply +noauto (wp_aunc_step "Open" _ (osNames j (.only [b]) (DFrac.own r) h)
      (crOut j b h (DFrac.own r)) Q) $$ Hau [Hn Hk Hp HΦ]
    iintro Hr
    ihave Hw := (osNames_join j _ q r h hq).1 $$ [Hn Hr]
    · iframe
    iapply wp_osOpenCreateS R d b j dq h t s0 qc fl hfl hcr htr hb hnd hs osN_sub_au osShN_sub_au
      $$ Hos Hsi Hp Hw Hk
    iintro %fd %e Hperm Hp Hres
    icases Hres with (⟨%i, %hi, Hw, Hr⟩ | ⟨%hn, %x, %i, Hlog, Hw, Hm, Hr⟩ | ⟨%he, Hw⟩)
    · -- the file existed
      icases (osNames_join j _ q r h hq).2 $$ Hw with ⟨Hn, Hr'⟩
      icases Hr with (%he | ⟨%he, Hfd⟩)
      · by_cases he4 : e = W64 4
        · ileft
          iframe Hr'
          iintro Hau
          obtain ⟨-, rfl⟩ := he
          subst he4
          try wp_auto
          try rw [os.file_ty_eq]
          try rw [os.File_ty_eq]
          wp_for_post
          inext
          iapply IH $$ Hperm Hp [Hau Hn] HΦ [$] [$] [$] [$] [$]
          ileft; iframe
        · iright
          iexists none
          isplitl [Hr']
          · dsimp only [crOut]; iexact Hr'
          iintro HQ
          obtain ⟨he0, rfl⟩ := he
          try wp_auto
          rw [decide_eq_false (show e ≠ W64 0 from he0)]
          try wp_auto
          rw [decide_eq_false (show e ≠ W64 4 from he4)]
          try wp_auto
          wp_apply os.wp_modelErrno
          try wp_auto
          wp_apply os.wp_modelPathError_ok _ _ e he0 as %pe #Hok
          try wp_auto
          wp_for_post
          iapply HΦ
          iframe
          dsimp only [crOut, crMeta]
          iframe
          isplitl []
          · iempintro
          iright
          isplitr
          · ipureintro; exact ⟨(fun h => by cases h), rfl⟩
          iapply (EtcdGrove.fmtErrorOkOrNil_of _) $$ Hok
      · iright
        iexists none
        isplitl [Hr']
        · dsimp only [crOut]; iexact Hr'
        iintro HQ
        obtain ⟨rfl, hfd0⟩ := he
        try wp_auto
        os_newfile
        wp_for_post_core
        iapply wp_fupd
        try wp_auto
        ipersist name
        ipersist f
        ipersist nonblock
        imodintro
        iapply HΦ
        iframe
        dsimp only [crOut, crMeta]
        iframe
        ileft
        iexists fd, i
        iframe
        isplitr
        · ipureintro; exact ⟨rfl, hfd0, hi⟩
        unfold os.ownFile os.ownOff
        isplitr [off]
        · iexists inner_ptr
          iframe
          isplitl [] <;> (try isplitl []) <;> iassumption
        · iexists inner_ptr
          iframe
          iassumption
    · -- the file created
      icases (osNames_join j _ q r _ hq).2 $$ Hw with ⟨Hn, Hr'⟩
      unfold osLogged
      icases Hlog with ⟨%hst, #He, #Hl⟩
      iright
      iexists some (x, s0, i)
      isplitl [Hr']
      · dsimp only [crOut, osLogged, crEnt]; iframe; iframe #
        ipureintro; exact ⟨⟨hn, hs⟩, hst⟩
      iintro HQ
      ihave Hout : crOut j b h (DFrac.own q) (some (x, s0, i)) $$ [Hn]
      · dsimp only [crOut, osLogged, crEnt]; iframe; iframe #
        ipureintro; exact ⟨⟨hn, hs⟩, hst⟩
      icases Hr with (%he | ⟨%he, Hfd⟩)
      · obtain ⟨he0, rfl⟩ := he
        try wp_auto
        rw [decide_eq_false (show e ≠ W64 0 from he0)]
        try wp_auto
        by_cases he4 : e = W64 4
        · rw [decide_eq_true he4]
          try wp_auto
          try rw [os.file_ty_eq]
          try rw [os.File_ty_eq]
          wp_for_post
          inext
          iapply IH $$ Hperm Hp [HQ Hout Hm] HΦ [$] [$] [$] [$] [$]
          iright; iexists (x, s0, i); dsimp only [crMeta]; iframe
        rw [decide_eq_false (show e ≠ W64 4 from he4)]
        try wp_auto
        wp_apply os.wp_modelErrno
        try wp_auto
        wp_apply os.wp_modelPathError_ok _ _ e he0 as %pe #Hok
        try wp_auto
        wp_for_post
        iapply HΦ
        dsimp only [crMeta]
        iframe
        iright
        isplitr
        · ipureintro; exact ⟨(fun h => by cases h), rfl⟩
        iapply (EtcdGrove.fmtErrorOkOrNil_of _) $$ Hok
      · obtain ⟨rfl, hfd0⟩ := he
        try wp_auto
        os_newfile
        wp_for_post_core
        iapply wp_fupd
        try wp_auto
        ipersist name
        ipersist f
        ipersist nonblock
        imodintro
        iapply HΦ
        dsimp only [crMeta]
        iframe
        ileft
        iexists fd, i
        iframe
        isplitr
        · ipureintro; exact ⟨rfl, hfd0, rfl⟩
        unfold os.ownFile os.ownOff
        isplitr [off]
        · iexists inner_ptr
          iframe
          isplitl [] <;> (try isplitl []) <;> iassumption
        · iexists inner_ptr
          iframe
          iassumption
    · -- an error, no effect
      icases (osNames_join j _ q r h hq).2 $$ Hw with ⟨Hn, Hr'⟩
      by_cases he4 : e = W64 4
      · ileft
        iframe Hr'
        iintro Hau
        obtain ⟨-, rfl⟩ := he
        subst he4
        try wp_auto
        try rw [os.file_ty_eq]
        try rw [os.File_ty_eq]
        wp_for_post
        inext
        iapply IH $$ Hperm Hp [Hau Hn] HΦ [$] [$] [$] [$] [$]
        ileft; iframe
      · iright
        iexists none
        isplitl [Hr']
        · dsimp only [crOut]; iexact Hr'
        iintro HQ
        obtain ⟨he0, rfl⟩ := he
        try wp_auto
        rw [decide_eq_false (show e ≠ W64 0 from he0)]
        try wp_auto
        rw [decide_eq_false (show e ≠ W64 4 from he4)]
        try wp_auto
        wp_apply os.wp_modelErrno
        try wp_auto
        wp_apply os.wp_modelPathError_ok _ _ e he0 as %pe #Hok
        try wp_auto
        wp_for_post
        iapply HΦ
        iframe
        dsimp only [crOut, crMeta]
        iframe
        isplitl []
        · iempintro
        iright
        isplitr
        · ipureintro; exact ⟨(fun h => by cases h), rfl⟩
        iapply (EtcdGrove.fmtErrorOkOrNil_of _) $$ Hok
  · obtain ⟨x, sx, i⟩ := xs
    have hi : (h.log x (crEnt j b i sx) (<[b := .file i]> h.cur)).cur !! b = some (.file i) := by
      simp only [NamesH.log]; exact GMap.lookup_insert _ _ _
    isimp only [crOut] at Hout
    icases Hout with ⟨%hc, Hlo, Hn⟩
    wp_apply +noauto wp_osOpenFileS R d b j i (.only [b]) dq (DFrac.own q) _ t s0 qc fl
      hfl htr hb
      (by simp [NameSet.Mem]) hi CoPset.subseteq_top CoPset.subseteq_top $$ Hos Hsi Hp Hn Hk
      as %fd %e %hres Hperm Hp Hn Hfd
    ihave Hout : crOut j b h (DFrac.own q) (some (x, sx, i)) $$ [Hlo Hn]
    · dsimp only [crOut]; iframe; ipureintro; exact hc
    by_cases he0 : e = W64 0
    · subst he0
      have hfd0 : 0 ≤ fd.toInt := by rcases hres with ⟨-, h⟩ | ⟨h, -⟩; exact h; exact absurd rfl h
      ihave Hfd := (show (if W64 0 = (0 : w64) then osFd (GF := GF) fd (DFrac.own 1)
          (openFd i fl) else emp) ⊢ osFd fd (DFrac.own 1) (openFd i fl)
        by split
           · iintro H; iexact H
           · exact absurd rfl ‹_›) $$ Hfd
      try wp_auto
      os_newfile
      wp_for_post_core
      iapply wp_fupd
      try wp_auto
      ipersist name
      ipersist f
      ipersist nonblock
      imodintro
      iapply HΦ
      iframe
      ileft
      iexists fd, i
      iframe
      isplitr
      · ipureintro; exact ⟨rfl, hfd0, rfl⟩
      unfold os.ownFile os.ownOff
      isplitr [off]
      · iexists inner_ptr
        iframe
        isplitl [] <;> (try isplitl []) <;> iassumption
      · iexists inner_ptr
        iframe
        iassumption
    · iclear Hfd
      have hfd : fd = -1 := by rcases hres with ⟨h, -⟩ | ⟨-, h⟩; exact absurd h he0; exact h
      subst hfd
      try wp_auto
      rw [decide_eq_false (show e ≠ W64 0 from he0)]
      try wp_auto
      by_cases he4 : e = W64 4
      · rw [decide_eq_true he4]
        try wp_auto
        try rw [os.file_ty_eq]
        try rw [os.File_ty_eq]
        wp_for_post
        inext
        iapply IH $$ Hperm Hp [HQ Hout Hm] HΦ [$] [$] [$] [$] [$]
        iright; iexists (x, sx, i); dsimp only [crMeta]; iframe
      rw [decide_eq_false (show e ≠ W64 4 from he4)]
      try wp_auto
      wp_apply os.wp_modelErrno
      try wp_auto
      wp_apply os.wp_modelPathError_ok _ _ e he0 as %pe #Hok
      try wp_auto
      wp_for_post
      iapply HΦ
      iframe
      iright
      isplitr
      · ipureintro; exact ⟨(fun h => by cases h), rfl⟩
      iapply (EtcdGrove.fmtErrorOkOrNil_of _) $$ Hok

/-- `os.OpenFile.specCreateS` without the error witness (session S6: a helper of the proof below). -/
private abbrev os.OpenFile.tripleOldCreateS : Prop :=
  ∀ (d b : GoString) (flag : w64) (perm : w32) (R : Roots) (j : Ino) (dq : DFrac) (h : NamesH) (q r qc : Qp)
    (Q : Option (Nat × Nat × Ino) → IProp GF),
  OpenFlagsOk (flag ||| W64 0x80000).toNat → (flag ||| W64 0x80000).toNat / O_CREAT % 2 = 1 →
  (flag ||| W64 0x80000).toNat / O_TRUNC % 2 = 0 →
  NameOk b → (∀ J, h.cur !! b ≠ some (.dir J)) → q + r = 1 →
  {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d dq j ∗ osCallPerm (callKey R d) qc ∗
      osNames j (.only [b]) (DFrac.own q) h ∗
      osAU (osNames j (.only [b]) (DFrac.own r) h) (crOut j b h (DFrac.own r)) Q }}
    (App (App (App (Val (@! os.OpenFile)) (Val #(child d b))) (Val #flag)) (Val #perm))
  {{ (f : Loc) (err : GoInterface), RET (PairV #f #err); osPathS R d dq j ∗ osCallPerm (callKey R d) qc ∗
      ∃ o, Q o ∗ crOut j b h (DFrac.own q) o ∗ crMeta o ∗
        ((∃ (fd : w64) (i : Ino), ⌜err = interface.nil ∧ 0 ≤ fd.toInt ∧ crIno b h o i⌝ ∗
            os.ownFile f fd (child d b) (DFrac.own 1) ∗ os.ownOff f (W64 0) ∗
            osFd fd (DFrac.own 1) (openFd i (flag ||| W64 0x80000))) ∨
         ⌜err ≠ interface.nil ∧ f = null⌝ ∗ fmtErrorOkOrNil err) }}

/-- `os.OpenFile.specCreateS` over a semantics with no errors (the former `os.OpenFile.specCreateSNoErr`). -/
private abbrev os.OpenFile.tripleNECreateS : Prop :=
  ∀ (Sio : IoSet) [FsStepSat (NoIoErr Sio)] [FsStepSat (NoMapLockErr Sio)]
    (d b : GoString) (flag : w64) (perm : w32) (R : Roots) (j : Ino) (dq : DFrac) (h : NamesH)
    (q r qc : Qp) (Q : Option (Nat × Nat × Ino) → IProp GF),
  Sio.path (child d b) ∧ PathFits (child d b) →
  OpenFlagsOk (flag ||| W64 0x80000).toNat → (flag ||| W64 0x80000).toNat / O_CREAT % 2 = 1 →
  (flag ||| W64 0x80000).toNat / O_TRUNC % 2 = 0 →
  NameOk b → (∀ J, h.cur !! b ≠ some (.dir J)) → q + r = 1 →
  {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d dq j ∗ osCallPerm (callKey R d) qc ∗
      osNames j (.only [b]) (DFrac.own q) h ∗
      osAU (osNames j (.only [b]) (DFrac.own r) h) (crOut j b h (DFrac.own r)) Q }}
    (App (App (App (Val (@! os.OpenFile)) (Val #(child d b))) (Val #flag)) (Val #perm))
  {{ (f : Loc) (err : GoInterface), RET (PairV #f #err); osPathS R d dq j ∗ osCallPerm (callKey R d) qc ∗
      ∃ o, Q o ∗ crOut j b h (DFrac.own q) o ∗ crMeta o ∗
        ∃ (fd : w64) (i : Ino), ⌜err = interface.nil ∧ 0 ≤ fd.toInt ∧ crIno b h o i⌝ ∗
          os.ownFile f fd (child d b) (DFrac.own 1) ∗ os.ownOff f (W64 0) ∗
          osFd fd (DFrac.own 1) (openFd i (flag ||| W64 0x80000)) }}

/-- `specCreateS` (without the witness) from `specCreateSnc`: an `osAU` is an `osAUnc`. -/
private theorem os.OpenFile.wp_oldCreateS : os.OpenFile.tripleOldCreateS (GF := GF) (hG := hG) := by
  intro d b flag perm R j dq h q r qc Q hfl hcr htr hb hnd hq
  iintro %Φ ⟨#Hos, #Hsi, Hp, Hperm, Hn, Hau⟩ HΦ
  iapply os.OpenFile.wp_proofCreateSnc d b flag perm R j dq h q r qc Q hfl hcr htr hb hnd hq $$ [Hp Hperm Hn Hau] HΦ
  iframe Hos Hsi Hp Hperm Hn
  iapply osAU_osAUnc $$ Hau

private theorem os.OpenFile.wp_NECreateS : os.OpenFile.tripleNECreateS (GF := GF) (hG := hG) := by
  intro Sio _ _ d b flag perm R j dq h q r qc Q hS hfl hcr htr hb hnd hq
  generalize hfl' : flag ||| W64 0x80000 = fl at hfl hcr htr ⊢
  wp_start as ⟨#Hos, #Hsi, Hp, Hperm, Hn, Hau⟩
  ihave Hau := osAU_osAUnc _ _ _ $$ Hau
  imod osNames_next R j _ _ h CoPset.subseteq_top $$ Hsi Hn with ⟨Hn, #Hlb⟩
  ihave HSt : iprop((osAUnc (osNames j (.only [b]) (DFrac.own r) h) (crOut j b h (DFrac.own r)) Q ∗
      osNames j (.only [b]) (DFrac.own q) h) ∨
    (∃ xs, Q (some xs) ∗ crOut j b h (DFrac.own q) (some xs) ∗ crMeta (some xs)))
    $$ [Hau Hn]
  · ileft; iframe
  wp_for_bind
  iloeb as IH generalizing Hperm Hp HSt HΦ
  wp_for_step
  icases osCallPerm_child R d b _ _ _ $$ Hp Hperm with ⟨Hp, Hperm⟩
  try wp_auto
  wp_open_stub
  wp_apply wp_osCallBeginS R _ qc h.next CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hperm Hlb as %t %s0 %hs Hk Hls
  iclear Hls
  try rw [os.file_ty_eq]
  try rw [os.File_ty_eq]
  try rw [show flag ||| W64 524288 = fl from hfl']
  (try wp_auto)
  icases HSt with (⟨Hau, Hn⟩ | ⟨%xs, HQ, Hout, Hm⟩)
  · wp_apply +noauto (wp_aunc_step "Open" _ (osNames j (.only [b]) (DFrac.own r) h)
      (crOut j b h (DFrac.own r)) Q) $$ Hau [Hn Hk Hp HΦ]
    iintro Hr
    ihave Hw := (osNames_join j _ q r h hq).1 $$ [Hn Hr]
    · iframe
    iapply wp_osOpenCreateSNE Sio R d b j dq h t s0 qc fl hfl hcr htr hb hnd hs hS osN_sub_au osShN_sub_au
      $$ Hos Hsi Hp Hw Hk
    iintro %fd %e %hPe Hperm Hp Hres
    icases Hres with (⟨%i, %hi, Hw, Hr⟩ | ⟨%hn, %x, %i, Hlog, Hw, Hm, Hr⟩ | ⟨%he, Hw⟩)
    · -- the file existed
      icases (osNames_join j _ q r h hq).2 $$ Hw with ⟨Hn, Hr'⟩
      icases Hr with (%he | ⟨%he, Hfd⟩)
      · by_cases he4 : e = W64 4
        · ileft
          iframe Hr'
          iintro Hau
          obtain ⟨-, rfl⟩ := he
          subst he4
          try wp_auto
          try rw [os.file_ty_eq]
          try rw [os.File_ty_eq]
          wp_for_post
          inext
          iapply IH $$ Hperm Hp [Hau Hn] HΦ [$] [$] [$] [$] [$]
          ileft; iframe
        · exact absurd (hPe he.1) he4
      · iright
        iexists none
        isplitl [Hr']
        · dsimp only [crOut]; iexact Hr'
        iintro HQ
        obtain ⟨rfl, hfd0⟩ := he
        try wp_auto
        os_newfile
        wp_for_post_core
        iapply wp_fupd
        try wp_auto
        ipersist name
        ipersist f
        ipersist nonblock
        imodintro
        iapply HΦ
        iframe
        dsimp only [crOut, crMeta]
        iframe
        try iexists fd, i
        iframe
        isplitr
        · ipureintro; exact ⟨rfl, hfd0, hi⟩
        unfold os.ownFile os.ownOff
        isplitr [off]
        · iexists inner_ptr
          iframe
          isplitl [] <;> (try isplitl []) <;> iassumption
        · iexists inner_ptr
          iframe
          iassumption
    · -- the file created
      icases (osNames_join j _ q r _ hq).2 $$ Hw with ⟨Hn, Hr'⟩
      unfold osLogged
      icases Hlog with ⟨%hst, #He, #Hl⟩
      iright
      iexists some (x, s0, i)
      isplitl [Hr']
      · dsimp only [crOut, osLogged, crEnt]; iframe; iframe #
        ipureintro; exact ⟨⟨hn, hs⟩, hst⟩
      iintro HQ
      ihave Hout : crOut j b h (DFrac.own q) (some (x, s0, i)) $$ [Hn]
      · dsimp only [crOut, osLogged, crEnt]; iframe; iframe #
        ipureintro; exact ⟨⟨hn, hs⟩, hst⟩
      icases Hr with (%he | ⟨%he, Hfd⟩)
      · obtain ⟨he0, rfl⟩ := he
        try wp_auto
        rw [decide_eq_false (show e ≠ W64 0 from he0)]
        try wp_auto
        by_cases he4 : e = W64 4
        · rw [decide_eq_true he4]
          try wp_auto
          try rw [os.file_ty_eq]
          try rw [os.File_ty_eq]
          wp_for_post
          inext
          iapply IH $$ Hperm Hp [HQ Hout Hm] HΦ [$] [$] [$] [$] [$]
          iright; iexists (x, s0, i); dsimp only [crMeta]; iframe
        exact absurd (hPe he0) he4
      · obtain ⟨rfl, hfd0⟩ := he
        try wp_auto
        os_newfile
        wp_for_post_core
        iapply wp_fupd
        try wp_auto
        ipersist name
        ipersist f
        ipersist nonblock
        imodintro
        iapply HΦ
        dsimp only [crMeta]
        iframe
        try iexists fd, i
        iframe
        isplitr
        · ipureintro; exact ⟨rfl, hfd0, rfl⟩
        unfold os.ownFile os.ownOff
        isplitr [off]
        · iexists inner_ptr
          iframe
          isplitl [] <;> (try isplitl []) <;> iassumption
        · iexists inner_ptr
          iframe
          iassumption
    · -- an error, no effect
      icases (osNames_join j _ q r h hq).2 $$ Hw with ⟨Hn, Hr'⟩
      by_cases he4 : e = W64 4
      · ileft
        iframe Hr'
        iintro Hau
        obtain ⟨-, rfl⟩ := he
        subst he4
        try wp_auto
        try rw [os.file_ty_eq]
        try rw [os.File_ty_eq]
        wp_for_post
        inext
        iapply IH $$ Hperm Hp [Hau Hn] HΦ [$] [$] [$] [$] [$]
        ileft; iframe
      · exact absurd (hPe he.1) he4
  · obtain ⟨x, sx, i⟩ := xs
    have hi : (h.log x (crEnt j b i sx) (<[b := .file i]> h.cur)).cur !! b = some (.file i) := by
      simp only [NamesH.log]; exact GMap.lookup_insert _ _ _
    isimp only [crOut] at Hout
    icases Hout with ⟨%hc, Hlo, Hn⟩
    wp_apply +noauto wp_osOpenFileSNE Sio R d b j i (.only [b]) dq (DFrac.own q) _ t s0 qc fl
      hfl htr hb
      (by simp [NameSet.Mem]) hi hS CoPset.subseteq_top CoPset.subseteq_top $$ Hos Hsi Hp Hn Hk
      as %fd %e %hres Hperm Hp Hn Hfd
    ihave Hout : crOut j b h (DFrac.own q) (some (x, sx, i)) $$ [Hlo Hn]
    · dsimp only [crOut]; iframe; ipureintro; exact hc
    by_cases he0 : e = W64 0
    · subst he0
      have hfd0 : 0 ≤ fd.toInt := by rcases hres with ⟨-, h⟩ | ⟨h, -⟩; exact h; exact absurd rfl h
      ihave Hfd := (show (if W64 0 = (0 : w64) then osFd (GF := GF) fd (DFrac.own 1)
          (openFd i fl) else emp) ⊢ osFd fd (DFrac.own 1) (openFd i fl)
        by split
           · iintro H; iexact H
           · exact absurd rfl ‹_›) $$ Hfd
      try wp_auto
      os_newfile
      wp_for_post_core
      iapply wp_fupd
      try wp_auto
      ipersist name
      ipersist f
      ipersist nonblock
      imodintro
      iapply HΦ
      iframe
      try iexists fd, i
      iframe
      isplitr
      · ipureintro; exact ⟨rfl, hfd0, rfl⟩
      unfold os.ownFile os.ownOff
      isplitr [off]
      · iexists inner_ptr
        iframe
        isplitl [] <;> (try isplitl []) <;> iassumption
      · iexists inner_ptr
        iframe
        iassumption
    · iclear Hfd
      have hfd : fd = -1 := by rcases hres with ⟨h, -⟩ | ⟨-, h, -⟩; exact absurd h he0; exact h
      subst hfd
      try wp_auto
      rw [decide_eq_false (show e ≠ W64 0 from he0)]
      try wp_auto
      by_cases he4 : e = W64 4
      · rw [decide_eq_true he4]
        try wp_auto
        try rw [os.file_ty_eq]
        try rw [os.File_ty_eq]
        wp_for_post
        inext
        iapply IH $$ Hperm Hp [HQ Hout Hm] HΦ [$] [$] [$] [$] [$]
        iright; iexists (x, sx, i); dsimp only [crMeta]; iframe
      have hE4 : e = EINTR := by rcases hres with ⟨h, -⟩ | ⟨-, -, h⟩; exact absurd h he0; exact h
      exact absurd hE4 he4

/-- **`specCreateS`**: by cases on `FsNoErr ∧ PathFits (child d b)`, the error-free triple (its set
of paths covers `d/b`, which fits) or the one without the witness, whose error arm then has
`¬ FsNoErr ∨ ¬ PathFits (child d b)`. -/
theorem os.OpenFile.wp_proofCreateS : os.OpenFile.specCreateS (GF := GF) (hG := hG) := by
  intro d b flag perm R j dq h q r qc Q hfl hcr htr hb hnd hq
  iintro %Φ Hpre HΦ
  by_cases hne : FsNoErr ∧ PathFits (child d b)
  · obtain ⟨⟨Sio, hSio, hs1, hs2, hsp⟩, hfit⟩ := hne
    haveI := hs1
    haveI := hs2
    iapply os.OpenFile.wp_NECreateS Sio d b flag perm R j dq h q r qc Q ⟨hsp _, hfit⟩ hfl hcr htr hb hnd hq
      $$ Hpre
    inext
    iintro %f %err ⟨Hp, Hperm, %o, HQ, Hc, Hm, H⟩
    iapply HΦ
    iframe Hp Hperm
    iexists o
    iframe HQ Hc Hm
    ileft; iexact H
  · iapply os.OpenFile.wp_oldCreateS d b flag perm R j dq h q r qc Q hfl hcr htr hb hnd hq $$ Hpre
    inext
    iintro %f %err ⟨Hp, Hperm, %o, HQ, Hc, Hm, H⟩
    iapply HΦ
    iframe Hp Hperm
    iexists o
    iframe HQ Hc Hm
    icases H with (H | ⟨%he, Hok⟩)
    · ileft; iexact H
    · iright; iframe Hok; ipureintro
      exact ⟨he.1, he.2, (Classical.not_and_iff_not_or_not.1 hne)⟩

end proof

end EtcdGrove
end Perennial
