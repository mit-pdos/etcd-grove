/-
The proofs of `Spec/os/CrashSt.lean`: the models' loops as in `Proof/os/OpenFile.lean`,
`Proof/os/File__WriteAt.lean`, `Proof/os/File__Truncate.lean`, `Proof/os/File__Sync.lean` and
`Proof/golang_org/x/sys/unix/*.lean`, over the steps of `Proof/os/CrashStOps.lean`. The open's loop
keeps what its attempts may have made of the state (`CsOpenInv`); a write's loop keeps a state it
reached (`WReach`), with the bytes written so far (`wa_stepS`); a truncate's one of the three
`TReach` states. Lean-first (no Rocq counterpart).
-/
module

public import Spec.os.CrashSt
public import Proof.golang_org.x.sys.unix.Munmap
public import Perennial.Golang.Theory.Plain

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

theorem syscall.Fdatasync.wp_proof_crashS [syscall.Assumptions] :
    syscall.Fdatasync.specCrashS (GF := GF) (hG := hG) := by
  intro fd dq d N P R γ Good Ok m H F T fa fb hd hH hF hc hN hok hokF
  wp_start as ⟨#Hos, #Hinv, Hfd, Hown⟩
  wp_apply wp_osFsync_cs fd dq d N P R γ Good Ok m H F T fa fb hH hF hd hc hN hok hokF
    $$ Hos Hinv Hfd Hown
    as %e Hr Hfd
  iapply wp_errno
  iapply HΦ
  iframe Hfd
  icases Hr with (⟨%he, H⟩ | ⟨%he, H⟩)
  · ileft; iframe; ipureintro; exact he
  · iright; iframe; ipureintro; exact he.1

theorem golang_org.x.sys.unix.Mmap.wp_proof_crashS [golang_org.x.sys.unix.Assumptions] :
    golang_org.x.sys.unix.Mmap.specCrashS (GF := GF) (hG := hG) := by
  intro fd off len prot fl dq d N P R γ Good Ok m bs fa fb hrd hoff hlen hprot hfl hN hok
  wp_start as ⟨#Hos, #Hinv, Hfd, Hown⟩
  have hl : ¬ (sint.Z len ≤ sint.Z (W64 0)) := by
    rw [show sint.Z (W64 0) = 0 from rfl]; simp only [sint.Z]; omega
  rw [decide_eq_false hl]
  wp_auto
  wp_apply wp_osMmap_cs fd off len prot fl dq d N P R γ Good Ok m bs fa fb hN hrd hoff hlen hprot
    hfl hok
    $$ Hos Hinv Hfd Hown as %base %e Hr Hfd
  icases Hr with (⟨%he, Hown, Hc⟩ | ⟨%he, Hown⟩)
  · obtain ⟨rfl, hpos, hmax⟩ := he
    rw [show decide ((0 : w64) = W64 0) = true from decide_eq_true rfl]
    simp only [Bool.not_true]
    wp_auto
    wp_func_call
    wp_call
    have hnn : base ≠ null := by intro h; subst h; simp [null] at hpos
    have hlz : sint.Z len = (len.toNat : Int) := by
      simp only [sint.Z]; have := BitVec.toInt_eq_toNat_cond len; split at this <;> omega
    rw [ite_eq_right (by omega), ite_eq_right hnn,
      ite_eq_right (by simp only [maxAddr] at hmax; push_cast; omega)]
    wp_auto
    rw [← show errnoErr 0 = interface.nil by unfold errnoErr; rfl]
    iapply HΦ
    iframe
    ileft
    iexists base
    iframe
    ipureintro; exact ⟨rfl, rfl⟩
  · obtain ⟨he, rfl⟩ := he
    have he' : ¬ e = W64 0 := he
    simp only [decide_eq_false he', Bool.not_false]
    wp_auto
    wp_apply wp_errno
    iapply HΦ
    iframe
    iright
    iframe
    ipureintro; exact ⟨he, rfl⟩

theorem golang_org.x.sys.unix.Munmap.wp_proof_crashS [golang_org.x.sys.unix.Assumptions] :
    golang_org.x.sys.unix.Munmap.specCrashS (GF := GF) (hG := hG) := by
  intro base len p N P R γ Good Ok m bs fa fb vf hpos hb hN hok
  wp_start as ⟨#Hos, #Hinv, Hown, Hc⟩
  by_cases hl0 : len = W64 0
  · rw [decide_eq_true hl0]
    wp_auto
    iapply wp_errno
    iapply HΦ
    iright
    isplitr
    · ipureintro; intro h; cases h
    iright; iframe
  · rw [decide_eq_false hl0]
    wp_auto
    have h0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z len := by
      simp only [sint.Z]; exact ⟨by decide, hpos⟩
    rw [if_pos h0]
    have hn : 0 < len.toNat := by
      have := BitVec.toInt_eq_toNat_cond len; split at this <;> omega
    icases cellsR_pos base _ vf hn $$ Hc with ⟨Hc, %hbase⟩
    rw [show sint.Z (W64 0) = 0 from rfl, sliceIndexRef_byte ⟨base, len, len⟩ 0 hbase (Int.le_refl _)]
    have hb0 : (base +ₗ (0 : Int)) = base := by simp
    rw [hb0]
    wp_auto
    wp_apply wp_osMunmap_cs base len len p N P R γ Good Ok m bs fa fb len.toNat vf hN hb rfl rfl hok
      $$ Hos Hinv Hown Hc as %e Hr
    iapply wp_errno
    iapply HΦ
    iexact Hr

variable [os.Assumptions]

theorem os.File.Sync.wp_proof_crashS : os.File.Sync.specCrashS (GF := GF) (hG := hG) := by
  intro f fd name dqf dq d N P R γ Good Ok m H F T fa fb hd hH hF hc hN hok hokF
  unfold os.ownFile
  wp_start as ⟨#Hos, #Hinv, ⟨%inner, #Hf, Hfd, #Hn⟩, Hosfd, Hown⟩
  unfold os.model.inner
  rw [os.file_ty_eq, os.File_ty_eq]
  ihave #Hf2 := Hf
  iStructNamed Hf2
  wp_auto
  wp_apply wp_osFdKind fd dq d CoPset.subseteq_top $$ Hos Hosfd as Hosfd
  wp_apply wp_osFsync_cs fd dq d N P R γ Good Ok m H F T fa fb hH hF hd hc hN hok hokF
    $$ Hos Hinv Hosfd Hown as %e Hr Hosfd
  by_cases he4 : e = W64 4
  · icases Hr with (⟨%he, -⟩ | ⟨%he, -⟩)
    · exact absurd (he4 ▸ he) (by decide)
    · exact absurd he4 he.2
  rw [decide_eq_false he4]
  wp_auto
  icases Hr with (⟨%he, Hown⟩ | ⟨%he, Hown⟩)
  · subst he
    rw [show decide ((0 : w64) = W64 0) = true from decide_eq_true rfl]
    simp only [Bool.not_true]
    wp_auto
    iapply HΦ
    iframe
    isplitl []
    · isplitl [] <;> iassumption
    ileft
    isplitr; · ipureintro; rfl
    iframe
  · have he0' : ¬ e = W64 0 := he.1
    simp only [decide_eq_false he0', Bool.not_false]
    wp_auto
    wp_apply os.wp_wrapErrno _ inner name e $$ Hn as %pe
    iapply HΦ
    iframe
    isplitl []
    · isplitl [] <;> iassumption
    iright
    iframe
    ipureintro; intro h; cases h

theorem os.OpenFile.wp_proof_crashS [os.file.FieldAssumptions] :
    os.OpenFile.specCrashS (GF := GF) (hG := hG) := by
  intro d b perm N R V j γ Good Ok s hb hd hs hN hok
  wp_start as ⟨#Hos, #Hinv, Hown⟩
  obtain ⟨s', hs'⟩ : ∃ s', s' = s := ⟨_, rfl⟩
  obtain ⟨V', hV'⟩ : ∃ V', V' = V := ⟨_, rfl⟩
  ihave Hown := (show csOwn (GF := GF) (child d b) R γ s V ⊢ csOwn (child d b) R γ s' V' by
    rw [hs', hV']) $$ Hown
  have hm : CsOpenInv j b V s s' V' := .inl ⟨hs', hV'⟩
  clear hs' hV'
  iloeb as IH generalizing %s' %V' %hm Hown HΦ
  rcases s' with _ | ⟨i, y⟩
  · -- nothing at the path: an attempt to create it
    obtain ⟨rfl, hVV⟩ : s = none ∧ V' = V := by
      rcases hm with ⟨h1, h2⟩ | ⟨i, h⟩
      · exact ⟨h1.symm, h2⟩
      · cases s <;> simp [csOpenSt, csNew] at h
    subst V'
    icases csOwn_none _ _ _ _ $$ Hown with ⟨Hv, Ht, %hn⟩
    ihave Ht := (osTree_halves (1 : Qp).half R V).1 $$ Ht
    wp_apply wp_osCallBegin R V (1 : Qp).half.half (1 : Qp).half.half CoPset.subseteq_top
      $$ Hos Ht as %t Ht Hk
    rw [os.file_ty_eq, os.File_ty_eq,
      show (W64 66 ||| W64 524288) = flCreat from by decide]
    (try wp_auto)
    wp_apply wp_osOpenCreate_cs d b N R γ Good Ok V j t V.2.length hN hb hd hn (hok rfl)
      $$ Hos Hinv Hv Ht Hk as %fd %e Hres
    icases Hres with (⟨%i, %he, Hown, Hfd⟩ | ⟨%he, Hst⟩)
    · obtain ⟨rfl, hfd0⟩ := he
      rw [decide_eq_true (show (0 : w64) = W64 0 from rfl)]
      wp_auto
      iStructNamed inner
      iapply wp_fupd
      wp_auto
      ipersist name
      ipersist f
      imodintro
      iapply HΦ
      ileft
      iexists fd, i
      simp only [csOpenSt]
      iframe
      isplitr
      · ipureintro; exact ⟨trivial, hfd0, .inl trivial⟩
      unfold os.ownFile
      iexists inner_ptr
      iframe
      isplitl [] <;> iassumption
    · obtain ⟨he0, rfl⟩ := he
      rw [decide_eq_false (show e ≠ W64 0 from he0)]
      wp_auto
      by_cases he4 : e = W64 4
      · rw [decide_eq_true he4]
        wp_auto
        try rw [os.file_ty_eq]
        try rw [os.File_ty_eq]
        icases Hst with (Hown | ⟨%i, Hown⟩)
        · iapply IH $$ %none %V %(.inl ⟨rfl, rfl⟩) Hown HΦ
        · iapply IH $$ %_ %_ %(.inr ⟨i, rfl⟩) Hown HΦ
      · rw [decide_eq_false he4]
        wp_auto
        unfold os.model.pathError
        wp_apply wp_errno
        iapply HΦ
        iright
        simp only [csOpenSt]
        iframe Hst
        ipureintro; exact ⟨(fun h => by cases h), trivial⟩
  · -- the file `i` at the path: an attempt to open it
    obtain ⟨hsi, heq, -⟩ := csOpenInv_some hs hm
    icases csOwn_tree _ _ _ _ _ _ $$ Hown with ⟨Ht, %hl, Hback⟩
    ihave Ht := (osTree_halves (1 : Qp).half R V').1 $$ Ht
    wp_apply wp_osCallBegin R V' (1 : Qp).half.half (1 : Qp).half.half CoPset.subseteq_top
      $$ Hos Ht as %t Ht Hk
    rw [os.file_ty_eq, os.File_ty_eq,
      show (W64 66 ||| W64 524288) = W64 0x80042 from by decide]
    (try wp_auto)
    wp_apply wp_osOpenFile (child d b) (W64 0x80042) R V' (1 : Qp).half.half (1 : Qp).half.half t _ i
      (by simp only [OpenFlagsOk, O_CREAT, O_TRUNC, O_CLOEXEC]; decide) (by decide) hl
      CoPset.subseteq_top $$ Hos Ht Hk as %fd %e %hres Ht Hfd
    ihave Ht := (osTree_halves (1 : Qp).half R V').2 $$ Ht
    ihave Hown := Hback $$ Ht
    by_cases he0 : e = W64 0
    · subst he0
      rw [decide_eq_true rfl]
      ihave Hfd := (show (if W64 0 = (0 : w64) then osFd (GF := GF) fd (DFrac.own 1)
          (openFd i (W64 0x80042)) else emp) ⊢ osFd fd (DFrac.own 1) ⟨i, true, true⟩
        by rw [openFd_rw]; split
           · iintro H; iexact H
           · exact absurd rfl ‹_›) $$ Hfd
      wp_auto
      iStructNamed inner
      iapply wp_fupd
      wp_auto
      ipersist name
      ipersist f
      imodintro
      have hfd0 : 0 ≤ fd.toInt := by rcases hres with ⟨-, h⟩ | ⟨h, -⟩; exact h; exact absurd rfl h
      iapply HΦ
      ileft
      iexists fd, i
      simp only [← heq]
      iframe
      isplitr
      · ipureintro; exact ⟨by simp, hfd0, hsi⟩
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
        iapply IH $$ %_ %_ %hm Hown HΦ
      · rw [decide_eq_false he4]
        wp_auto
        unfold os.model.pathError
        wp_apply wp_errno
        iapply HΦ
        iright
        isplitr
        · ipureintro; exact ⟨(fun h => by cases h), rfl⟩
        iright
        iexists i
        simp only [← heq]
        iexact Hown

theorem os.File.WriteAt.wp_proof_crashS : os.File.WriteAt.specCrashS (GF := GF) (hG := hG) := by
  intro f fd name dqf sl data dqs off dq d N P R γ Good Ok m bs fa fb hwr hoff hgap hbig hn hn2 hN
    hfz hW
  unfold os.ownFile
  wp_start as ⟨#Hos, #Hinv, ⟨%inner, #Hf, Hfd, #Hn⟩, Hsl, Hosfd, Hown, Hc⟩
  icases csOwnF_wf _ _ $$ Hown with %Hwf
  have hlen : bs.length = m.size := Hwf.1
  unfold os.model.inner
  rw [os.file_ty_eq, os.File_ty_eq]
  ihave #Hf2 := Hf
  iStructNamed Hf2
  icases ownSlice_len sl dqs data $$ Hsl with %Hlen
  icases ownSlice_wf sl dqs data $$ Hsl with %Hwfs
  wp_auto
  have h0 : ¬ (sint.Z off < sint.Z (W64 0)) := by
    rw [show sint.Z (W64 0) = 0 from rfl]; exact Int.not_lt.2 hoff
  rw [decide_eq_false h0]
  wp_auto
  have hl0 : sl.len ≠ W64 0 := by
    intro h; have h1 := Hlen.1; rw [h, show sint.nat (W64 0) = 0 from rfl] at h1; omega
  rw [decide_eq_false hl0]
  wp_pure
  wp_pure
  have hslz : sint.Z sl.len = data.length := by
    have h1 := Hlen.1; have h2 := Hlen.2
    simp only [sint.nat, sint.Z] at h1 h2 ⊢; omega
  -- the invariant: a state the loop reached, `nn` of the bytes written
  obtain ⟨nnv, hnnv⟩ : ∃ nnv : w64, nnv = W64 0 := ⟨_, rfl⟩
  conv in (occs := 4) (#(W64 0) : val) => rw [← hnnv]
  obtain ⟨m', hm'⟩ : ∃ m', m' = m := ⟨_, rfl⟩
  obtain ⟨bs', hbs'⟩ : ∃ bs', bs' = bs := ⟨_, rfl⟩
  have hR : WReach m bs off.toNat data nnv.toNat m' bs' := by
    subst hm' hbs' hnnv; exact .refl
  have hnn : nnv.toNat < data.length := by subst hnnv; exact hn
  have hS : off.toNat + nnv.toNat ≤ m'.size := by subst hnnv hm'; exact hgap
  have hpre : ∀ i < nnv.toNat, (bs'[off.toNat + i]?).map Prod.fst = data[i]? := by
    subst hnnv; intro i hi; exact absurd hi (Nat.not_lt_zero _)
  ihave Hown := (show csOwnF (GF := GF) γ (some (d.ino, ⟨m, bs, fa, fb, .idle⟩)) ⊢
    csOwnF γ (some (d.ino, ⟨m', bs', fa, fb, .idle⟩)) by rw [hm', hbs']) $$ Hown
  clear hm' hbs' hnnv
  iloeb as IH generalizing %m' %bs' %nnv %hR %hnn %hS %hpre Hown Hosfd Hsl Hfd Hc HΦ
  have hNar := hR.narrow hlen hgap
  -- one attempt, from `nn`
  have hnnz : sint.Z nnv = nnv.toNat := by
    simp only [sint.Z]; rw [BitVec.toInt_eq_toNat_of_lt (by omega)]
  have hnnn : sint.nat nnv = nnv.toNat := by simp [sint.nat, hnnz]
  wp_auto
  have hmax : ¬ (sint.Z (W64 1073741824) < sint.Z (sl.len - nnv)) := by
    have hsub : sint.Z (sl.len - nnv) = sint.Z sl.len - sint.Z nnv := by
      have : sint.Z nnv ≤ sint.Z sl.len := by rw [hnnz, hslz]; omega
      have : 0 ≤ sint.Z nnv := by rw [hnnz]; omega
      word
    rw [hsub, hslz, hnnz, show sint.Z (W64 1073741824) = 1073741824 from rfl]; omega
  rw [decide_eq_false hmax]
  wp_auto
  have hsb : 0 ≤ sint.Z nnv ∧ sint.Z nnv ≤ sint.Z sl.len ∧ sint.Z sl.len ≤ sint.Z sl.cap := by
    rw [hnnz, hslz]; omega
  rw [if_pos hsb]
  ihave ⟨Hsl1, Hsl2⟩ := (ownSlice_split_all nnv sl dqs data ⟨by omega, by omega⟩).1 $$ Hsl
  rw [hnnn]
  wp_apply wp_bytes_to_string _ (data.drop nnv.toNat) dqs $$ Hsl2 as Hsl2
  ihave Hsl := (ownSlice_split_all nnv sl dqs data ⟨by omega, by omega⟩).2 $$ [Hsl1 Hsl2]
  · rw [hnnn]; iframe
  have hoffv : (off + nnv).toNat = off.toNat + nnv.toNat := by
    rw [BitVec.toNat_add]; apply Nat.mod_eq_of_lt; omega
  have hoffv' : 0 ≤ (off + nnv).toInt := by
    rw [BitVec.toInt_eq_toNat_of_lt (by rw [hoffv]; omega)]; omega
  have hdl : (data.drop nnv.toNat).length = data.length - nnv.toNat := List.length_drop
  have hgap' : (off + nnv).toNat ≤ m'.size := by rw [hoffv]; exact hS
  have hfz' : (off + nnv).toNat + (data.drop nnv.toNat).length ≤ fa ∨ fb ≤ (off + nnv).toNat := by
    rw [hoffv, hdl]; omega
  have hcl : cfLo m' (off + nnv).toNat = off.toNat + nnv.toNat := by
    rw [hoffv]; unfold cfLo; omega
  have hend : (off + nnv).toNat + (data.drop nnv.toNat).length = off.toNat + data.length := by
    rw [hoffv, hdl]; omega
  -- the cells this attempt takes
  ihave ⟨Hc1, Hc2⟩ := mcellsAny_split m.maps off.toNat (off.toNat + nnv.toNat)
    (off.toNat + data.length) (by omega) (by omega) $$ Hc
  ihave Hc2 := (show mcellsAny (GF := GF) m.maps (off.toNat + nnv.toNat) (off.toNat + data.length) ⊢
    mcellsAny m'.maps (cfLo m' (off + nnv).toNat) ((off + nnv).toNat + (data.drop nnv.toNat).length)
      by rw [hcl, hend, hNar.maps]) $$ Hc2
  have hW1 : ∀ t, Ok (some (d.ino,
      ⟨m', bs', fa, fb, .write t (off + nnv).toNat (data.drop nnv.toNat)⟩)) := by
    intro t; rw [hoffv]; exact (hW _ _ _ hR).2 hnn t
  wp_apply wp_osPWriteStart_cs fd (off + nnv) (data.drop nnv.toNat) dq d N P R γ Good Ok m' bs' fa fb
    hN hwr hoffv' hgap' hfz' hW1 $$ Hos Hinv Hosfd Hown Hc2 as %t Hosfd Hown
  have hW2 : ∀ k ≤ (data.drop nnv.toNat).length, Ok (some (d.ino,
      ⟨finMeta m' (off + nnv).toNat (data.drop nnv.toNat) k,
        finBytes m' bs' (off + nnv).toNat (data.drop nnv.toNat) k, fa, fb, .idle⟩)) := by
    intro k hk; rw [hoffv]
    exact (hW _ _ _ (hR.step k _ hnn (by rw [hdl] at hk; exact hk) (.inl rfl))).1
  wp_apply wp_osPWriteFinish_cs t d.ino (off + nnv).toNat (data.drop nnv.toNat) N P R γ Good Ok m'
    bs' fa fb hN hW2 $$ Hos Hinv Hown as %k %e %hke Hown Hc2
  obtain ⟨hk, hke⟩ := hke
  obtain ⟨hNar', hS', hpre'⟩ := wa_stepS hgap hNar hS hpre hoffv (by omega) hk
  rw [hdl] at hk
  have hRs : ∀ nn', (nn' = nnv.toNat ∨ nn' = nnv.toNat + k) →
      WReach m bs off.toNat data nn' (finMeta m' (off + nnv).toNat (data.drop nnv.toNat) k)
        (finBytes m' bs' (off + nnv).toNat (data.drop nnv.toNat) k) := by
    intro nn' h; rw [hoffv]; exact hR.step k nn' hnn hk h
  -- the cells back
  ihave Hc2 := mcells_any _ _ _ _ $$ Hc2
  ihave Hc2 := (show mcellsAny (GF := GF) m'.maps (cfLo m' (off + nnv).toNat)
      ((off + nnv).toNat + (data.drop nnv.toNat).length) ⊢
    mcellsAny m.maps (off.toNat + nnv.toNat) (off.toNat + data.length)
      by rw [hcl, hend, hNar.maps]) $$ Hc2
  ihave Hc := mcellsAny_merge m.maps off.toNat (off.toNat + nnv.toNat) (off.toNat + data.length)
    (by omega) (by omega) $$ [Hc1 Hc2]
  · iframe
  have hsln : sl.len = W64 data.length := by
    apply BitVec.eq_of_toInt_eq
    simp only [sint.Z] at hslz
    rw [hslz, W64, BitVec.toInt_ofInt, Int.bmod]; split <;> omega
  by_cases he4 : e = W64 4
  · rw [decide_eq_true he4]
    wp_pure
    iapply IH $$ %_ %_ %nnv %(hRs _ (.inl rfl)) %hnn %(by omega)
      %(fun i hi => hpre' i (by omega)) Hown Hosfd Hsl Hfd Hc HΦ
  · rw [decide_eq_false he4]
    wp_auto
    have hWk : (W64 k).toNat = k := by
      simp only [W64]; rw [BitVec.toNat_ofInt]; omega
    have hnk : (nnv + W64 k).toNat = nnv.toNat + k := by
      rw [BitVec.toNat_add, hWk]; exact Nat.mod_eq_of_lt (by omega)
    by_cases hfull : nnv + W64 k = sl.len
    · rw [decide_eq_true hfull]
      wp_auto
      have hfk : nnv.toNat + k = data.length := by
        have := congrArg BitVec.toNat hfull; rw [hnk, hsln] at this
        simp only [W64] at this; rw [BitVec.toNat_ofInt] at this; omega
      by_cases he0 : e = W64 0
      · rw [decide_eq_true he0]
        wp_auto
        iapply HΦ
        iframe
        isplitl []
        · isplitl [] <;> iassumption
        · ipureintro
          exact ⟨_, hRs _ (.inl rfl), .inl ⟨hsln, rfl, by omega, fun i hi => hpre' i (by omega)⟩⟩
      · rw [decide_eq_false he0]
        wp_auto
        simp only [decide_eq_false he0, Bool.not_false]
        wp_auto
        wp_apply os.wp_wrapErrno _ inner name e $$ Hn as %pe
        iapply HΦ
        iframe
        isplitl []
        · isplitl [] <;> iassumption
        · ipureintro
          exact ⟨_, hRs _ (.inl rfl), .inr ⟨rfl, by intro h; cases h⟩⟩
    · rw [decide_eq_false hfull]
      wp_auto
      by_cases he0 : e = W64 0
      · -- a short write: the next attempt from `nn + k`
        rw [decide_eq_true he0]
        simp only [Bool.not_true]
        wp_pure
        have hne : nnv.toNat + k ≠ data.length := by
          intro hc; apply hfull; apply BitVec.eq_of_toNat_eq
          rw [hnk, hsln]; simp only [W64]; rw [BitVec.toNat_ofInt]; omega
        iapply IH $$ %_ %_ %(nnv + W64 k) %(by rw [hnk]; exact hRs _ (.inr rfl))
          %(by rw [hnk]; omega) %(by rw [hnk]; omega)
          %(fun i hi => hpre' i (by rw [hnk] at hi; omega)) Hown Hosfd Hsl Hfd Hc HΦ
      · rw [decide_eq_false he0]
        simp only [Bool.not_false]
        wp_auto
        wp_apply os.wp_wrapErrno _ inner name e $$ Hn as %pe
        iapply HΦ
        iframe
        isplitl []
        · isplitl [] <;> iassumption
        · ipureintro
          exact ⟨_, hRs _ (.inl rfl), .inr ⟨rfl, by intro h; cases h⟩⟩

omit [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt] [go.Semantics] [os.Assumptions] in
theorem ftMeta_grown (m : OsMeta) (sz : Nat) : (ftMeta m sz).grown sz = m.grown sz := by
  cases m; simp only [ftMeta, OsMeta.grown, OsMeta.mk.injEq, _root_.and_true, _root_.true_and]; omega

omit [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt] [go.Semantics] [os.Assumptions] in
theorem ftMeta_ftMeta (m : OsMeta) (sz : Nat) : ftMeta (ftMeta m sz) sz = ftMeta m sz := by
  cases m; simp only [ftMeta, OsMeta.mk.injEq, _root_.and_true, _root_.true_and]; omega

omit [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt] [go.Semantics] [os.Assumptions] in
theorem grown_grown (m : OsMeta) (sz : Nat) : (m.grown sz).grown sz = m.grown sz := by
  simp [OsMeta.grown]

omit [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt] [go.Semantics] [os.Assumptions] in
theorem ftMeta_of_grown (m : OsMeta) (sz : Nat) : ftMeta (m.grown sz) sz = m.grown sz := by
  cases m; simp only [ftMeta, OsMeta.grown, OsMeta.mk.injEq, _root_.and_true, _root_.true_and]; omega

/-- A truncate attempt's outcome, as `wp_osFtruncateFinish_cs` gives it. -/
def truncPost (p : Ino) (γ : GName) (m : OsMeta) (bs : List (w8 × Bool)) (fa fb sz hi : Nat)
    (e : w64) : IProp GF :=
  iprop((⌜e = 0⌝ ∗ csGrownOwn p γ m bs fa fb sz hi) ∨
    (⌜e ≠ 0⌝ ∗ (csGrownOwn p γ m bs fa fb sz hi ∨
      (csOwnF γ (some (p, ⟨ftMeta m sz, bs, fa, fb, .idle⟩)) ∗ mcellsAny m.maps m.size hi))))

theorem os.File.Truncate.wp_proof_crashS : os.File.Truncate.specCrashS (GF := GF) (hG := hG) := by
  intro f fd name dqf sz dq d N P R γ Good Ok m bs fa fb hi hfd0 hwr hsz hgrow hhi hN hT
  unfold os.ownFile
  wp_start as ⟨#Hos, #Hinv, ⟨%inner, #Hf, Hfd, #Hn⟩, Hosfd, Hown, Hc⟩
  unfold os.model.inner
  rw [os.file_ty_eq, os.File_ty_eq]
  ihave #Hf2 := Hf
  iStructNamed Hf2
  wp_auto
  have h1 : ¬ (sint.Z fd < sint.Z (W64 0)) := by
    rw [show sint.Z (W64 0) = 0 from rfl]; exact Int.not_lt.2 hfd0
  rw [decide_eq_false h1]
  wp_auto
  have h2 : ¬ (sint.Z sz < sint.Z (W64 0)) := by
    rw [show sint.Z (W64 0) = 0 from rfl]; exact Int.not_lt.2 hsz
  rw [decide_eq_false h2]
  wp_auto
  have hnil : ∀ zs : List w8, zs.length = sz.toNat - (m.grown sz.toNat).size → zs = [] :=
    fun zs h => List.eq_nil_of_length_eq_zero (by rw [h]; simp [OsMeta.grown])
  have hGo : csGrownOwn (GF := GF) d.ino γ (ftMeta m sz.toNat) bs fa fb sz.toNat hi =
      csGrownOwn d.ino γ m bs fa fb sz.toNat hi := by
    unfold csGrownOwn; rw [ftMeta_grown]; rfl
  ihave HS : (∃ m0, ⌜m0 = m ∨ m0 = ftMeta m sz.toNat⌝ ∗
      csOwnF γ (some (d.ino, ⟨m0, bs, fa, fb, .idle⟩)) ∗ mcellsAny m.maps m.size hi) ∨
      csGrownOwn d.ino γ m bs fa fb sz.toNat hi $$ [Hown Hc]
  · ileft; iexists m; iframe; ipureintro; exact .inl rfl
  iloeb as IH generalizing HS Hosfd Hfd HΦ
  -- the state the attempt starts from, and how its outcome is the spec's
  ihave ⟨%m1, %bs1, %hR1, %hs1, %hmp1, Hown, Hc, Hnorm⟩ : ∃ m1 bs1,
      ⌜TReach m bs sz.toNat m1 bs1⌝ ∗ ⌜m1.size ≤ sz.toNat⌝ ∗ ⌜m1.maps = m.maps⌝ ∗
      csOwnF γ (some (d.ino, ⟨m1, bs1, fa, fb, .idle⟩)) ∗ mcellsAny m1.maps m1.size hi ∗
      (∀ e, truncPost d.ino γ m1 bs1 fa fb sz.toNat hi e -∗
        truncPost d.ino γ m bs fa fb sz.toNat hi e) $$ [HS]
  · icases HS with (⟨%m0, %hm0, Hown, Hc⟩ | Hg)
    · rcases hm0 with rfl | rfl
      · iexists m0, bs; iframe; isplitr; · ipureintro; exact .refl
        isplitr; · ipureintro; exact hgrow
        isplitr; · ipureintro; rfl
        iintro %e H; iexact H
      · iexists (ftMeta m sz.toNat), bs; iframe; isplitr; · ipureintro; exact .ft
        isplitr; · ipureintro; exact hgrow
        isplitr; · ipureintro; rfl
        iintro %e H
        unfold truncPost
        rw [ftMeta_ftMeta, hGo, show (ftMeta m sz.toNat).maps = m.maps from rfl,
          show (ftMeta m sz.toNat).size = m.size from rfl]
        iexact H
    · unfold csGrownOwn
      icases Hg with ⟨%zs, %hzs, Hown, Hz, Hc⟩
      iexists (m.grown sz.toNat), (bs ++ zs.map (·, false))
      iframe Hown
      isplitr; · ipureintro; exact .grown zs hzs.1 hzs.2
      isplitr; · ipureintro; simp [OsMeta.grown]
      isplitr; · ipureintro; rfl
      isplitl [Hc]
      · rw [show (m.grown sz.toNat).maps = m.maps from rfl,
          show (m.grown sz.toNat).size = sz.toNat from rfl]; iexact Hc
      iintro %e H
      unfold truncPost csGrownOwn
      rw [grown_grown, ftMeta_of_grown]
      icases H with (⟨%he, %zs', %hzs', Hown, -, Hc⟩ | ⟨%he, (⟨%zs', %hzs', Hown, -, Hc⟩ | ⟨Hown, Hc⟩)⟩)
      · obtain rfl := hnil zs' hzs'.1
        rw [List.map_nil, List.append_nil]
        ileft; isplitr; · ipureintro; exact he
        iexists zs; iframe; ipureintro; exact hzs
      · obtain rfl := hnil zs' hzs'.1
        rw [List.map_nil, List.append_nil]
        iright; isplitr; · ipureintro; exact he
        ileft; iexists zs; iframe; ipureintro; exact hzs
      · iright; isplitr; · ipureintro; exact he
        ileft; iexists zs; iframe; ipureintro; exact hzs
  have hhi1 : MapsBelow m1.maps hi := by rw [hmp1]; exact hhi
  wp_apply wp_osFtruncateStart_cs fd sz dq d N P R γ Good Ok m1 bs1 fa fb hi hN hwr hsz hs1 hhi1
    (hT _ _ hR1).2 $$ Hos Hinv Hosfd Hown Hc as %t Hosfd Hown
  have hokG : ∀ zs : List w8, zs.length = sz.toNat - m1.size →
      (m1.zero = true → zs = List.replicate (sz.toNat - m1.size) 0) →
      Ok (some (d.ino, ⟨m1.grown sz.toNat, bs1 ++ zs.map (·, false), fa, fb, .idle⟩)) := by
    intro zs hz h0
    rcases hR1 with _ | _ | ⟨zs0, hz0, h00⟩
    · exact (hT _ _ (.grown zs hz h0)).1
    · rw [ftMeta_grown]; exact (hT _ _ (.grown zs hz h0)).1
    · obtain rfl := hnil zs hz
      rw [grown_grown, List.map_nil, List.append_nil]; exact (hT _ _ (.grown zs0 hz0 h00)).1
  have hokF : Ok (some (d.ino, ⟨ftMeta m1 sz.toNat, bs1, fa, fb, .idle⟩)) := by
    rcases hR1 with _ | _ | ⟨zs0, hz0, h00⟩
    · exact (hT _ _ .ft).1
    · rw [ftMeta_ftMeta]; exact (hT _ _ .ft).1
    · rw [ftMeta_of_grown]; exact (hT _ _ (.grown zs0 hz0 h00)).1
  wp_apply wp_osFtruncateFinish_cs t d.ino sz.toNat N P R γ Good Ok m1 bs1 fa fb hi hN hhi1 hokG hokF
    $$ Hos Hinv Hown as %e Hr0
  ihave Hr := Hnorm $$ %e [Hr0]
  · unfold truncPost; iexact Hr0
  unfold truncPost
  by_cases he4 : e = W64 4
  · rw [decide_eq_true he4]
    wp_auto
    icases Hr with (⟨%he, -⟩ | ⟨-, HS⟩)
    · exact absurd (he4 ▸ he) (by decide)
    iapply IH $$ [HS] Hosfd Hfd HΦ
    icases HS with (H | ⟨Hown, Hc⟩)
    · iright; iexact H
    · ileft; iexists (ftMeta m sz.toNat); iframe; ipureintro; exact .inr rfl
  · rw [decide_eq_false he4]
    wp_auto
    icases Hr with (⟨%he, Hg⟩ | ⟨%he, HS⟩)
    · subst he
      rw [show decide ((0 : w64) = W64 0) = true from decide_eq_true rfl]
      simp only [Bool.not_true]
      wp_auto
      iapply HΦ
      iframe
      isplitl []
      · isplitl [] <;> iassumption
      ileft
      iframe
      ipureintro; rfl
    · have he0' : ¬ e = W64 0 := he
      rw [decide_eq_false he0']
      wp_auto
      wp_apply os.wp_wrapErrno _ inner name e $$ Hn as %pe
      iapply HΦ
      iframe
      isplitl []
      · isplitl [] <;> iassumption
      iright
      iframe
      ipureintro; intro h; cases h

end proof

end EtcdGrove
end Perennial
