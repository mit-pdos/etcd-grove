/-
The proofs of `Spec/os/CrashSt.lean`: the models' loops as in `Proof/os/Crash.lean`,
`Proof/os/File__Truncate.lean`, `Proof/os/File__Sync.lean` and `Proof/golang_org/x/sys/unix/*.lean`,
over the steps of `Proof/os/CrashStOps.lean`. A write's loop keeps a state it reached (`WReach`),
a truncate's one of the three `TReach` states. Lean-first (no Rocq counterpart).
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

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

theorem syscall.Fdatasync.wp_proof_crashS [syscall.Assumptions] :
    syscall.Fdatasync.specCrashS (GF := GF) (hG := hG) := by
  intro fd dq d N γ Ok m H F T fa fb hd hH hF hc hN hok hokF
  wp_start as ⟨#Hos, #Hinv, Hfd, Hown⟩
  wp_apply wp_osFsync_cs fd dq d N γ Ok m H F T fa fb hH hF hd hc hN hok hokF $$ Hos Hinv Hfd Hown
    as %e Hr Hfd
  iapply wp_errno
  iapply HΦ
  iframe Hfd
  icases Hr with (⟨%he, H⟩ | ⟨%he, H⟩)
  · ileft; iframe; ipureintro; exact he
  · iright; iframe; ipureintro; exact he.1

theorem golang_org.x.sys.unix.Mmap.wp_proof_crashS [golang_org.x.sys.unix.Assumptions] :
    golang_org.x.sys.unix.Mmap.specCrashS (GF := GF) (hG := hG) := by
  intro fd off len prot fl dq d N γ Ok m bs fa fb hrd hoff hlen hprot hfl hN hok
  wp_start as ⟨#Hos, #Hinv, Hfd, Hown⟩
  have hl : ¬ (sint.Z len ≤ sint.Z (W64 0)) := by
    rw [show sint.Z (W64 0) = 0 from rfl]; simp only [sint.Z]; omega
  rw [decide_eq_false hl]
  wp_auto
  wp_apply wp_osMmap_cs fd off len prot fl dq d N γ Ok m bs fa fb hN hrd hoff hlen hprot hfl hok
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
  intro base len p N γ Ok m bs fa fb vf hpos hb hN hok
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
    wp_apply wp_osMunmap_cs base len len p N γ Ok m bs fa fb len.toNat vf hN hb rfl rfl hok
      $$ Hos Hinv Hown Hc as %e Hr
    iapply wp_errno
    iapply HΦ
    iexact Hr

variable [os.Assumptions]

theorem os.File.Sync.wp_proof_crashS : os.File.Sync.specCrashS (GF := GF) (hG := hG) := by
  intro f fd name dqf dq d N γ Ok m H F T fa fb hd hH hF hc hN hok hokF
  unfold os.ownFile
  wp_start as ⟨#Hos, #Hinv, ⟨%inner, #Hf, Hfd, #Hn⟩, Hosfd, Hown⟩
  unfold os.model.inner
  rw [os.file_ty_eq, os.File_ty_eq]
  ihave #Hf2 := Hf
  iStructNamed Hf2
  wp_auto
  wp_apply wp_osFsync_cs fd dq d N γ Ok m H F T fa fb hH hF hd hc hN hok hokF
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
  intro path perm N γ Ok s hs hN hok
  wp_start as ⟨#Hos, #Hinv, Hown⟩
  obtain ⟨s', hs'⟩ : ∃ s', s' = s := ⟨_, rfl⟩
  ihave Hown := (show csOwn path γ s ⊢ csOwn path γ s' by rw [hs']) $$ Hown
  have hm2 : s' = s ∨ s' = csOpen s := .inl hs'
  clear hs'
  iloeb as IH generalizing %s' %hm2 Hown HΦ
  rw [os.file_ty_eq, os.File_ty_eq,
    show (W64 66 ||| W64 524288) = W64 0x80042 from by decide]
  have hs2 : s' = none ∨ ∃ m bs fa fb, s' = some ⟨m, bs, fa, fb, .idle⟩ := by
    rcases hm2 with rfl | rfl
    · exact hs
    · rcases hs with rfl | ⟨m, bs, fa, fb, rfl⟩
      · exact .inr ⟨_, _, _, _, rfl⟩
      · exact .inr ⟨_, _, _, _, rfl⟩
  have hos : csOpen s' = csOpen s := by
    rcases hm2 with rfl | rfl
    · rfl
    · rcases hs with rfl | ⟨m, bs, fa, fb, rfl⟩ <;> rfl
  wp_apply wp_osOpen_cs path (W64 0x80042) N γ Ok s' hs2 hN
    (by simp only [OpenFlagsOk, O_CREAT, O_TRUNC, O_CLOEXEC]; decide) (by decide) (by decide)
    (by rw [hos]; exact hok) $$ Hos Hinv Hown as %fd %e %s2 %hres Hown Hfd
  have hfd : openFd path (W64 0x80042) = ⟨path, true, true⟩ := by
    simp [openFd, O_WRONLY, O_RDONLY]
  by_cases he0 : e = W64 0
  · subst he0
    rw [decide_eq_true rfl]
    ihave Hfd := (show (if W64 0 = (0 : w64) then osFd (GF := GF) fd (DFrac.own 1)
        (openFd path (W64 524354)) else emp) ⊢ osFd fd (DFrac.own 1) ⟨path, true, true⟩
      by rw [hfd]; split
         · iintro H; iexact H
         · exact absurd rfl ‹_›) $$ Hfd
    wp_auto
    iStructNamed inner
    iapply wp_fupd
    wp_auto
    ipersist name
    ipersist f
    imodintro
    obtain ⟨-, hfd0, hs2e⟩ := hres.resolve_right (fun h => h.1 rfl)
    rw [hos] at hs2e
    subst hs2e
    iapply HΦ
    ileft
    iexists fd
    iframe
    isplitr
    · ipureintro; exact ⟨rfl, hfd0⟩
    unfold os.ownFile
    iexists inner_ptr
    iframe
    isplitl [] <;> iassumption
  · rw [decide_eq_false he0]
    iclear Hfd
    have hm3 : s2 = s ∨ s2 = csOpen s := by
      rcases hres with ⟨h, -⟩ | ⟨-, -, h | h⟩
      · exact absurd h he0
      · rw [h]; exact hm2
      · rw [h, hos]; exact .inr rfl
    wp_auto
    by_cases he4 : e = W64 4
    · rw [decide_eq_true he4]
      wp_auto
      try rw [os.file_ty_eq]
      try rw [os.File_ty_eq]
      try rw [show (W64 66 ||| W64 524288) = W64 0x80042 from by decide]
      iapply IH $$ %_ %hm3 Hown HΦ
    · rw [decide_eq_false he4]
      wp_auto
      unfold os.model.pathError
      wp_apply wp_errno
      iapply HΦ
      iright
      isplitr
      · ipureintro; exact ⟨(fun h => by cases h), rfl⟩
      iexists s2
      iframe
      ipureintro; exact hm3

theorem csOwn_wf' (p : GoString) (γ : GName) (s : CState) :
    csOwn (GF := GF) p γ s ⊢ csOwn (GF := GF) p γ s ∗ ⌜CsWf s⌝ := by
  unfold csOwn; iintro ⟨H1, H2, %h⟩; iframe; ipureintro; exact ⟨h, h⟩

theorem os.File.WriteAt.wp_proof_crashS : os.File.WriteAt.specCrashS (GF := GF) (hG := hG) := by
  intro f fd name dqf sl data dqs off dq d N γ Ok m bs fa fb hwr hoff hn hn2 hN hfz hW
  unfold os.ownFile
  wp_start as ⟨#Hos, #Hinv, ⟨%inner, #Hf, Hfd, #Hn⟩, Hsl, Hosfd, Hown, Hc⟩
  icases csOwn_wf' _ _ _ $$ Hown with ⟨Hown, %Hwf⟩
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
  -- the invariant: a narrowing of the file
  obtain ⟨m', hm'⟩ : ∃ m', m' = m := ⟨_, rfl⟩
  obtain ⟨bs', hbs'⟩ : ∃ bs', bs' = bs := ⟨_, rfl⟩
  have hR : WReach m bs off.toNat data m' bs' := by
    subst hm' hbs'; exact .refl
  ihave Hown := (show csOwn (GF := GF) d.path γ (some ⟨m, bs, fa, fb, .idle⟩) ⊢
    csOwn d.path γ (some ⟨m', bs', fa, fb, .idle⟩) by rw [hm', hbs']) $$ Hown
  clear hm' hbs'
  iloeb as IH generalizing %m' %bs' %hR Hown Hosfd Hsl Hfd Hc HΦ
  have hNar := hR.narrow hlen
  -- one attempt
  wp_auto
  have hslz : sint.Z sl.len = data.length := by
    have h1 := Hlen.1; have h2 := Hlen.2
    simp only [sint.nat, sint.Z] at h1 h2 ⊢; omega
  have hz : sl.len - W64 0 = sl.len := BitVec.sub_zero sl.len
  have hmax : ¬ (sint.Z (W64 1073741824) < sint.Z (sl.len - W64 0)) := by
    rw [hz, hslz, show sint.Z (W64 1073741824) = 1073741824 from rfl]; omega
  rw [decide_eq_false hmax]
  wp_auto
  have hsb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z sl.len ∧ sint.Z sl.len ≤ sint.Z sl.cap := by
    rw [show sint.Z (W64 0) = 0 from rfl]; omega
  rw [if_pos hsb, ← slice_slice_trivial, show off + W64 0 = off from BitVec.add_zero off]
  wp_apply wp_bytes_to_string sl data dqs $$ Hsl as Hsl
  have hlo : cfLo m off.toNat ≤ cfLo m' off.toNat := by have := hNar.size; unfold cfLo; omega
  have hlo2 : cfLo m' off.toNat ≤ off.toNat + data.length := by unfold cfLo; omega
  ihave ⟨Hc1, Hc2⟩ := mcellsAny_split m.maps (cfLo m off.toNat) (cfLo m' off.toNat)
    (off.toNat + data.length) hlo hlo2 $$ Hc
  ihave Hc2 := (show mcellsAny (GF := GF) m.maps (cfLo m' off.toNat) (off.toNat + data.length) ⊢
    mcellsAny m'.maps (cfLo m' off.toNat) (off.toNat + data.length) by rw [hNar.maps]) $$ Hc2
  wp_apply wp_osPWriteStart_cs fd off data dq d N γ Ok m' bs' fa fb hN hwr hoff hfz
    (hW _ _ hR).2 $$ Hos Hinv Hosfd Hown Hc2 as %t Hosfd Hown
  wp_apply wp_osPWriteFinish_cs t d.path off.toNat data N γ Ok m' bs' fa fb hN
    (fun k hk => (hW _ _ (hR.step k hk)).1) $$ Hos Hinv Hown
    as %k %e %hke Hown Hc2
  obtain ⟨hk, hke⟩ := hke
  have hR' := hR.step k hk
  ihave Hc2 := mcells_any _ _ _ _ $$ Hc2
  ihave Hc2 := (show mcellsAny (GF := GF) m'.maps (cfLo m' off.toNat) (off.toNat + data.length) ⊢
    mcellsAny m.maps (cfLo m' off.toNat) (off.toNat + data.length) by rw [hNar.maps]) $$ Hc2
  ihave Hc := mcellsAny_merge m.maps (cfLo m off.toNat) (cfLo m' off.toNat)
    (off.toNat + data.length) hlo hlo2 $$ [Hc1 Hc2]
  · iframe
  by_cases he4 : e = W64 4
  · rw [decide_eq_true he4]
    wp_pure
    iapply IH $$ %_ %_ %hR' Hown Hosfd Hsl Hfd Hc HΦ
  · rw [decide_eq_false he4]
    wp_auto
    have hsln : sl.len = W64 data.length := by
      apply BitVec.eq_of_toInt_eq
      simp only [sint.Z] at hslz
      rw [hslz, W64, BitVec.toInt_ofInt, Int.bmod]; split <;> omega
    rcases hke with ⟨rfl, rfl⟩ | he0
    · rw [decide_eq_true (by rw [hsln]; exact BitVec.zero_add _)]
      wp_auto
      iapply HΦ
      iframe
      isplitl []
      · isplitl [] <;> iassumption
      · ipureintro
        refine ⟨hR', .inl ⟨hsln, rfl, ?_, fun i hi => finBytes_data hNar.len hn i hi⟩⟩
        show off.toNat + data.length ≤ pwSize m'.size off.toNat data.length
        unfold pwSize; split <;> omega
    · have he0' : ¬ e = W64 0 := he0
      by_cases hkl : W64 0 + W64 ↑k = sl.len
      · rw [decide_eq_true hkl]
        wp_auto
        rw [decide_eq_false he0']
        wp_auto
        simp only [decide_eq_false he0', Bool.not_false]
        wp_auto
        wp_apply os.wp_wrapErrno _ inner name e $$ Hn as %pe
        iapply HΦ
        iframe
        isplitl []
        · isplitl [] <;> iassumption
        · ipureintro
          exact ⟨hR', .inr ⟨rfl, by intro h; cases h⟩⟩
      · rw [decide_eq_false hkl]
        wp_auto
        simp only [decide_eq_false he0', Bool.not_false]
        wp_auto
        wp_apply os.wp_wrapErrno _ inner name e $$ Hn as %pe
        iapply HΦ
        iframe
        isplitl []
        · isplitl [] <;> iassumption
        · ipureintro
          exact ⟨hR', .inr ⟨rfl, by intro h; cases h⟩⟩

omit [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt] [go.Semantics] [os.Assumptions] in
theorem ftMeta_grown (m : OsMeta) (sz : Nat) : (ftMeta m sz).grown sz = m.grown sz := by
  cases m; simp only [ftMeta, OsMeta.grown, OsMeta.mk.injEq, _root_.and_true, _root_.true_and]; omega

omit [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt] [go.Semantics] [os.Assumptions] in
theorem ftMeta_ftMeta (m : OsMeta) (sz : Nat) : ftMeta (ftMeta m sz) sz = ftMeta m sz := by
  cases m; simp only [ftMeta, OsMeta.mk.injEq, _root_.and_true, _root_.true_and]; omega

omit [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt] [go.Semantics] [os.Assumptions] in
theorem grown_grown (m : OsMeta) (sz : Nat) : (m.grown sz).grown sz = m.grown sz := by
  simp [OsMeta.grown]

omit [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt] [go.Semantics] [os.Assumptions] in
theorem ftMeta_of_grown (m : OsMeta) (sz : Nat) : ftMeta (m.grown sz) sz = m.grown sz := by
  cases m; simp only [ftMeta, OsMeta.grown, OsMeta.mk.injEq, _root_.and_true, _root_.true_and]; omega

/-- A truncate attempt's outcome, as `wp_osFtruncateFinish_cs` gives it. -/
def truncPost (p : GoString) (γ : GName) (m : OsMeta) (bs : List (w8 × Bool)) (fa fb sz hi : Nat)
    (e : w64) : IProp GF :=
  iprop((⌜e = 0⌝ ∗ csGrownOwn p γ m bs fa fb sz hi) ∨
    (⌜e ≠ 0⌝ ∗ (csGrownOwn p γ m bs fa fb sz hi ∨
      (csOwn p γ (some ⟨ftMeta m sz, bs, fa, fb, .idle⟩) ∗ mcellsAny m.maps m.size hi))))

theorem os.File.Truncate.wp_proof_crashS : os.File.Truncate.specCrashS (GF := GF) (hG := hG) := by
  intro f fd name dqf sz dq d N γ Ok m bs fa fb hi hfd0 hwr hsz hgrow hhi hN hT
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
  have hrep : bs ++ List.replicate (sz.toNat - m.size) ((0 : w8), false) ++
      List.replicate (sz.toNat - (m.grown sz.toNat).size) ((0 : w8), false) =
      bs ++ List.replicate (sz.toNat - m.size) ((0 : w8), false) := by
    simp [OsMeta.grown]
  have hGo : csGrownOwn (GF := GF) d.path γ (ftMeta m sz.toNat) bs fa fb sz.toNat hi =
      csGrownOwn d.path γ m bs fa fb sz.toNat hi := by
    unfold csGrownOwn; rw [ftMeta_grown]; rfl
  ihave HS : (∃ m0, ⌜m0 = m ∨ m0 = ftMeta m sz.toNat⌝ ∗
      csOwn d.path γ (some ⟨m0, bs, fa, fb, .idle⟩) ∗ mcellsAny m.maps m.size hi) ∨
      csGrownOwn d.path γ m bs fa fb sz.toNat hi $$ [Hown Hc]
  · ileft; iexists m; iframe; ipureintro; exact .inl rfl
  iloeb as IH generalizing HS Hosfd Hfd HΦ
  -- the state the attempt starts from, and how its outcome is the spec's
  ihave ⟨%m1, %bs1, %hR1, %hs1, %hmp1, Hown, Hc, Hnorm⟩ : ∃ m1 bs1,
      ⌜TReach m bs sz.toNat m1 bs1⌝ ∗ ⌜m1.size ≤ sz.toNat⌝ ∗ ⌜m1.maps = m.maps⌝ ∗
      csOwn d.path γ (some ⟨m1, bs1, fa, fb, .idle⟩) ∗ mcellsAny m1.maps m1.size hi ∗
      (∀ e, truncPost d.path γ m1 bs1 fa fb sz.toNat hi e -∗
        truncPost d.path γ m bs fa fb sz.toNat hi e) $$ [HS]
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
      icases Hg with ⟨Hown, Hz, Hc⟩
      iexists (m.grown sz.toNat), (bs ++ List.replicate (sz.toNat - m.size) ((0 : w8), false))
      iframe Hown
      isplitr; · ipureintro; exact .grown
      isplitr; · ipureintro; simp [OsMeta.grown]
      isplitr; · ipureintro; rfl
      isplitl [Hc]
      · rw [show (m.grown sz.toNat).maps = m.maps from rfl,
          show (m.grown sz.toNat).size = sz.toNat from rfl]; iexact Hc
      iintro %e H
      unfold truncPost csGrownOwn
      rw [grown_grown, ftMeta_of_grown, hrep]
      icases H with (⟨%he, Hown, -, Hc⟩ | ⟨%he, (⟨Hown, -, Hc⟩ | ⟨Hown, Hc⟩)⟩)
      · ileft; iframe; ipureintro; exact he
      · iright; isplitr; · ipureintro; exact he
        ileft; iframe
      · iright; isplitr; · ipureintro; exact he
        ileft; iframe
  have hhi1 : MapsBelow m1.maps hi := by rw [hmp1]; exact hhi
  wp_apply wp_osFtruncateStart_cs fd sz dq d N γ Ok m1 bs1 fa fb hi hN hwr hsz hs1 hhi1
    (hT _ _ hR1).2 $$ Hos Hinv Hosfd Hown Hc as %t Hosfd Hown
  have hokG : Ok (some ⟨m1.grown sz.toNat, bs1 ++ List.replicate (sz.toNat - m1.size) ((0 : w8), false),
      fa, fb, .idle⟩) := by
    rcases hR1 with _ | _ | _
    · exact (hT _ _ .grown).1
    · rw [ftMeta_grown]; exact (hT _ _ .grown).1
    · rw [grown_grown, hrep]; exact (hT _ _ .grown).1
  have hokF : Ok (some ⟨ftMeta m1 sz.toNat, bs1, fa, fb, .idle⟩) := by
    rcases hR1 with _ | _ | _
    · exact (hT _ _ .ft).1
    · rw [ftMeta_ftMeta]; exact (hT _ _ .ft).1
    · rw [ftMeta_of_grown]; exact (hT _ _ .grown).1
  wp_apply wp_osFtruncateFinish_cs t d.path sz.toNat N γ Ok m1 bs1 fa fb hi hN hhi1 hokG hokF
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
