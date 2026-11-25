/-
The proofs of `Spec/os/CrashStIL.lean`: the models' loops of `Proof/os/CrashStSpec.lean`, over the
local steps of `Proof/os/CrashStIL.lean` with `csInvI`'s accessor (`csI_acc`), the caller's part
`csOwnIL` and the bytes each call takes. A write's loop keeps, beside the state it reached, the
caller's half of the write's range as that state holds it (`finBytes_window`); a truncate's, in
its grown state, the caller's half of the new bytes. Lean-first (no Rocq counterpart).
-/
module

public import Spec.os.CrashStIL
public import Proof.os.CrashStSpec

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

/-- The window `[nn, len)` of a window `[off, off + len)`. -/
theorem window_drop {α : Type} (l : List α) (off len nn : Nat) :
    ((l.drop off).take len).drop nn = (l.drop (off + nn)).take (len - nn) := by
  apply List.ext_getElem?
  intro j
  simp only [List.getElem?_drop, List.getElem?_take]
  by_cases h : j < len - nn
  · rw [if_pos (by omega), if_pos h]
    all_goals first | rfl | (congr 1; omega)
  · rw [if_neg (by omega), if_neg h]

/-- **The range of a write inside the file after an attempt from `off + nn`**: the bytes before
`off + nn` as they were, then the attempt's. -/
theorem finBytes_window (m' : OsMeta) (bs' : List ByteG) (off nn : Nat) (data : List w8) (k n : Nat)
    (hl : bs'.length = m'.size) (hin : off + data.length ≤ m'.size) (hnn : nn ≤ data.length)
    (hk : k ≤ data.length - nn) :
    ((finBytes m' bs' (off + nn) (data.drop nn) k n []).drop off).take data.length =
      ((bs'.drop off).take data.length).take nn ++
        pwBytes m'.size (off + nn) (data.drop nn) k n
          (cfRange m' bs' (off + nn) (data.drop nn).length) [] := by
  have hdl : (data.drop nn).length = data.length - nn := List.length_drop
  have hlo : cfLo m' (off + nn) = off + nn := Nat.min_eq_left (by omega)
  have hps : pwSize m'.size (off + nn) k = m'.size := by unfold pwSize; split <;> omega
  have hpl : (pwBytes m'.size (off + nn) (data.drop nn) k n
      (cfRange m' bs' (off + nn) (data.drop nn).length) []).length = data.length - nn := by
    rw [pwBytes_length, hps, hdl]; omega
  have hA : (((bs'.drop off).take data.length).take nn).length = nn := by
    simp only [List.length_take, List.length_drop]; omega
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_take, List.getElem?_drop]
  have hget := getElem?_tpd bs' (pwBytes m'.size (off + nn) (data.drop nn) k n
    (cfRange m' bs' (off + nn) (data.drop nn).length) []) (cfLo m' (off + nn))
    (cfHi m' (off + nn) (data.drop nn).length) (off + j) (by rw [hl]; omega)
  rw [← finBytes, hlo] at hget
  by_cases h1 : j < data.length
  · rw [if_pos h1, hget]
    by_cases h2 : j < nn
    · rw [if_pos (by omega), List.getElem?_append_left (by omega), List.getElem?_take,
        if_pos h2, List.getElem?_take, if_pos h1, List.getElem?_drop]
    · rw [if_neg (by omega), if_pos (by rw [hpl]; omega), List.getElem?_append_right (by omega),
        hA, show off + j - (off + nn) = j - nn by omega]
  · rw [if_neg h1, List.getElem?_eq_none (by simp only [List.length_append, hA, hpl]; omega)]

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

theorem syscall.Fdatasync.wp_proof_crashIL [syscall.Assumptions] :
    syscall.Fdatasync.specCrashIL (GF := GF) (hG := hG) := by
  intro A _ fd dq d N i γ γa γc Ok a m bs c hi hN hcov hok
  subst hi
  wp_start as ⟨#Hos, #Hinv, Hfd, Hown, Hb⟩
  wp_apply wp_osFsync_L fd dq d N (csInvI (GF := GF) N d.ino γ γa γc Ok) (csTokI γ γa a) (Ok a)
    (csI_acc N d.ino γ γa γc Ok a) m bs c hN hcov hok $$ Hos Hinv Hfd Hown Hb as %e Hr Hfd
  iapply wp_errno
  iapply HΦ
  iframe Hfd
  icases Hr with (⟨%he, H⟩ | ⟨%he, H⟩)
  · ileft; iframe; ipureintro; exact he
  · iright; iframe; ipureintro; exact he.1

theorem golang_org.x.sys.unix.Mmap.wp_proof_crashIL [golang_org.x.sys.unix.Assumptions] :
    golang_org.x.sys.unix.Mmap.specCrashIL (GF := GF) (hG := hG) := by
  intro A _ fd off len prot fl dq d N i γ γa γc Ok a m bs hi hrd hoff hlen hprot hfl hN hok
  subst hi
  wp_start as ⟨#Hos, #Hinv, Hfd, Hown⟩
  have hl : ¬ (sint.Z len ≤ sint.Z (W64 0)) := by
    rw [show sint.Z (W64 0) = 0 from rfl]; simp only [sint.Z]; omega
  rw [decide_eq_false hl]
  wp_auto
  wp_apply wp_osMmap_L fd off len prot fl dq d N (csInvI (GF := GF) N d.ino γ γa γc Ok)
    (csTokI γ γa a) (Ok a) (csI_acc N d.ino γ γa γc Ok a) m bs hN hrd hoff hlen hprot hfl hok
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

theorem golang_org.x.sys.unix.Munmap.wp_proof_crashIL [golang_org.x.sys.unix.Assumptions] :
    golang_org.x.sys.unix.Munmap.specCrashIL (GF := GF) (hG := hG) := by
  intro A _ base len p N γ γa γc Ok a m bs vf hpos hb hN hok
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
    wp_apply wp_osMunmap_L base len len p N (csInvI (GF := GF) N p γ γa γc Ok) (csTokI γ γa a) (Ok a)
      (csI_acc N p γ γa γc Ok a) m bs len.toNat vf hN hb rfl rfl hok
      $$ Hos Hinv Hown Hc as %e Hr
    iapply wp_errno
    iapply HΦ
    iexact Hr

variable [os.Assumptions]

theorem os.File.Sync.wp_proof_crashIL : os.File.Sync.specCrashIL (GF := GF) (hG := hG) := by
  intro A _ f fd name dqf dq d N i γ γa γc Ok a m bs c hi hN hcov hok
  subst hi
  unfold os.ownFile
  wp_start as ⟨#Hos, #Hinv, ⟨%inner, #Hf, Hfd, #Hn, #Hsys⟩, Hosfd, Hown, Hb⟩
  unfold os.model.inner
  rw [os.file_ty_eq, os.File_ty_eq]
  ihave #Hf2 := Hf
  iStructNamed Hf2
  wp_auto
  wp_apply wp_osFdKind fd dq d CoPset.subseteq_top $$ Hos Hosfd as Hosfd
  wp_apply wp_osFsync_L fd dq d N (csInvI (GF := GF) N d.ino γ γa γc Ok) (csTokI γ γa a) (Ok a)
    (csI_acc N d.ino γ γa γc Ok a) m bs c hN hcov hok $$ Hos Hinv Hosfd Hown Hb as %e Hr Hosfd
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
    · (repeat' isplitl []) <;> iassumption
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
    · (repeat' isplitl []) <;> iassumption
    iright
    iframe
    ipureintro; intro h; cases h

theorem os.File.WriteAt.wp_proof_crashIL : os.File.WriteAt.specCrashIL (GF := GF) (hG := hG) := by
  intro A _ f fd name dqf sl data dqs off dq d N i γ γa γc Ok a m bs xs hi hwr hoff hin hbig hn hn2
    hxl hN hW
  subst hi
  unfold os.ownFile
  wp_start as ⟨#Hos, #Hinv, ⟨%inner, #Hf, Hfd, #Hn, #Hsys⟩, Hsl, Hosfd, Hown, Hx, Hc⟩
  icases csOwnL_locOk _ _ _ $$ Hown with %Hlo
  have hlen : bs.length = m.size := Hlo.1.1
  have hgap : off.toNat ≤ m.size := by omega
  -- the caller's bytes are the state's
  imod csOwnIL_agree N d.ino γ γa γc Ok ⟨m, bs, 0, 0, .idle⟩ a ⊤ CoPset.subseteq_top off.toNat
    (DFrac.own (1 : Qp).half) xs (by show off.toNat + xs.length ≤ bs.length; omega)
    $$ Hinv Hown Hx with ⟨Hown, Hx, %hxs⟩
  rw [hxl] at hxs
  subst hxs
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
  obtain ⟨nnv, hnnv⟩ : ∃ nnv : w64, nnv = W64 0 := ⟨_, rfl⟩
  conv in (occs := 4) (#(W64 0) : val) => rw [← hnnv]
  obtain ⟨m', hm'⟩ : ∃ m', m' = m := ⟨_, rfl⟩
  obtain ⟨bs', hbs'⟩ : ∃ bs', bs' = bs := ⟨_, rfl⟩
  have hR : WReach m bs off.toNat data nnv.toNat m' bs' := by
    subst hm' hbs' hnnv; exact .refl
  have hnn : nnv.toNat < data.length := by subst hnnv; exact hn
  have hpre : ∀ i < nnv.toNat, (bs'[off.toNat + i]?).map Prod.fst = data[i]? := by
    subst hnnv; intro i hi; exact absurd hi (Nat.not_lt_zero _)
  ihave Hown := (show csOwnIL (GF := GF) d.ino γ γa ⟨m, bs, 0, 0, .idle⟩ a ⊢
    csOwnIL (GF := GF) d.ino γ γa ⟨m', bs', 0, 0, .idle⟩ a by rw [hm', hbs']) $$ Hown
  ihave Hx := (show osBytes (GF := GF) d.ino off.toNat (DFrac.own (1 : Qp).half)
      ((bs.drop off.toNat).take data.length) ⊢
    osBytes (GF := GF) d.ino off.toNat (DFrac.own (1 : Qp).half)
      ((bs'.drop off.toNat).take data.length) by rw [hbs']) $$ Hx
  clear hm' hbs' hnnv
  iloeb as IH generalizing %m' %bs' %nnv %hR %hnn %hpre Hown Hx Hosfd Hsl Hfd Hc HΦ
  obtain ⟨hNar, hS0, -⟩ := hR.wIn hlen hgap
  have hsz1 := hNar.sz1
  have hl' := hNar.len
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
  have hin' : (off + nnv).toNat + (data.drop nnv.toNat).length ≤ m'.size := by
    rw [hoffv, hdl]; omega
  have hend : (off + nnv).toNat + (data.drop nnv.toNat).length = off.toNat + data.length := by
    rw [hoffv, hdl]; omega
  -- the caller's bytes: those written so far, and this attempt's range
  have hA : (((bs'.drop off.toNat).take data.length).take nnv.toNat).length = nnv.toNat := by
    simp only [List.length_take, List.length_drop]; omega
  ihave ⟨Hx1, Hx2⟩ := (show osBytes (GF := GF) d.ino off.toNat (DFrac.own (1 : Qp).half)
      ((bs'.drop off.toNat).take data.length) ⊢
    osBytes (GF := GF) d.ino off.toNat (DFrac.own (1 : Qp).half)
      (((bs'.drop off.toNat).take data.length).take nnv.toNat) ∗
    osBytes (GF := GF) d.ino (off + nnv).toNat (DFrac.own (1 : Qp).half)
      ((bs'.drop (off + nnv).toNat).take (data.drop nnv.toNat).length) by
      conv => lhs; rw [← List.take_append_drop nnv.toNat ((bs'.drop off.toNat).take data.length)]
      refine (osBytes_appendL _ _ _ _ _).1.trans (sep_mono .rfl ?_)
      rw [hA, window_drop, hoffv, hdl]) $$ Hx
  -- the cells this attempt takes
  ihave ⟨Hc1, Hc2⟩ := mcellsAny_split m.maps off.toNat (off.toNat + nnv.toNat)
    (off.toNat + data.length) (by omega) (by omega) $$ Hc
  ihave Hc2 := (show mcellsAny (GF := GF) m.maps (off.toNat + nnv.toNat) (off.toNat + data.length) ⊢
    mcellsAny m'.maps (off + nnv).toNat ((off + nnv).toNat + (data.drop nnv.toNat).length)
      by rw [hend, hoffv, hNar.maps]) $$ Hc2
  have hdne : data.drop nnv.toNat ≠ [] := by
    intro h; have := congrArg List.length h; rw [hdl] at this; simp at this; omega
  have hW1 : ∀ t n, PwFresh m' bs' (off + nnv).toNat (data.drop nnv.toNat) n →
      Ok a ⟨m', bs', 0, 0, .write t (off + nnv).toNat (data.drop nnv.toNat) n⟩ := by
    intro t n hfr; rw [hoffv] at hfr ⊢; exact (hW _ _ _ hR).2 hnn t n hfr
  wp_apply wp_osPWriteStart_L fd (off + nnv) (data.drop nnv.toNat) dq d N
    (csInvI (GF := GF) N d.ino γ γa γc Ok) (csTokI γ γa a) (Ok a) (csI_acc N d.ino γ γa γc Ok a)
    m' bs' ((bs'.drop (off + nnv).toNat).take (data.drop nnv.toNat).length) hN hwr hoffv' hin' hdne
    (by
      have h1 : (off + nnv).toNat + (data.drop nnv.toNat).length ≤ bs'.length := by
        rw [hl']; exact hin'
      simp only [List.length_take, List.length_drop] at h1 ⊢; omega) hW1
    $$ Hos Hinv Hosfd Hown Hx2 Hc2 as %t %nst %hfrx Hosfd Hown
  have hfr := hfrx.1
  have hps : ∀ k, k ≤ (data.drop nnv.toNat).length → pwSize m'.size (off + nnv).toNat k = m'.size :=
    fun k hk => by unfold pwSize; split <;> omega
  have hW2 : ∀ k, k ≤ (data.drop nnv.toNat).length →
      Ok a ⟨pwPostK true m' (off + nnv).toNat (data.drop nnv.toNat) k nst,
        finBytes m' bs' (off + nnv).toNat (data.drop nnv.toNat) k nst [], 0, 0, .idle⟩ := by
    intro k hk; rw [hoffv] at hfr ⊢
    exact (hW _ _ _ (hR.step k _ nst [] hnn (by rw [hdl] at hk; exact hk) (.inl rfl)
      (by rw [← hoffv, hps k hk]; simp) (fun _ _ _ h => absurd h (Nat.not_lt_zero _)) hfr)).1
  wp_apply wp_osPWriteFinish_L t d.ino (off + nnv).toNat (data.drop nnv.toNat) nst N
    (csInvI (GF := GF) N d.ino γ γa γc Ok) (csTokI γ γa a) (Ok a) (csI_acc N d.ino γ γa γc Ok a)
    m' bs' hN hl' hin' hW2 $$ Hos Hinv Hown as %k %e %hke Hown Hy Hc2
  obtain ⟨hk, hke, hzt, hzl⟩ := hke
  rw [hdl] at hk
  have hv := fin_vals (n := nst) (zs := []) hl' (by omega : off.toNat + nnv.toNat ≤ m'.size)
    (Nat.le_refl _) (by omega) hk hpre
  rw [← hoffv, Nat.max_eq_right (Nat.le_add_right _ _)] at hv
  obtain ⟨-, hpre'⟩ := hv
  have hRs : ∀ nn', (nn' = nnv.toNat + k ∨ nn' = nnv.toNat) →
      WReach m bs off.toNat data nn' (pwPostK true m' (off + nnv).toNat (data.drop nnv.toNat) k nst)
        (finBytes m' bs' (off + nnv).toNat (data.drop nnv.toNat) k nst []) := by
    intro nn' h; rw [hoffv] at hzl hfr ⊢
    exact hR.step k nn' nst [] hnn hk h (by rw [← hoffv, hps k (by rw [hdl]; exact hk)]; simp)
      (fun _ _ _ h => absurd h (Nat.not_lt_zero _)) hfr
  -- the caller's bytes of the range, as the new state holds them
  ihave Hx := (show osBytes (GF := GF) d.ino off.toNat (DFrac.own (1 : Qp).half)
      (((bs'.drop off.toNat).take data.length).take nnv.toNat) ∗
    osBytes (GF := GF) d.ino (off + nnv).toNat (DFrac.own (1 : Qp).half)
      (pwBytes m'.size (off + nnv).toNat (data.drop nnv.toNat) k nst
        (cfRange m' bs' (off + nnv).toNat (data.drop nnv.toNat).length) []) ⊢
    osBytes (GF := GF) d.ino off.toNat (DFrac.own (1 : Qp).half)
      (((finBytes m' bs' (off + nnv).toNat (data.drop nnv.toNat) k nst []).drop off.toNat).take
        data.length) by
      rw [hoffv, finBytes_window m' bs' off.toNat nnv.toNat data k nst hl' (by omega) (by omega)
        (by omega)]
      refine BIBase.Entails.trans ?_ (osBytes_appendL _ _ _ _ _).2
      rw [hA]) $$ [Hx1 Hy]
  · iframe
  -- the cells back
  ihave Hc2 := mcells_any _ _ _ _ $$ Hc2
  ihave Hc2 := (show mcellsAny (GF := GF) m'.maps (off + nnv).toNat
      ((off + nnv).toNat + (data.drop nnv.toNat).length) ⊢
    mcellsAny m.maps (off.toNat + nnv.toNat) (off.toNat + data.length)
      by rw [hend, hoffv, hNar.maps]) $$ Hc2
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
    iapply IH $$ %_ %_ %nnv %(hRs _ (.inr rfl)) %hnn %(fun i hi => hpre' i (by omega))
      Hown Hx Hosfd Hsl Hfd Hc HΦ
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
        · (repeat' isplitl []) <;> iassumption
        · ipureintro
          exact ⟨_, by trivial, hRs _ (.inl rfl), .inl ⟨hsln, rfl, hfk, fun i hi => hpre' i (by omega)⟩⟩
      · rw [decide_eq_false he0]
        wp_auto
        simp only [decide_eq_false he0, Bool.not_false]
        wp_auto
        wp_apply os.wp_wrapErrno _ inner name e $$ Hn as %pe
        iapply HΦ
        iframe
        isplitl []
        · (repeat' isplitl []) <;> iassumption
        · ipureintro
          exact ⟨_, by trivial, hRs _ (.inl rfl), .inr ⟨rfl, by intro h; cases h⟩⟩
    · rw [decide_eq_false hfull]
      wp_auto
      by_cases he0 : e = W64 0
      · rw [decide_eq_true he0]
        simp only [Bool.not_true]
        wp_pure
        have hne : nnv.toNat + k ≠ data.length := by
          intro hc; apply hfull; apply BitVec.eq_of_toNat_eq
          rw [hnk, hsln]; simp only [W64]; rw [BitVec.toNat_ofInt]; omega
        iapply IH $$ %_ %_ %(nnv + W64 k) %(by rw [hnk]; exact hRs _ (.inl rfl))
          %(by rw [hnk]; omega) %(fun i hi => hpre' i (by rw [hnk] at hi; omega))
          Hown Hx Hosfd Hsl Hfd Hc HΦ
      · rw [decide_eq_false he0]
        simp only [Bool.not_false]
        wp_auto
        wp_apply os.wp_wrapErrno _ inner name e $$ Hn as %pe
        iapply HΦ
        iframe
        isplitl []
        · (repeat' isplitl []) <;> iassumption
        · ipureintro
          exact ⟨_, by trivial, hRs _ (.inl rfl), .inr ⟨rfl, by intro h; cases h⟩⟩

theorem os.File.Truncate.wp_proof_crashIL : os.File.Truncate.specCrashIL (GF := GF) (hG := hG) := by
  intro A _ f fd name dqf sz dq d N i γ γa γc Ok a m bs hi hfd0 hwr hsz hgrow hN hT
  subst hi
  unfold os.ownFile
  wp_start as ⟨#Hos, #Hinv, ⟨%inner, #Hf, Hfd, #Hn, #Hsys⟩, Hosfd, Hown, Hc⟩
  icases csOwnL_locOk _ _ _ $$ Hown with %Hlo
  have hlen : bs.length = m.size := Hlo.1.1
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
  ihave HS : (∃ m0, ⌜m0 = m ∨ m0 = m.announce (min m.size sz.toNat) (rsHi true m.size sz.toNat) sz.toNat⌝ ∗
      csOwnIL (GF := GF) d.ino γ γa ⟨m0, bs, 0, 0, .idle⟩ a ∗ mcellsAny m.maps m.size (rsHi true m.size sz.toNat)) ∨
      (∃ n m0, ⌜m0 = m ∨ m0 = m.announce (min m.size sz.toNat) (rsHi true m.size sz.toNat) sz.toNat⌝ ∗
        csGrownL (GF := GF) (csTokI γ γa a) d.ino m0 bs sz.toNat n) $$ [Hown Hc]
  · ileft; iexists m; iframe; ipureintro; exact .inl rfl
  iloeb as IH generalizing HS Hosfd Hfd HΦ
  icases HS with (⟨%m0, %hm0, Hown, Hc⟩ | ⟨%n0, %m0, %hm0, Hg⟩)
  · -- not grown yet
    have hsz0 : m0.size = m.size := by rcases hm0 with rfl | rfl <;> simp
    have hmp0 : m0.maps = m.maps := by rcases hm0 with rfl | rfl <;> simp
    have hR0 : TReach m bs sz.toNat m0 bs := by rcases hm0 with rfl | rfl; exact .refl; exact .ann
    ihave Hc := (show mcellsAny (GF := GF) m.maps m.size (rsHi true m.size sz.toNat) ⊢
      mcellsAny m0.maps m0.size (rsHi true m0.size sz.toNat) by rw [hsz0, hmp0]) $$ Hc
    wp_apply wp_osFtruncateStart_L fd sz dq d N (csInvI (GF := GF) N d.ino γ γa γc Ok)
      (csTokI γ γa a) (Ok a) (csI_acc N d.ino γ γa γc Ok a) m0 bs hN hwr hsz
      (by rw [hsz0]; exact hgrow) (hT _ _ hR0).2 $$ Hos Hinv Hosfd Hown Hc as %t %n Hosfd Hown
    have hpost : rsPost true m0 sz.toNat sz.toNat = rsPost true m sz.toNat sz.toNat := by
      rcases hm0 with rfl | rfl
      · rfl
      · exact os.rsPost_announce _ _ _ _
    have hann : m0.announce (min m0.size sz.toNat) (rsHi true m0.size sz.toNat) sz.toNat =
        m.announce (min m.size sz.toNat) (rsHi true m.size sz.toNat) sz.toNat := by
      rw [hsz0]; rcases hm0 with rfl | rfl
      · rfl
      · exact os.announce_idem _ _ _ _
    have hokG : ∀ zs : List Cands, zs.length = sz.toNat - m0.size →
        Ok a ⟨rsPost true m0 sz.toNat sz.toNat, bs ++ grownBytes zs n, 0, 0, .idle⟩ := by
      intro zs hz; rw [hpost]; rw [hsz0] at hz; exact (hT _ _ (.grown n zs hz)).1
    have hokF : Ok a ⟨m0.announce (min m0.size sz.toNat) (rsHi true m0.size sz.toNat) sz.toNat,
        bs, 0, 0, .idle⟩ := by rw [hann]; exact (hT _ _ .ann).1
    wp_apply wp_osFtruncateFinish_L t d.ino sz.toNat n N (csInvI (GF := GF) N d.ino γ γa γc Ok)
      (csTokI γ γa a) (Ok a) (csI_acc N d.ino γ γa γc Ok a) m0 bs hN (by rw [hsz0]; exact hlen)
      (by rw [hsz0]; exact hgrow) hokG hokF $$ Hos Hinv Hown as %e Hr
    by_cases he4 : e = W64 4
    · rw [decide_eq_true he4]
      wp_auto
      iapply IH $$ [Hr] Hosfd Hfd HΦ
      icases Hr with (⟨%he, Hg⟩ | ⟨-, (Hg | ⟨Hown, Hc⟩)⟩)
      · iright; iexists n, m0; iframe; ipureintro; exact hm0
      · iright; iexists n, m0; iframe; ipureintro; exact hm0
      · ileft; iexists _; rw [hann]; iframe Hown
        isplitr
        · ipureintro; exact .inr rfl
        ihave Hc := mcells_any (GF := GF) _ _ _ _ $$ Hc
        iapply (show mcellsAny (GF := GF) m0.maps m0.size (rsHi true m0.size sz.toNat) ⊢
          mcellsAny m.maps m.size (rsHi true m.size sz.toNat) by rw [hsz0, hmp0]); iexact Hc
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
        · (repeat' isplitl []) <;> iassumption
        ileft
        isplitr; · ipureintro; rfl
        iexists n, m0; iframe; ipureintro; exact hm0
      · have he0' : ¬ e = W64 0 := he
        rw [decide_eq_false he0']
        wp_auto
        wp_apply os.wp_wrapErrno _ inner name e $$ Hn as %pe
        iapply HΦ
        iframe
        isplitl []
        · (repeat' isplitl []) <;> iassumption
        iright
        isplitr; · ipureintro; intro h; cases h
        icases HS with (Hg | ⟨Hown, Hc⟩)
        · ileft; iexists n, m0; iframe; ipureintro; exact hm0
        · iright; rw [hann]; iframe Hown
          ihave Hc := mcells_any (GF := GF) _ _ _ _ $$ Hc
          iapply (show mcellsAny (GF := GF) m0.maps m0.size (rsHi true m0.size sz.toNat) ⊢
            mcellsAny m.maps m.size (rsHi true m.size sz.toNat) by rw [hsz0, hmp0]); iexact Hc
  · -- grown: a further attempt is a resize to the size the file has
    have hsz0 : m0.size = m.size := by rcases hm0 with rfl | rfl <;> simp
    have hpost : rsPost true m0 sz.toNat sz.toNat = rsPost true m sz.toNat sz.toNat := by
      rcases hm0 with rfl | rfl
      · rfl
      · exact os.rsPost_announce _ _ _ _
    iunfold csGrownL at Hg
    icases Hg with ⟨%zs, %hzs, Hown, Hz, Hcs⟩
    have hR0 : TReach m bs sz.toNat (rsPost true m0 sz.toNat sz.toNat) (bs ++ grownBytes zs n0) := by
      rw [hpost]; exact .grown n0 zs (by rw [hzs.1, hsz0])
    have hgsz : (rsPost true m0 sz.toNat sz.toNat).size = sz.toNat := rfl
    have hgmaps : (rsPost true m0 sz.toNat sz.toNat).maps = m0.maps := by simp [rsPost]
    have hRR : rsHi true sz.toNat sz.toNat = rsHi true m0.size sz.toNat := by
      simp only [rsHi, if_true, Nat.max_self, Nat.max_eq_right (show m0.size ≤ sz.toNat by omega)]
    have hR1 := le_rsHi true m0.size sz.toNat
    have hgl : (bs ++ grownBytes zs n0).length = sz.toNat := by
      simp only [grownBytes, List.length_append, List.length_map, hlen, hzs.1]; omega
    icases (mcells_split (GF := GF) m0.maps m0.size sz.toNat (rsHi true m0.size sz.toNat) _
      (by omega) (by omega)).1 $$ Hcs with ⟨Hc1, Hc2⟩
    ihave Hc0 := mcells_any (GF := GF) _ _ _ _ $$ Hc2
    ihave Hc0 := (show mcellsAny (GF := GF) m0.maps sz.toNat (rsHi true m0.size sz.toNat) ⊢
      mcellsAny (rsPost true m0 sz.toNat sz.toNat).maps (rsPost true m0 sz.toNat sz.toNat).size
        (rsHi true (rsPost true m0 sz.toNat sz.toNat).size sz.toNat) by rw [hgsz, hgmaps, hRR]) $$ Hc0
    wp_apply wp_osFtruncateStart_L fd sz dq d N (csInvI (GF := GF) N d.ino γ γa γc Ok)
      (csTokI γ γa a) (Ok a) (csI_acc N d.ino γ γa γc Ok a) _ _ hN hwr hsz
      (by rw [hgsz]; exact Nat.le_refl _) (hT _ _ hR0).2 $$ Hos Hinv Hosfd Hown Hc0 as %t %n Hosfd Hown
    have hokG : ∀ zs' : List Cands, zs'.length = sz.toNat - (rsPost true m0 sz.toNat sz.toNat).size →
        Ok a ⟨rsPost true (rsPost true m0 sz.toNat sz.toNat) sz.toNat sz.toNat,
          (bs ++ grownBytes zs n0) ++ grownBytes zs' n, 0, 0, .idle⟩ := by
      intro zs' hz
      rw [hgsz, Nat.sub_self] at hz
      rw [List.eq_nil_of_length_eq_zero hz, show grownBytes [] n = [] from rfl, List.append_nil,
        os.rsPost_rsPost]
      exact (hT _ _ hR0).1
    have hokF : Ok a ⟨(rsPost true m0 sz.toNat sz.toNat).announce
        (min (rsPost true m0 sz.toNat sz.toNat).size sz.toNat)
        (rsHi true (rsPost true m0 sz.toNat sz.toNat).size sz.toNat)
        sz.toNat, bs ++ grownBytes zs n0, 0, 0, .idle⟩ := by
      rw [os.announce_rsPost]; exact (hT _ _ hR0).1
    wp_apply wp_osFtruncateFinish_L t d.ino sz.toNat n N (csInvI (GF := GF) N d.ino γ γa γc Ok)
      (csTokI γ γa a) (Ok a) (csI_acc N d.ino γ γa γc Ok a) _ _ hN (by rw [hgsz]; exact hgl)
      (by rw [hgsz]; try exact Nat.le_refl _) hokG hokF $$ Hos Hinv Hown as %e Hr
    -- the state is the grown one again
    ihave Hown : csOwnIL (GF := GF) d.ino γ γa ⟨rsPost true m0 sz.toNat sz.toNat,
        bs ++ grownBytes zs n0, 0, 0, .idle⟩ a ∗
        mcells m0.maps sz.toNat (rsHi true m0.size sz.toNat) (rsCell sz.toNat) $$ [Hr]
    · unfold csGrownL
      icases Hr with (⟨-, ⟨%zs', %hzs', Hown, -, Hc⟩⟩ | ⟨-, (⟨%zs', %hzs', Hown, -, Hc⟩ | ⟨Hown, Hc⟩)⟩)
      · rw [hgsz, Nat.sub_self] at hzs'
        rw [List.eq_nil_of_length_eq_zero hzs'.1, show grownBytes [] n = [] from rfl, List.append_nil,
          os.rsPost_rsPost] at *
        rw [hgsz, hgmaps, hRR]
        iframe
      · rw [hgsz, Nat.sub_self] at hzs'
        rw [List.eq_nil_of_length_eq_zero hzs'.1, show grownBytes [] n = [] from rfl, List.append_nil,
          os.rsPost_rsPost] at *
        rw [hgsz, hgmaps, hRR]
        iframe
      · have hA : (rsPost true m0 sz.toNat sz.toNat).announce (min sz.toNat sz.toNat)
            (rsHi true sz.toNat sz.toNat) sz.toNat = rsPost true m0 sz.toNat sz.toNat :=
          os.announce_rsPost true m0 sz.toNat
        isplitl [Hown]
        · iapply (show csOwnL (GF := GF) (csTokI γ γa a) d.ino ⟨(rsPost true m0 sz.toNat sz.toNat).announce
              (min sz.toNat sz.toNat) (rsHi true sz.toNat sz.toNat) sz.toNat,
              bs ++ grownBytes zs n0, 0, 0, .idle⟩ ⊢
            csOwnIL (GF := GF) d.ino γ γa ⟨rsPost true m0 sz.toNat sz.toNat,
              bs ++ grownBytes zs n0, 0, 0, .idle⟩ a by rw [hA]; try exact .rfl)
          iexact Hown
        · rw [← hRR, touch_maps]
          iapply (mcells_congr_iff (GF := GF) _ _ _ _ _ (fun i h1 _ => by
            simp only [rsOld, rsCell]; rw [if_neg (by omega), if_neg (by omega)])).1 $$ Hc
    icases Hown with ⟨Hown, Hc2⟩
    ihave Hcs := (mcells_split (GF := GF) m0.maps m0.size sz.toNat (rsHi true m0.size sz.toNat) _
      (by omega) (by omega)).2 $$ [Hc1 Hc2]
    · iframe
    ihave Hg : csGrownL (GF := GF) (csTokI γ γa a) d.ino m0 bs sz.toNat n0 $$ [Hown Hz Hcs]
    · unfold csGrownL; iexists zs; iframe; ipureintro; exact hzs
    by_cases he4 : e = W64 4
    · rw [decide_eq_true he4]
      wp_auto
      iapply IH $$ [Hg] Hosfd Hfd HΦ
      iright; iexists n0, m0; iframe; ipureintro; exact hm0
    · rw [decide_eq_false he4]
      wp_auto
      by_cases he0 : e = W64 0
      · rw [decide_eq_true he0]
        simp only [Bool.not_true]
        wp_auto
        iapply HΦ
        iframe
        isplitl []
        · (repeat' isplitl []) <;> iassumption
        ileft
        isplitr; · ipureintro; rfl
        iexists n0, m0; iframe; ipureintro; exact hm0
      · rw [decide_eq_false he0]
        wp_auto
        wp_apply os.wp_wrapErrno _ inner name e $$ Hn as %pe
        iapply HΦ
        iframe
        isplitl []
        · (repeat' isplitl []) <;> iassumption
        iright
        isplitr; · ipureintro; intro h; cases h
        ileft; iexists n0, m0; iframe; ipureintro; exact hm0

end proof

end EtcdGrove
end Perennial
