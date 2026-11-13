/-
The proofs of `Spec/os/Crash.lean`: the models' loops as in `Proof/os/OpenFile.lean`,
`Proof/os/File__WriteAt.lean` and `Proof/syscall/Fdatasync.lean`, over the crash-aware steps of
`Proof/os/CrashOps.lean`. The open's loop keeps what its attempts may have made of the state
(`OpenInv`: a failed attempt may have created the file); a write's loop keeps a state the write
may pass through (`WIn`, `wIn_fin`), whose crashes the caller's `WriteOk` covers (`fileOk_idle`,
`fileOk_flight`), and the bytes written so far (`fin_vals`).
-/
module

public import Spec.os.Crash

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

theorem syscall.Fdatasync.wp_proof_crash [syscall.Assumptions] :
    syscall.Fdatasync.specCrash (GF := GF) (hG := hG) := by
  intro fd dq d N p R γ Good m bs V hN hok
  wp_start as ⟨#Hos, #Hinv, Hfd, Hown⟩
  wp_apply wp_osFsync_cf fd dq d N p R γ Good m bs V hN hok $$ Hos Hinv Hfd Hown as %e Hr Hfd
  iapply wp_errno
  iapply HΦ
  iframe Hfd
  icases Hr with (⟨%he, H⟩ | ⟨%he, H⟩)
  · ileft; iframe; ipureintro; exact he
  · iright; iframe; ipureintro; exact he.1

variable [os.Assumptions]

theorem os.OpenFile.wp_proof_crash [os.file.FieldAssumptions] :
    os.OpenFile.specCrash (GF := GF) (hG := hG) := by
  intro d b perm N R V j γ Good s hb hd hs hN hok
  wp_start as ⟨#Hos, #Hinv, Hown⟩
  obtain ⟨s', hs'⟩ : ∃ s', s' = s := ⟨_, rfl⟩
  obtain ⟨V', hV'⟩ : ∃ V', V' = V := ⟨_, rfl⟩
  ihave Hown := (show cfOwn (GF := GF) (child d b) R γ s V ⊢ cfOwn (child d b) R γ s' V' by
    rw [hs', hV']) $$ Hown
  have hm : OpenInv j b V s s' V' := .inl ⟨hs', hV'⟩
  clear hs' hV'
  iloeb as IH generalizing %s' %V' %hm Hown HΦ
  rcases s' with _ | ⟨i, y⟩
  · -- nothing at the path: an attempt to create it
    obtain ⟨rfl, hVV⟩ : s = none ∧ V' = V := by
      rcases hm with ⟨h1, h2⟩ | ⟨i, h⟩
      · exact ⟨h1.symm, h2⟩
      · cases s <;> simp [openSt] at h
    subst V'
    icases cfOwn_none _ _ _ _ $$ Hown with ⟨Hv, Ht, %hn⟩
    ihave Ht := (osTree_halves (1 : Qp).half R V).1 $$ Ht
    wp_apply wp_osCallBegin R V (1 : Qp).half.half (1 : Qp).half.half CoPset.subseteq_top
      $$ Hos Ht as %t Ht Hk
    rw [os.file_ty_eq, os.File_ty_eq,
      show (W64 66 ||| W64 524288) = flCreat from by decide]
    (try wp_auto)
    wp_apply wp_osOpenCreate_cf d b N R γ Good V j t V.2.length hN hb hd hn (hok rfl)
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
      simp only [openSt]
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
        simp only [openSt]
        iframe Hst
        ipureintro; exact ⟨(fun h => by cases h), trivial⟩
  · -- the file `i` at the path: an attempt to open it
    obtain ⟨hsi, heq, m, bs, rfl⟩ := openInv_some hs hm
    icases cfOwn_tree _ _ _ _ _ _ $$ Hown with ⟨Ht, %hl, Hback⟩
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

theorem os.File.WriteAt.wp_proof_crash : os.File.WriteAt.specCrash (GF := GF) (hG := hG) := by
  intro f fd name dqf sl data dqs off dq d N p R γ Good m bs V hwr hoff hgap hbig hn hn2 hN hW
  unfold os.ownFile
  wp_start as ⟨#Hos, #Hinv, ⟨%inner, #Hf, Hfd, #Hn⟩, Hsl, Hosfd, Hown⟩
  icases cfOwn_wf _ _ _ _ _ $$ Hown with %Hwf
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
  -- the invariant: a state the write may pass through, `nn ≤ w` of the bytes written
  obtain ⟨nnv, hnnv⟩ : ∃ nnv : w64, nnv = W64 0 := ⟨_, rfl⟩
  conv in (occs := 4) (#(W64 0) : val) => rw [← hnnv]
  obtain ⟨m', hm'⟩ : ∃ m', m' = m := ⟨_, rfl⟩
  obtain ⟨bs', hbs'⟩ : ∃ bs', bs' = bs := ⟨_, rfl⟩
  have hIn : WIn m bs off.toNat data m' bs' := by
    subst hm' hbs'; exact wIn_refl _ _ hlen
  obtain ⟨w, hw0⟩ : ∃ w : Nat, w = 0 := ⟨_, rfl⟩
  have hnn : nnv.toNat < data.length := by subst hnnv; exact hn
  have hnw : nnv.toNat ≤ w := by subst hnnv hw0; exact Nat.le_refl _
  have hw : w ≤ data.length := by subst hw0; omega
  have hS : off.toNat + w ≤ m'.size := by subst hw0 hm'; exact hgap
  have hpre : ∀ i < w, (bs'[off.toNat + i]?).map Prod.fst = data[i]? := by
    subst hw0; intro i hi; exact absurd hi (Nat.not_lt_zero _)
  ihave Hown := (show cfOwn (GF := GF) p R γ (some (d.ino, m, bs, none)) V ⊢
    cfOwn p R γ (some (d.ino, m', bs', none)) V by rw [hm', hbs']) $$ Hown
  clear hm' hbs' hnnv hw0
  iloeb as IH generalizing %m' %bs' %nnv %w %hIn %hnn %hnw %hw %hS %hpre Hown Hosfd Hsl
    Hfd HΦ
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
  have hdne : data.drop nnv.toNat ≠ [] := by
    intro h; have := congrArg List.length h; rw [hdl] at this; simp at this; omega
  have hgap' : (off + nnv).toNat ≤ m'.size := by rw [hoffv]; omega
  have hend : (off + nnv).toNat + (data.drop nnv.toNat).length = off.toNat + data.length := by
    rw [hoffv, hdl]; omega
  have hdd : data.drop nnv.toNat = data.drop ((off + nnv).toNat - off.toNat) := by
    rw [hoffv, show off.toNat + nnv.toNat - off.toNat = nnv.toNat by omega]
  have hle : off.toNat ≤ (off + nnv).toNat := by rw [hoffv]; omega
  have hW1 : ∀ t n, FileOk Good (m', bs', some (t, (off + nnv).toNat, data.drop nnv.toNat, n)) :=
    fun t n => fileOk_flight t n hIn hW hlen hle hend hdd hdne hgap'
  wp_apply wp_osPWriteStart_cf fd (off + nnv) (data.drop nnv.toNat) dq d N p R γ Good m' bs' V
    hN hwr hoffv' hgap' hdne hW1 $$ Hos Hinv Hosfd Hown as %t %nst Hosfd Hown
  have hW2 : ∀ k (zs : List Cands), k ≤ (data.drop nnv.toNat).length → (off + nnv).toNat ≤ m'.size →
      FileOk Good (pwPost m' (off + nnv).toNat (data.drop nnv.toNat).length k,
        finBytes m' bs' (off + nnv).toNat (data.drop nnv.toNat) k nst zs, none) :=
    fun k zs hk _ => fileOk_idle (wIn_fin hIn hlen hle hend hdd hdne hgap' hk) hW hlen
  wp_apply wp_osPWriteFinish_cf t d.ino (off + nnv).toNat (data.drop nnv.toNat) nst N p R γ Good m'
    bs' V hN hW2 $$ Hos Hinv Hown as %k %e %zs %hke Hown
  obtain ⟨hk, hke, -, -⟩ := hke
  have hIn' := wIn_fin (k := k) (n := nst) (zs := zs) hIn hlen hle hend hdd hdne hgap' hk
  rw [hdl] at hk
  have hv := fin_vals (n := nst) (zs := zs) hIn.len hS hnw hw hk hpre
  rw [← hoffv] at hv
  obtain ⟨hS', hpre'⟩ := hv
  have hS'' : off.toNat + max w (nnv.toNat + k) ≤
      (pwPost m' (off + nnv).toNat (data.drop nnv.toNat).length k).size := hS'
  have hsln : sl.len = W64 data.length := by
    apply BitVec.eq_of_toInt_eq
    simp only [sint.Z] at hslz
    rw [hslz, W64, BitVec.toInt_ofInt, Int.bmod]; split <;> omega
  by_cases he4 : e = W64 4
  · rw [decide_eq_true he4]
    wp_pure
    iapply IH $$ %_ %_ %nnv %(max w (nnv.toNat + k)) %hIn' %hnn %(by omega) %(by omega) %hS''
      %hpre' Hown Hosfd Hsl Hfd HΦ
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
          refine ⟨hIn', .inl ⟨hsln, rfl, by omega, fun i hi => hpre' i (by omega)⟩⟩
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
          exact ⟨hIn', .inr ⟨rfl, by intro h; cases h⟩⟩
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
        iapply IH $$ %_ %_ %(nnv + W64 k) %(max w (nnv.toNat + k)) %hIn' %(by rw [hnk]; omega)
          %(by rw [hnk]; omega) %(by omega) %hS'' %hpre' Hown Hosfd Hsl Hfd HΦ
      · rw [decide_eq_false he0]
        simp only [Bool.not_false]
        wp_auto
        wp_apply os.wp_wrapErrno _ inner name e $$ Hn as %pe
        iapply HΦ
        iframe
        isplitl []
        · isplitl [] <;> iassumption
        · ipureintro
          exact ⟨hIn', .inr ⟨rfl, by intro h; cases h⟩⟩

end proof

end EtcdGrove
end Perennial
