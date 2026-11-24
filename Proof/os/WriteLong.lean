/-
The proof of `Spec/os/WriteLong.lean` (`os.File.WriteAt.specLong`). Up to `maxRW` (1 GiB) it is
`File__WriteAt.lean`'s spec (one chunk: `A = len(b)`, `PwOut` is `PwOutA` with everything
announced, `pwPostE` is `pwPost`). Past 1 GiB the model's loop writes chunks of at most `maxRW`
from where the last attempt stopped, each announcing its own range; the proof is
`File__WriteAt.lean`'s Löb induction with the invariant generalized to "a write of `data` that
announced its first `A` bytes, wrote its first `j`, and whose last whole chunk ended at `E`"
(`osMeta (pwPostE m off A j E)`, `PwOutA m off data A j xs ys`, `PwCutE off len j E`), the chunk's
end joined from the two branches of the model's `max` (`wp_if_join`), the slice, bytes and cells
split in three around each chunk, and the pure steps of `WriteLongStep.lean` (2026-11-14,
`wal-wlong1`). Lean-first.
-/
module

public import Proof.os.WriteLongStep
public import Perennial.Golang.Theory.IfJoin
public import Proof.os.ForLoeb

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

/-- `PwOut` is `PwOutA` with everything announced. -/
theorem os.PwOut.pwOutA {m : OsMeta} {off : Nat} {data : List w8} {j : Nat} {xs ys : List ByteG}
    (h : os.PwOut m off data j xs ys) : os.PwOutA m off data data.length j xs ys := by
  refine ⟨h.1, fun i hi => ?_⟩
  obtain ⟨h1, c0, extra, h2, h3, h4, h5⟩ := h.2 i hi
  exact ⟨h1, c0, extra, h2, fun _ => h3, h4, h5⟩

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions]

theorem wl_osBytes_split3 (i : Ino) (o0 L n : Nat) (ys : List ByteG) (hL : L ≤ ys.length) :
    osBytes (GF := GF) i o0 (DFrac.own 1) ys ⊢
      osBytes i o0 (DFrac.own 1) (ys.take L) ∗
      osBytes i (o0 + L) (DFrac.own 1) ((ys.drop L).take n) ∗
      osBytes i (o0 + L + ((ys.drop L).take n).length) (DFrac.own 1) ((ys.drop L).drop n) := by
  conv => lhs; rw [← List.take_append_drop L ys, ← List.take_append_drop n (ys.drop L)]
  unfold osBytes
  iintro H
  ihave ⟨H1, H2⟩ := (bytesG_append _ _ _ _ _ _).1 $$ H
  rw [List.length_take, Nat.min_eq_left hL]
  ihave ⟨H2, H3⟩ := (bytesG_append _ _ _ _ _ _).1 $$ H2
  iframe

theorem wl_osBytes_merge3 (i : Ino) (o0 L : Nat) (a b c xsw : List ByteG) (hL : a.length = L)
    (hc : c = [] ∨ xsw.length = b.length) :
    osBytes (GF := GF) i o0 (DFrac.own 1) a ∗ osBytes i (o0 + L) (DFrac.own 1) b ∗
      osBytes i (o0 + L + xsw.length) (DFrac.own 1) c ⊢
      osBytes i o0 (DFrac.own 1) (a ++ b ++ c) := by
  unfold osBytes
  iintro ⟨H1, H2, H3⟩
  rcases hc with rfl | hc
  · rw [List.append_nil]
    iapply (bytesG_append _ _ _ _ _ _).2
    rw [hL]
    iframe
  · rw [List.append_assoc]
    iapply (bytesG_append _ _ _ _ _ _).2
    rw [hL]
    iframe H1
    iapply (bytesG_append _ _ _ _ _ _).2
    rw [← hc]
    iframe

set_option maxHeartbeats 2000000 in
theorem os.File.WriteAt.wp_proof_long : os.File.WriteAt.specLong (GF := GF) (hG := hG) := by
  intro f fd name dqf sl data dqs off dq d m xs hwr hoff hgap hbig hn hlo hxl
  by_cases hsmall : data.length ≤ 0x40000000
  · iintro %Φ Hpre HΦ
    iapply (os.File.WriteAt.wp_ino (GF := GF) (hG := hG) f fd name dqf sl data dqs off dq d m xs
      hwr hoff hgap hbig hn hsmall hxl) $$ Hpre
    iintro !> %n %err ⟨Hf, Hsl, Hfd, %j, %ys, %Hr, Hm, Hbs, Hmc, Hok⟩
    obtain ⟨hj, hout, hcut, hres⟩ := Hr
    iapply HΦ
    iframe Hf Hsl Hfd
    iexists j, data.length, (if j = data.length then data.length else 0), ys
    rw [pwPostE_one m off.toNat data.length j hj]
    iframe Hm Hbs Hmc Hok
    ipureintro
    refine ⟨hj, Nat.le_refl _, fun _ => rfl, by split <;> omega, fun h => by rw [if_pos h],
      os.PwOut.pwOutA hout, .inl hcut, hres⟩
  · -- past `maxRW`: the chunked loop (see the file header)
    have hbig' : 0x40000000 < data.length := by omega
    have hmin0 : min off.toNat m.size = off.toNat := Nat.min_eq_left hgap
    unfold os.ownFile
    wp_start as ⟨#Hinv, ⟨%inner, #Hf, Hfd, #Hn, #Hnb⟩, Hsl, Hosfd, Hm, Hbs, Hc⟩
    ihave #Hf2 := Hf
    iStructNamed Hf2
    icases ownSlice_len sl dqs data $$ Hsl with %Hlen
    icases ownSlice_wf sl dqs data $$ Hsl with %Hwf
    try wp_auto
    have h0 : ¬ (sint.Z off < sint.Z (W64 0)) := by
      rw [show sint.Z (W64 0) = 0 from rfl]; exact Int.not_lt.2 hoff
    rw [decide_eq_false h0]
    try wp_auto
    have hl0 : sl.len ≠ W64 0 := by
      intro h; have h1 := Hlen.1; rw [h, show sint.nat (W64 0) = 0 from rfl] at h1; omega
    rw [decide_eq_false hl0]
    try wp_auto
    try simp only [os.modelMaxRW]
    have hslz : sint.Z sl.len = data.length := by
      have h1 := Hlen.1; have h2 := Hlen.2
      simp only [sint.nat, sint.Z] at h1 h2 ⊢; omega
    -- the invariant: the file as a write that announced its first `A` bytes and wrote its first
    -- `j` left it, `nn ≤ j` of them written, the last whole chunk ending at `E`
    obtain ⟨nnv, hnnv⟩ : ∃ nnv : w64, nnv = W64 0 := ⟨_, rfl⟩
    ihave Hnnp : (nn_ptr ↦ nnv : IProp GF) $$ [nn]
    · rw [hnnv]; iexact nn
    obtain ⟨mj, hmj⟩ : ∃ mj, mj = m := ⟨_, rfl⟩
    ihave Hm := (show osMeta (GF := GF) d.ino (DFrac.own 1) m ⊢ osMeta d.ino (DFrac.own 1) mj by
      rw [hmj]) $$ Hm
    obtain ⟨ys, hy⟩ : ∃ ys, ys = xs := ⟨_, rfl⟩
    ihave Hbs := (show osBytes (GF := GF) d.ino off.toNat (DFrac.own 1) xs ⊢
      osBytes d.ino off.toNat (DFrac.own 1) ys by rw [hy]) $$ Hbs
    obtain ⟨j, hj0⟩ : ∃ j : Nat, j = 0 := ⟨_, rfl⟩
    obtain ⟨A, hA0⟩ : ∃ A : Nat, A = 0 := ⟨_, rfl⟩
    obtain ⟨E, hE0⟩ : ∃ E : Nat, E = 0 := ⟨_, rfl⟩
    have hnn0 : nnv.toNat = 0 := by subst hnnv; rfl
    have hnn : nnv.toNat ≤ j := by omega
    have hnl : nnv.toNat < data.length := by omega
    have hj : j ≤ A := by omega
    have hAl : A ≤ data.length := by omega
    have hAn : A ≤ nnv.toNat + 0x40000000 := by omega
    have hEj : E ≤ j := by omega
    have hjA : j = A → E = A := by omega
    have hinv : (A = 0 ∧ mj = m) ∨ (0 < A ∧ mj = os.pwPostE m off.toNat A j E) := .inl ⟨hA0, hmj⟩
    have hout : os.PwOutA m off.toNat data A j xs ys := by
      rw [hA0, hj0, hy]; exact pwOutA_zero m off.toNat data xs hxl
    have hcj : os.PwCutE off.toNat data.length j E := by
      left; unfold PwCut; exact ⟨.inl hj0, .inl hj0⟩
    clear hmj hy hj0 hA0 hE0 hnnv hnn0
    wp_for_bind
    iloeb as IH generalizing %j %A %E %nnv %mj %ys %hnn %hnl %hj %hAl %hAn %hEj %hjA %hinv %hout %hcj
      Hm Hbs Hc Hosfd Hsl Hfd HΦ
    wp_for_step
    -- one attempt, from `nn`, of the chunk `[nn, nn + c)`
    have hnnz : sint.Z nnv = nnv.toNat := by
      simp only [sint.Z]; rw [BitVec.toInt_eq_toNat_of_lt (by omega)]
    have hnnn : sint.nat nnv = nnv.toNat := by simp [sint.nat, hnnz]
    try wp_auto
    have hsub : sint.Z (sl.len - nnv) = data.length - nnv.toNat := by
      have : sint.Z nnv ≤ sint.Z sl.len := by rw [hnnz, hslz]; omega
      have : 0 ≤ sint.Z nnv := by rw [hnnz]; omega
      have : sint.Z (sl.len - nnv) = sint.Z sl.len - sint.Z nnv := by word
      rw [this, hslz, hnnz]
    obtain ⟨A', hA'd⟩ : ∃ A' : Nat, A' = min data.length (nnv.toNat + 0x40000000) := ⟨_, rfl⟩
    have hAA' : A ≤ A' := by omega
    have hnA' : nnv.toNat < A' := by omega
    have hA'l : A' ≤ data.length := by omega
    have h2p30 : sint.Z (W64 1073741824) = 1073741824 := rfl
    wp_if_join (fun v => iprop(⌜v = executeVal⌝ ∗ ∃ mx : w64, max_ptr ↦ mx ∗ ⌜sint.Z mx = A'⌝))
    · try wp_auto
      isplitr
      · ipureintro; rfl
      iexists (nnv + W64 1073741824)
      iframe
      ipureintro
      rw [hsub, h2p30] at Hif
      rw [wl_add30 nnv (by rw [hnnz]; omega) (by rw [hnnz]; omega), hnnz]; omega
    · try wp_auto
      isplitr
      · ipureintro; rfl
      iexists sl.len
      iframe
      ipureintro
      rw [hsub, h2p30] at Hif
      rw [hslz]; omega
    iintro %v ⟨%hv, %mx, Hmax, %hmxz⟩
    subst hv
    try wp_auto
    have hmxt := wl_toNat_of_sintZ mx A' hmxz
    have hmxn : sint.nat mx = A' := by simp [sint.nat, hmxz]
    have hsb : 0 ≤ sint.Z nnv ∧ sint.Z nnv ≤ sint.Z mx ∧ sint.Z mx ≤ sint.Z sl.cap := by
      rw [hnnz, hmxz]; omega
    rw [if_pos hsb]
    have hsb2 : 0 ≤ sint.Z nnv ∧ sint.Z nnv ≤ sint.Z mx ∧ sint.Z mx ≤ sint.Z sl.len := by
      rw [hnnz, hmxz, hslz]; omega
    ihave ⟨Hsl1, Hsl2, Hsl3⟩ := (ownSlice_slice nnv mx sl dqs data hsb2).1 $$ Hsl
    rw [hnnn, hmxn]
    wp_apply wp_bytes_to_string _ (subslice nnv.toNat A' data) dqs $$ Hsl2 as Hsl2
    ihave Hsl := (ownSlice_slice nnv mx sl dqs data hsb2).2 $$ [Hsl1 Hsl2 Hsl3]
    · rw [hnnn, hmxn]; iframe
    have hdc : subslice nnv.toNat A' data = (data.drop nnv.toNat).take (A' - nnv.toNat) := by
      simp only [subslice, List.drop_take]
    rw [hdc]
    -- the bytes and cells this attempt takes
    have hmsz : mj.size = pwSize m.size off.toNat j := by
      rcases hinv with ⟨hA0, rfl⟩ | ⟨-, rfl⟩
      · have : j = 0 := by omega
        subst this; simp [pwSize]
      · rfl
    have hmaps : mj.maps = m.maps := by
      rcases hinv with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · rfl
      · exact pwPostE_maps _ _ _ _ _
    have hyl : ys.length = min (off.toNat + data.length) (pwSize m.size off.toNat j) - off.toNat :=
      hout.1
    have hS := pwSize_off m.size off.toNat j nnv.toNat hgap hnn
    have hnny : nnv.toNat ≤ ys.length := by rw [hyl]; omega
    ihave ⟨Hbs1, Hbs2, Hbs3⟩ := wl_osBytes_split3 d.ino off.toNat nnv.toNat (A' - nnv.toNat) ys hnny
      $$ Hbs
    ihave ⟨Hc1, Hc2⟩ := mcellsAny_split m.maps off.toNat (off.toNat + nnv.toNat)
      (off.toNat + data.length) (by omega) (by omega) $$ Hc
    ihave ⟨Hc2, Hc3⟩ := mcellsAny_split m.maps (off.toNat + nnv.toNat) (off.toNat + A')
      (off.toNat + data.length) (by omega) (by omega) $$ Hc2
    have hoffv : (off + nnv).toNat = off.toNat + nnv.toNat := by
      rw [BitVec.toNat_add]; apply Nat.mod_eq_of_lt; omega
    have hoffv' : 0 ≤ (off + nnv).toInt := by
      rw [BitVec.toInt_eq_toNat_of_lt (by rw [hoffv]; omega)]; omega
    have hdl : ((data.drop nnv.toNat).take (A' - nnv.toNat)).length = A' - nnv.toNat := by
      simp only [List.length_take, List.length_drop]; omega
    have hdne : (data.drop nnv.toNat).take (A' - nnv.toNat) ≠ [] := by
      intro h; have := congrArg List.length h; rw [hdl] at this; simp at this; omega
    have hy2 : ((ys.drop nnv.toNat).take (A' - nnv.toNat)).length =
        min (A' - nnv.toNat) (ys.length - nnv.toNat) := by
      simp only [List.length_take, List.length_drop]
    have hend : off.toNat + nnv.toNat + (A' - nnv.toNat) = off.toNat + A' := by omega
    try wp_auto
    wp_stub os.fsPWrite.impl
    wp_apply wp_osPWriteStart fd (off + nnv) ((data.drop nnv.toNat).take (A' - nnv.toNat)) dq d mj
      ((ys.drop nnv.toNat).take (A' - nnv.toNat))
      CoPset.subseteq_top hwr hoffv' (by rw [hoffv, hmsz]; exact hS) hdne
      (by rw [hoffv, hdl, hy2, hyl, hmsz]; omega)
      $$ Hinv Hosfd Hm [Hbs2] [Hc2] as %t %nst %- Hosfd Ht
    · rw [hoffv]; iexact Hbs2
    · rw [hoffv, hdl, hmaps, hend]
      iexact Hc2
    wp_apply wp_osPWriteFinishW t d.ino (off + nnv).toNat ((data.drop nnv.toNat).take (A' - nnv.toNat))
      mj ((ys.drop nnv.toNat).take (A' - nnv.toNat)) nst CoPset.subseteq_top $$ Hinv Ht
      as %k %e %zs %hke %hpc Hm Hbs2 Hc2 %hneW
    obtain ⟨hk, hke, -, -⟩ := hke
    rw [hdl] at hk
    have hpc' : PwCut (off.toNat + nnv.toNat) (A' - nnv.toNat) k := by
      rw [hoffv, hdl] at hpc; exact hpc
    have hcj' := pwCutE_step off.toNat data.length nnv.toNat j A A' E k hcj hnn hj hAA' hnA' hk hjA
      hpc'
    -- the file as a write that announced `A'` and wrote `max j (nn + k)` left it
    have hmeta : pwPost mj (off + nnv).toNat ((data.drop nnv.toNat).take (A' - nnv.toNat)).length k =
        os.pwPostE m off.toNat A' (max j (nnv.toNat + k)) (if k = A' - nnv.toNat then A' else E) := by
      rw [hoffv, hdl]
      rcases hinv with ⟨hA0, hm⟩ | ⟨hA0, hm⟩ <;> rw [hm]
      · have h1 : j = 0 := by omega
        have h2 : nnv.toNat = 0 := by omega
        have h3 : E = 0 := by omega
        rw [h1, h2, h3, Nat.add_zero, Nat.sub_zero, Nat.zero_add, Nat.max_eq_right (Nat.zero_le _)]
        exact pwPostE_base m off.toNat A' k (by omega)
      · exact pwPostE_step m off.toNat A j E nnv.toNat A' k hgap hlo hnn hj hA0 hAA' hnA' hk hEj
    rw [hmeta]
    have hrest := pwBytes_rest mj.size off.toNat nnv.toNat (A' - nnv.toNat) k nst data.length
      ((data.drop nnv.toNat).take (A' - nnv.toNat)) ys zs (by rw [hyl, hmsz])
      (by rw [hmsz]; exact hS) (by omega) hdl
    rw [hoffv]
    ihave Hbs := wl_osBytes_merge3 d.ino off.toNat nnv.toNat (ys.take nnv.toNat)
      (pwBytes mj.size (off.toNat + nnv.toNat) ((data.drop nnv.toNat).take (A' - nnv.toNat)) k nst
        ((ys.drop nnv.toNat).take (A' - nnv.toNat)) zs)
      ((ys.drop nnv.toNat).drop (A' - nnv.toNat)) ((ys.drop nnv.toNat).take (A' - nnv.toNat))
      (by rw [List.length_take, Nat.min_eq_left hnny]) hrest $$ [Hbs1 Hbs2 Hbs3]
    · iframe
    rw [hmsz]
    ihave Hc2 := mcells_any _ _ _ _ $$ Hc2
    ihave Hc := mcellsAny_merge m.maps (off.toNat + nnv.toNat) (off.toNat + A')
      (off.toNat + data.length) (by omega) (by omega) $$ [Hc2 Hc3]
    · rw [hdl, hmaps, hend]
      iframe
    ihave Hc := mcellsAny_merge m.maps off.toNat (off.toNat + nnv.toNat) (off.toNat + data.length)
      (by omega) (by omega) $$ [Hc1 Hc]
    · iframe
    have hys' := pwOutA_step m off.toNat nnv.toNat data A j A' k nst xs ys zs hgap hnn hj hAA' hA'l
      hnA' hk hxl hout
    have hj' : max j (nnv.toNat + k) ≤ A' := by omega
    have hEj' : (if k = A' - nnv.toNat then A' else E) ≤ max j (nnv.toNat + k) := by
      split <;> omega
    have hjA' : max j (nnv.toNat + k) = A' → (if k = A' - nnv.toNat then A' else E) = A' := by
      split <;> omega
    have hinv' : (A' = 0 ∧ os.pwPostE m off.toNat A' (max j (nnv.toNat + k))
          (if k = A' - nnv.toNat then A' else E) = m) ∨
        (0 < A' ∧ os.pwPostE m off.toNat A' (max j (nnv.toNat + k))
            (if k = A' - nnv.toNat then A' else E) =
          os.pwPostE m off.toNat A' (max j (nnv.toNat + k)) (if k = A' - nnv.toNat then A' else E)) :=
      .inr ⟨by omega, rfl⟩
    have hnn1 : nnv.toNat ≤ max j (nnv.toNat + k) := by omega
    have hAn1 : A' ≤ nnv.toNat + 0x40000000 := by omega
    have hsln := wl_len_eq sl data.length hslz (by omega)
    by_cases he4 : e = W64 4
    · rw [decide_eq_true he4]
      try wp_auto
      wp_for_post
      inext
      iapply IH $$ %(max j (nnv.toNat + k)) %A' %_ %nnv %_ %_ %hnn1 %hnl %hj' %hA'l %hAn1
        %hEj' %hjA' %hinv' %hys' %hcj' Hm Hbs Hc Hosfd Hsl Hfd HΦ [$] [$] [$] [$] [$] [$] [$] [$]
    · rw [decide_eq_false he4]
      try wp_auto
      have hWk : (W64 k).toNat = k := wl_W64_toNat k (by omega)
      have hnk : (nnv + W64 k).toNat = nnv.toNat + k := by
        rw [BitVec.toNat_add, hWk]; exact Nat.mod_eq_of_lt (by omega)
      have hlenN : (W64 data.length).toNat = data.length := wl_W64_toNat _ (by omega)
      by_cases hfull : nnv + W64 k = sl.len
      · rw [decide_eq_true hfull]
        try wp_auto
        have hfk : nnv.toNat + k = data.length := by
          have := congrArg BitVec.toNat hfull; rw [hnk, hsln, hlenN] at this; exact this
        by_cases he0 : e = W64 0
        · rw [decide_eq_true he0]
          try wp_auto
          ihave #Hokn := (EtcdGrove.fmtErrorOkOrNil_nil (GF := GF))
          wp_for_post
          iapply HΦ
          iframe Hokn
          iframe
          isplitl []
          · isplitl [] <;> (try isplitl []) <;> iassumption
          · ipureintro
            exact ⟨hj', hA'l, fun h => absurd h (by omega), hEj', hjA', hys', hcj',
              .inl ⟨by omega, hsln, rfl⟩⟩
        · rw [decide_eq_false he0]
          try wp_auto
          simp only [decide_eq_false he0, Bool.not_false]
          try wp_auto
          wp_apply os.wp_wrapErrno_ok _ inner name e he0 $$ Hn as %pe #Hok
          ihave #Hokn := EtcdGrove.fmtErrorOkOrNil_of _ $$ Hok
          wp_for_post
          iapply HΦ
          iframe Hokn
          iframe
          isplitl []
          · isplitl [] <;> (try isplitl []) <;> iassumption
          · ipureintro
            exact ⟨hj', hA'l, fun h => absurd h (by omega), hEj', hjA', hys', hcj',
              .inr ⟨rfl, (by intro h; cases h), (hneW he0).imp_right (fun h => by rw [hoffv] at h; omega)⟩⟩
      · rw [decide_eq_false hfull]
        try wp_auto
        by_cases he0 : e = W64 0
        · -- a short write, or a whole chunk: the next attempt from `nn + k`
          rw [decide_eq_true he0]
          simp only [Bool.not_true]
          wp_pure
          have hnk' : nnv.toNat + k ≠ data.length := by
            intro hc; apply hfull; apply BitVec.eq_of_toNat_eq
            rw [hnk, hsln, hlenN]; exact hc
          have hnl' : (nnv + W64 k).toNat < data.length := by rw [hnk]; omega
          have hnn2 : (nnv + W64 k).toNat ≤ max j (nnv.toNat + k) := by rw [hnk]; omega
          have hAn2 : A' ≤ (nnv + W64 k).toNat + 0x40000000 := by rw [hnk]; omega
          wp_for_post
          inext
          iapply IH $$ %(max j (nnv.toNat + k)) %A' %_ %(nnv + W64 k) %_ %_ %hnn2 %hnl'
            %hj' %hA'l %hAn2 %hEj' %hjA' %hinv' %hys' %hcj' [Hm] [Hbs] [Hc] Hosfd Hsl Hfd HΦ
            [$] [$] [$] [$] [$] [$] [$] [$]
          · iexact Hm
          · iexact Hbs
          · iexact Hc
        · rw [decide_eq_false he0]
          simp only [Bool.not_false]
          try wp_auto
          wp_apply os.wp_wrapErrno_ok _ inner name e he0 $$ Hn as %pe #Hok
          ihave #Hokn := EtcdGrove.fmtErrorOkOrNil_of _ $$ Hok
          wp_for_post
          iapply HΦ
          iframe Hokn
          iframe
          isplitl []
          · isplitl [] <;> (try isplitl []) <;> iassumption
          · ipureintro
            exact ⟨hj', hA'l, fun h => absurd h (by omega), hEj', hjA', hys', hcj',
              .inr ⟨rfl, (by intro h; cases h), (hneW he0).imp_right (fun h => by rw [hoffv] at h; omega)⟩⟩


end proof

end EtcdGrove
end Perennial
