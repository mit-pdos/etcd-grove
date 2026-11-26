/-
The proof of `Spec/os/CrashStILLong.lean`: `os.File.WriteAt.wp_proof_crashIL`'s loop
(`Proof/os/CrashStILSpec.lean`), each attempt of the next chunk (`wchunk`: at most `maxRW` bytes,
the model's `max`, as `Proof/os/WriteLong.lean` takes it), over the local steps of
`Proof/os/CrashStIL.lean`. The caller's half of the write's range splits around the chunk
(`window_split3`) and joins again as the new state holds it (`finBytes_windowC`); the bytes written
so far are the data's (`fin_valsC`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.os.CrashStILLong
public import Spec.os.CrashSt
public import Proof.os.CrashStIOps
public import Proof.os.WriteLongStep
public import Perennial.Golang.Theory.IfJoin
public import Perennial.Golang.Theory.Plain
public import GooseLang.Ext.Fs.TruncateBig
public import Proof.os.ErrorOk
public import Spec.os.CrashStILR

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

/-- A window `[off, off + len)` around a range `[nn, nn + c)` of it. -/
theorem window_split3 {α : Type} (l : List α) (off len nn c : Nat) (h : nn + c ≤ len) :
    (l.drop off).take len = ((l.drop off).take len).take nn ++
      ((l.drop (off + nn)).take c ++ ((l.drop off).take len).drop (nn + c)) := by
  have e0 : ((l.drop off).take len).drop nn = (l.drop (off + nn)).take (len - nn) := by
    apply List.ext_getElem?
    intro j
    simp only [List.getElem?_drop, List.getElem?_take]
    by_cases h' : j < len - nn
    · rw [if_pos (by omega), if_pos h']
      all_goals first | rfl | (congr 1; omega)
    · rw [if_neg (by omega), if_neg h']
  have e1 : ((l.drop off).take len).drop (nn + c) = (((l.drop off).take len).drop nn).drop c := by
    rw [List.drop_drop]
  have e2 : (((l.drop off).take len).drop nn).take c = (l.drop (off + nn)).take c := by
    rw [e0, List.take_take]; congr 1; omega
  conv => lhs; rw [← List.take_append_drop nn ((l.drop off).take len)]
  congr 1
  rw [e1, ← e2, List.take_append_drop]

/-- The chunk is the data from `nn` on. -/
theorem wchunk_get (data : List w8) (nn j : Nat) (hj : j < (wchunk data nn).length) :
    (wchunk data nn)[j]? = data[nn + j]? := by
  rw [wchunk_length] at hj
  simp only [wchunk, List.getElem?_take, List.getElem?_drop]
  rw [if_pos (by omega)]

/-- **The range of a write inside the file after an attempt of the chunk `dc` from `off + nn`**: the
bytes before `off + nn` as they were, the attempt's, then the bytes after the chunk as they were. -/
theorem finBytes_windowC (m' : OsMeta) (bs' : List ByteG) (off nn : Nat) (data dc : List w8)
    (k n : Nat) (hl : bs'.length = m'.size) (hin : off + data.length ≤ m'.size)
    (hc : nn + dc.length ≤ data.length) (hk : k ≤ dc.length) :
    ((finBytes m' bs' (off + nn) dc k n []).drop off).take data.length =
      ((bs'.drop off).take data.length).take nn ++
        (pwBytes m'.size (off + nn) dc k n (cfRange m' bs' (off + nn) dc.length) [] ++
          ((bs'.drop off).take data.length).drop (nn + dc.length)) := by
  have hlo : cfLo m' (off + nn) = off + nn := Nat.min_eq_left (by omega)
  have hhi : cfHi m' (off + nn) dc.length = off + nn + dc.length := by unfold cfHi; omega
  have hps : pwSize m'.size (off + nn) k = m'.size := by unfold pwSize; split <;> omega
  have hpl : (pwBytes m'.size (off + nn) dc k n (cfRange m' bs' (off + nn) dc.length) []).length =
      dc.length := by
    rw [pwBytes_length, hps]; omega
  have hA : (((bs'.drop off).take data.length).take nn).length = nn := by
    simp only [List.length_take, List.length_drop]; omega
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_take, List.getElem?_drop]
  have hget := getElem?_tpd bs' (pwBytes m'.size (off + nn) dc k n
    (cfRange m' bs' (off + nn) dc.length) []) (cfLo m' (off + nn)) (cfHi m' (off + nn) dc.length)
    (off + j) (by rw [hl]; omega)
  rw [← finBytes, hlo, hhi] at hget
  by_cases h1 : j < data.length
  · rw [if_pos h1, hget]
    by_cases h2 : j < nn
    · rw [if_pos (by omega), List.getElem?_append_left (by omega), List.getElem?_take,
        if_pos h2, List.getElem?_take, if_pos h1, List.getElem?_drop]
    · rw [if_neg (by omega), List.getElem?_append_right (by omega), hA]
      by_cases h3 : j < nn + dc.length
      · rw [if_pos (by rw [hpl]; omega), List.getElem?_append_left (by rw [hpl]; omega),
          show off + j - (off + nn) = j - nn by omega]
      · rw [if_neg (by rw [hpl]; omega), List.getElem?_append_right (by rw [hpl]; omega), hpl,
          List.getElem?_drop, List.getElem?_take, if_pos (by omega), List.getElem?_drop]
        congr 1; omega
  · rw [if_neg h1]
    symm
    apply List.getElem?_eq_none
    simp only [List.length_append, hA, hpl, List.length_drop, List.length_take]
    omega

/-- **The bytes a write has written are the data's**, after an attempt of the chunk `dc` (the data
from `nn` on) that wrote `k`. -/
theorem fin_valsC {m' : OsMeta} {bs' : List ByteG} {off nn k n : Nat} {data dc : List w8}
    (hlen : bs'.length = m'.size) (hin : off + data.length ≤ m'.size) (hk : k ≤ dc.length)
    (hdc : ∀ j < dc.length, dc[j]? = data[nn + j]?) (hc : nn + dc.length ≤ data.length)
    (hpre : ∀ i < nn, (bs'[off + i]?).map Prod.fst = data[i]?) :
    ∀ i < nn + k, ((finBytes m' bs' (off + nn) dc k n [])[off + i]?).map Prod.fst = data[i]? := by
  intro i hi
  have hlo : cfLo m' (off + nn) = off + nn := Nat.min_eq_left (by omega)
  have hps : pwSize m'.size (off + nn) k = m'.size := by unfold pwSize; split <;> omega
  have hpl : (pwBytes m'.size (off + nn) dc k n (cfRange m' bs' (off + nn) dc.length) []).length =
      dc.length := by
    rw [pwBytes_length, hps]; omega
  have hget := getElem?_tpd bs' (pwBytes m'.size (off + nn) dc k n
    (cfRange m' bs' (off + nn) dc.length) []) (cfLo m' (off + nn)) (cfHi m' (off + nn) dc.length)
    (off + i) (by rw [hlen]; omega)
  rw [← finBytes, hlo] at hget
  rw [hget]
  by_cases c1 : off + i < off + nn
  · rw [if_pos c1]; exact hpre i (by omega)
  rw [if_neg c1, if_pos (by rw [hpl]; omega), List.getElem?_eq_getElem (by rw [hpl]; omega),
    Option.map_some, pwBytes_getElem _ _ _ _ _ _ _ _ (by rw [hpl]; omega),
    show off + nn + (off + i - (off + nn)) = off + i by omega]
  unfold pwByte
  rw [if_pos (by omega : off + i < off + nn + k), show off + i - (off + nn) = i - nn by omega,
    List.getD_eq_getElem?_getD, hdc (i - nn) (by omega), show nn + (i - nn) = i by omega,
    List.getElem?_eq_getElem (show i < data.length by omega), Option.getD_some]

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [GoGlobalContext]
  [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

/-- A growing truncate's second step to a target past `maxBytes`, from the local caller's part:
it fails, its `OsMeta` as the first step announced it (`wp_osFtruncateFinishBig`), of which the
caller shows `Ok`. -/
theorem wp_osFtruncateFinish_LBig (t : Nat) (p : Ino) (sz n : Nat) (N : Namespace)
    (I : IProp GF) [Persistent I] (Tok : CSt → IProp GF) (Ok : CSt → Prop)
    (hacc : CsAcc (L := L) N I Tok Ok p) (m : OsMeta) (bs : List ByteG)
    (hN : ↑osN ⊆ (⊤ : CoPset) \ ↑N) (hl : bs.length = m.size) (hgrow : m.size ≤ sz)
    (hbig : maxBytes < sz)
    (hokF : Ok ⟨m.announce (min m.size sz) (rsHi true m.size sz) sz, bs, 0, 0, .idle⟩)
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ I -∗ Tok ⟨m, bs, 0, 0, .trunc t sz n⟩ -∗
      (∀ e : w64, ⌜e ≠ 0⌝ -∗
        csOwnL (L := L) Tok p ⟨m.announce (min m.size sz) (rsHi true m.size sz) sz, bs, 0, 0, .idle⟩ -∗
        mcells (L := L) m.maps m.size (rsHi true m.size sz) (rsOld m.size m.size []) -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "FtruncateFinish" (Val (osTokV t))) {{ Φ }} := by
  iintro #Hos #Hinv Hv HΦ
  have hmin : min m.size sz = m.size := Nat.min_eq_left hgrow
  iapply (wp_atomic (E2 := (⊤ : CoPset) \ ↑N))
  imod hacc ⊤ _ (show ↑N ⊆ (⊤ : CoPset) from CoPset.subseteq_top) $$ Hinv Hv with ⟨Hr, %Hok', Hclose⟩
  have hcut : m.cut = none := Hok'.2
  icases (show invResS (L := L) (some (p, ⟨m, bs, 0, 0, .trunc t sz n⟩)) ⊢
    rsTok (L := L) true t p sz m [] n ∗ invBytes (L := L) p ⟨m, bs, 0, 0, .trunc t sz n⟩ from .rfl)
    $$ Hr with ⟨Ht, Hb2⟩
  icases (invBytes_whole p ⟨m, bs, 0, 0, .trunc t sz n⟩ (taken_trunc _ t sz n rfl)
    (Nat.le_refl _)).1 $$ Hb2 with Hb2
  imodintro
  iapply wp_osFtruncateFinishBig t p sz m [] n hbig hN $$ Hos Ht
  iintro %e %he Hres
  unfold rsUndone
  icases Hres with ⟨Hm, -, Hc⟩
  icases (osMeta_halves _ _).1 $$ Hm with ⟨Hm1, Hm2⟩
  imod Hclose $$ %(⟨m.announce (min m.size sz) (rsHi true m.size sz) sz, bs, 0, 0, .idle⟩ : CSt)
    %(And.intro (hokF) (by simp [hcut, OsMeta.announce])) [Hm2 Hb2] with Hv
  · iapply (invResS_idle _ _ rfl).2; iframe Hm2
    iapply (invBytes_whole p _ (taken_idle _ rfl) (Nat.le_refl _)).2; iexact Hb2
  imodintro
  ihave Hc := (show mcells (L := L) m.maps (min m.size sz) (rsHi true m.size sz)
      (rsOld m.size (min m.size sz) []) ⊢
    mcells (L := L) m.maps m.size (rsHi true m.size sz) (rsOld m.size m.size []) by rw [hmin]) $$ Hc
  iapply HΦ $$ %e %he [Hv Hm1] Hc
  unfold csOwnL
  iframe Hv Hm1
  ipureintro
  exact ⟨⟨by rw [announce_size]; exact hl, Nat.le_refl _, Nat.zero_le _, trivial⟩, rfl, rfl, rfl⟩

end res

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions]

theorem os.File.WriteAt.wp_proof_crashILLongR : os.File.WriteAt.specCrashILLongR (GF := GF) (hG := hG) := by
  intro A _ f fd name dqf sl data dqs off dq d N i γ γa γc Ok R _ a m bs xs hi hwr hoff hin hmaxB hbig hn hxl hN hW
  subst hi
  unfold os.ownFile
  wp_start as ⟨#Hos, #Hinv, ⟨%inner, #Hf, Hfd, #Hn, #Hsys⟩, Hsl, Hosfd, Hown, Hx, Hc⟩
  icases csOwnL_locOk _ _ _ $$ Hown with %Hlo
  have hlen : bs.length = m.size := Hlo.1.1
  -- the caller's bytes are the state's
  imod csOwnILR_agree R N d.ino γ γa γc Ok ⟨m, bs, 0, 0, .idle⟩ a ⊤ CoPset.subseteq_top off.toNat
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
  have hR : WReachC m bs off.toNat data nnv.toNat m' bs' := by
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
  obtain ⟨hsz', hmp', hl', -⟩ := hR.inside hlen hin
  have hnnz : sint.Z nnv = nnv.toNat := by
    simp only [sint.Z]; rw [BitVec.toInt_eq_toNat_of_lt (by omega)]
  have hnnn : sint.nat nnv = nnv.toNat := by simp [sint.nat, hnnz]
  wp_auto
  -- this attempt's chunk, `[nn, A')`
  have hsub : sint.Z (sl.len - nnv) = data.length - nnv.toNat := by
    have : sint.Z nnv ≤ sint.Z sl.len := by rw [hnnz, hslz]; omega
    have : 0 ≤ sint.Z nnv := by rw [hnnz]; omega
    have : sint.Z (sl.len - nnv) = sint.Z sl.len - sint.Z nnv := by word
    rw [this, hslz, hnnz]
  obtain ⟨A', hA'd⟩ : ∃ A' : Nat, A' = min data.length (nnv.toNat + 0x40000000) := ⟨_, rfl⟩
  have hnA' : nnv.toNat < A' := by omega
  have hA'l : A' ≤ data.length := by omega
  have h2p30 : sint.Z (W64 1073741824) = 1073741824 := rfl
  wp_if_join (fun v => iprop(∃ mx : w64, ⌜v = #mx ∧ sint.Z mx = A'⌝))
  · iexists (nnv + W64 1073741824)
    ipureintro
    refine ⟨rfl, ?_⟩
    rw [hsub, h2p30] at Hif
    rw [wl_add30 nnv (by rw [hnnz]; omega) (by rw [hnnz]; omega), hnnz]; omega
  · iexists sl.len
    ipureintro
    refine ⟨rfl, ?_⟩
    rw [hsub, h2p30] at Hif
    rw [hslz]; omega
  iintro %v ⟨%mx, %hmxv⟩
  obtain ⟨rfl, hmxz⟩ := hmxv
  wp_auto
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
  have hdc : subslice nnv.toNat A' data = wchunk data nnv.toNat := by
    have h1 : subslice nnv.toNat A' data = (data.drop nnv.toNat).take (A' - nnv.toNat) := by
      simp only [subslice, List.drop_take]
    rw [h1, wchunk]
    by_cases hA : nnv.toNat + 0x40000000 ≤ data.length
    · rw [show A' - nnv.toNat = 0x40000000 by omega]
    · rw [List.take_of_length_le (by simp only [List.length_drop]; omega),
        List.take_of_length_le (by simp only [List.length_drop]; omega)]
  rw [hdc]
  have hcl : (wchunk data nnv.toNat).length = A' - nnv.toNat := by rw [wchunk_length]; omega
  have hoffv : (off + nnv).toNat = off.toNat + nnv.toNat := by
    rw [BitVec.toNat_add]; apply Nat.mod_eq_of_lt; omega
  have hoffv' : 0 ≤ (off + nnv).toInt := by
    rw [BitVec.toInt_eq_toNat_of_lt (by rw [hoffv]; omega)]; omega
  have hin' : (off + nnv).toNat + (wchunk data nnv.toNat).length ≤ m'.size := by
    rw [hoffv, hcl]; omega
  -- the caller's bytes: those before the chunk, the chunk's range, those after it
  have hA : (((bs'.drop off.toNat).take data.length).take nnv.toNat).length = nnv.toNat := by
    simp only [List.length_take, List.length_drop]; omega
  have hml : ((bs'.drop (off.toNat + nnv.toNat)).take (wchunk data nnv.toNat).length).length =
      (wchunk data nnv.toNat).length := by
    simp only [List.length_take, List.length_drop]; omega
  ihave ⟨Hx1, Hx2, Hx3⟩ := (show osBytes (GF := GF) d.ino off.toNat (DFrac.own (1 : Qp).half)
      ((bs'.drop off.toNat).take data.length) ⊢
    osBytes (GF := GF) d.ino off.toNat (DFrac.own (1 : Qp).half)
      (((bs'.drop off.toNat).take data.length).take nnv.toNat) ∗
    osBytes (GF := GF) d.ino (off + nnv).toNat (DFrac.own (1 : Qp).half)
      ((bs'.drop (off + nnv).toNat).take (wchunk data nnv.toNat).length) ∗
    osBytes (GF := GF) d.ino (off.toNat + nnv.toNat + (wchunk data nnv.toNat).length)
      (DFrac.own (1 : Qp).half)
      (((bs'.drop off.toNat).take data.length).drop (nnv.toNat + (wchunk data nnv.toNat).length)) by
      conv => lhs; rw [window_split3 bs' off.toNat data.length nnv.toNat
        (wchunk data nnv.toNat).length (by omega)]
      refine (osBytes_appendL _ _ _ _ _).1.trans (sep_mono .rfl ?_)
      rw [hA]
      refine (osBytes_appendL _ _ _ _ _).1.trans ?_
      rw [hml, hoffv]) $$ Hx
  -- the cells: before the chunk, the chunk's, after it
  ihave ⟨Hc1, Hc23⟩ := mcellsAny_split m.maps off.toNat (off.toNat + nnv.toNat)
    (off.toNat + data.length) (by omega) (by omega) $$ Hc
  ihave ⟨Hc2, Hc3⟩ := mcellsAny_split m.maps (off.toNat + nnv.toNat)
    (off.toNat + nnv.toNat + (wchunk data nnv.toNat).length) (off.toNat + data.length)
    (by omega) (by omega) $$ Hc23
  ihave Hc2 := (show mcellsAny (GF := GF) m.maps (off.toNat + nnv.toNat)
      (off.toNat + nnv.toNat + (wchunk data nnv.toNat).length) ⊢
    mcellsAny m'.maps (off + nnv).toNat ((off + nnv).toNat + (wchunk data nnv.toNat).length)
      by rw [hoffv, hmp']) $$ Hc2
  have hdne : wchunk data nnv.toNat ≠ [] := by
    intro h; have := congrArg List.length h; rw [hcl] at this; simp at this; omega
  have hW1 : ∀ t n, PwFresh m' bs' (off + nnv).toNat (wchunk data nnv.toNat) n →
      Ok a ⟨m', bs', 0, 0, .write t (off + nnv).toNat (wchunk data nnv.toNat) n⟩ := by
    intro t n hfr; rw [hoffv] at hfr ⊢; exact (hW _ _ _ hR).2 hnn t n hfr
  wp_apply wp_osPWriteStart_L fd (off + nnv) (wchunk data nnv.toNat) dq d N
    (csInvIR (GF := GF) N d.ino γ γa γc Ok R) (csTokI γ γa a) (Ok a) (csI_accR R N d.ino γ γa γc Ok a)
    m' bs' ((bs'.drop (off + nnv).toNat).take (wchunk data nnv.toNat).length) hN hwr hoffv' hin'
    hdne (by
      have h1 : (off + nnv).toNat + (wchunk data nnv.toNat).length ≤ bs'.length := by
        rw [hl']; exact hin'
      simp only [List.length_take, List.length_drop] at h1 ⊢; omega) hW1
    $$ Hos Hinv Hosfd Hown Hx2 Hc2 as %t %nst %hfrx Hosfd Hown
  have hfr := hfrx.1
  have hps : ∀ k, k ≤ (wchunk data nnv.toNat).length →
      pwSize m'.size (off + nnv).toNat k = m'.size :=
    fun k hk => by unfold pwSize; split <;> omega
  have hW2 : ∀ k, k ≤ (wchunk data nnv.toNat).length →
      Ok a ⟨pwPostK true m' (off + nnv).toNat (wchunk data nnv.toNat) k nst,
        finBytes m' bs' (off + nnv).toNat (wchunk data nnv.toNat) k nst [], 0, 0, .idle⟩ := by
    intro k hk; rw [hoffv] at hfr ⊢
    exact (hW _ _ _ (hR.step k _ nst [] hnn hk (.inl rfl)
      (by rw [← hoffv, hps k hk]; simp) (fun _ _ _ h => absurd h (Nat.not_lt_zero _)) hfr)).1
  wp_apply wp_osPWriteFinish_L t d.ino (off + nnv).toNat (wchunk data nnv.toNat) nst N
    (csInvIR (GF := GF) N d.ino γ γa γc Ok R) (csTokI γ γa a) (Ok a) (csI_accR R N d.ino γ γa γc Ok a)
    m' bs' hN hl' hin' (by rw [hoffv]; omega) hW2 $$ Hos Hinv Hown as %k %e %hke Hown Hy Hc2
  obtain ⟨hk, hke, hzt, hzl, hfe⟩ := hke
  have hpre' : ∀ i < nnv.toNat + k,
      ((finBytes m' bs' (off + nnv).toNat (wchunk data nnv.toNat) k nst [])[off.toNat + i]?).map
        Prod.fst = data[i]? := by
    rw [hoffv]
    exact fin_valsC hl' (by omega) hk (wchunk_get data nnv.toNat) (by omega) hpre
  have hRs : ∀ nn', (nn' = nnv.toNat + k ∨ nn' = nnv.toNat) →
      WReachC m bs off.toNat data nn'
        (pwPostK true m' (off + nnv).toNat (wchunk data nnv.toNat) k nst)
        (finBytes m' bs' (off + nnv).toNat (wchunk data nnv.toNat) k nst []) := by
    intro nn' h; rw [hoffv] at hfr ⊢
    exact hR.step k nn' nst [] hnn hk h (by rw [← hoffv, hps k hk]; simp)
      (fun _ _ _ h => absurd h (Nat.not_lt_zero _)) hfr
  -- the caller's bytes of the range, as the new state holds them
  have hpl : (pwBytes m'.size (off.toNat + nnv.toNat) (wchunk data nnv.toNat) k nst
      (cfRange m' bs' (off.toNat + nnv.toNat) (wchunk data nnv.toNat).length) []).length =
      (wchunk data nnv.toNat).length := by
    rw [pwBytes_length, show pwSize m'.size (off.toNat + nnv.toNat) k = m'.size by
      rw [← hoffv]; exact hps k hk]
    omega
  ihave Hx := (show osBytes (GF := GF) d.ino off.toNat (DFrac.own (1 : Qp).half)
      (((bs'.drop off.toNat).take data.length).take nnv.toNat) ∗
    (osBytes (GF := GF) d.ino (off + nnv).toNat (DFrac.own (1 : Qp).half)
      (pwBytes m'.size (off + nnv).toNat (wchunk data nnv.toNat) k nst
        (cfRange m' bs' (off + nnv).toNat (wchunk data nnv.toNat).length) []) ∗
     osBytes (GF := GF) d.ino (off.toNat + nnv.toNat + (wchunk data nnv.toNat).length)
      (DFrac.own (1 : Qp).half)
      (((bs'.drop off.toNat).take data.length).drop (nnv.toNat + (wchunk data nnv.toNat).length))) ⊢
    osBytes (GF := GF) d.ino off.toNat (DFrac.own (1 : Qp).half)
      (((finBytes m' bs' (off + nnv).toNat (wchunk data nnv.toNat) k nst []).drop off.toNat).take
        data.length) by
      rw [hoffv, finBytes_windowC m' bs' off.toNat nnv.toNat data (wchunk data nnv.toNat) k nst hl'
        (by omega) (by omega) hk]
      refine BIBase.Entails.trans ?_ (osBytes_appendL _ _ _ _ _).2
      rw [hA]
      refine sep_mono .rfl ?_
      refine BIBase.Entails.trans ?_ (osBytes_appendL _ _ _ _ _).2
      rw [hpl]) $$ [Hx1 Hy Hx3]
  · iframe
  -- the cells back
  ihave Hc2 := mcells_any _ _ _ _ $$ Hc2
  ihave Hc2 := (show mcellsAny (GF := GF) m'.maps (off + nnv).toNat
      ((off + nnv).toNat + (wchunk data nnv.toNat).length) ⊢
    mcellsAny m.maps (off.toNat + nnv.toNat) (off.toNat + nnv.toNat + (wchunk data nnv.toNat).length)
      by rw [hoffv, hmp']) $$ Hc2
  ihave Hc23 := mcellsAny_merge m.maps (off.toNat + nnv.toNat)
    (off.toNat + nnv.toNat + (wchunk data nnv.toNat).length) (off.toNat + data.length)
    (by omega) (by omega) $$ [Hc2 Hc3]
  · iframe
  ihave Hc := mcellsAny_merge m.maps off.toNat (off.toNat + nnv.toNat) (off.toNat + data.length)
    (by omega) (by omega) $$ [Hc1 Hc23]
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
          obtain ⟨hsz2, hmp2, -, -⟩ := (hRs _ (.inl rfl)).inside hlen hin
          exact ⟨_, by trivial, hRs _ (.inl rfl), .inl ⟨hsln, rfl, hfk, hsz2, hmp2,
            fun i hi => hpre' i (by omega)⟩⟩
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
          exact ⟨_, by trivial, hRs _ (.inl rfl), .inr ⟨rfl, (by intro h; cases h),
            hfe (fun h => he0 (by rw [h]; rfl))⟩⟩
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
          exact ⟨_, by trivial, hRs _ (.inl rfl), .inr ⟨rfl, (by intro h; cases h),
            hfe (fun h => he0 (by rw [h]; rfl))⟩⟩

theorem os.File.WriteAt.wp_proof_crashILLong : os.File.WriteAt.specCrashILLong (GF := GF) (hG := hG) := by
  intro A _ f fd name dqf sl data dqs off dq d N i γ γa γc Ok a m bs xs hi hwr hoff hin hmaxB hbig hn hxl hN hW
  iintro %Φ ⟨#Hos, #Hinv, H⟩ HΦ
  iapply (os.File.WriteAt.wp_proof_crashILLongR (GF := GF) (hG := hG)
    f fd name dqf sl data dqs off dq d N i γ γa γc Ok (fun _ => iprop(emp)) a m bs xs hi hwr hoff hin hmaxB hbig hn hxl hN hW) $$ [H]
  · isplitr
    · iexact Hos
    isplitr [H]
    · iapply csInvI_R; iexact Hinv
    · iexact H
  · iexact HΦ

theorem os.File.Truncate.wp_proof_crashILBigR :
    os.File.Truncate.specCrashILBigR (GF := GF) (hG := hG) := by
  intro A _ f fd name dqf sz dq d N i γ γa γc Ok R _ a m bs hi hfd0 hwr hsz hgrow hbig hN hT
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
  ihave HS : ∃ m0, ⌜m0 = m ∨ m0 = m.announce (min m.size sz.toNat) (rsHi true m.size sz.toNat) sz.toNat⌝ ∗
      csOwnIL (GF := GF) d.ino γ γa ⟨m0, bs, 0, 0, .idle⟩ a ∗
      mcellsAny m.maps m.size (rsHi true m.size sz.toNat) $$ [Hown Hc]
  · iexists m; iframe; ipureintro; exact .inl rfl
  iloeb as IH generalizing HS Hosfd Hfd HΦ
  icases HS with ⟨%m0, %hm0, Hown, Hc⟩
  have hsz0 : m0.size = m.size := by rcases hm0 with rfl | rfl <;> simp
  have hmp0 : m0.maps = m.maps := by rcases hm0 with rfl | rfl <;> simp
  ihave Hc := (show mcellsAny (GF := GF) m.maps m.size (rsHi true m.size sz.toNat) ⊢
    mcellsAny m0.maps m0.size (rsHi true m0.size sz.toNat) by rw [hsz0, hmp0]) $$ Hc
  wp_apply wp_osFtruncateStart_L fd sz dq d N (csInvIR (GF := GF) N d.ino γ γa γc Ok R)
    (csTokI γ γa a) (Ok a) (csI_accR R N d.ino γ γa γc Ok a) m0 bs hN hwr hsz
    (by rw [hsz0]; exact hgrow) (hT _ hm0).2 $$ Hos Hinv Hosfd Hown Hc as %t %n Hosfd Hown
  have hann : m0.announce (min m0.size sz.toNat) (rsHi true m0.size sz.toNat) sz.toNat =
      m.announce (min m.size sz.toNat) (rsHi true m.size sz.toNat) sz.toNat := by
    rw [hsz0]; rcases hm0 with rfl | rfl
    · rfl
    · exact os.announce_idem _ _ _ _
  have hokF : Ok a ⟨m0.announce (min m0.size sz.toNat) (rsHi true m0.size sz.toNat) sz.toNat,
      bs, 0, 0, .idle⟩ := by rw [hann]; exact (hT _ (.inr rfl)).1
  wp_apply wp_osFtruncateFinish_LBig t d.ino sz.toNat n N (csInvIR (GF := GF) N d.ino γ γa γc Ok R)
    (csTokI γ γa a) (Ok a) (csI_accR R N d.ino γ γa γc Ok a) m0 bs hN (by rw [hsz0]; exact hlen)
    (by rw [hsz0]; exact hgrow) hbig hokF $$ Hos Hinv Hown as %e %he Hown Hc
  ihave Hc := mcells_any (GF := GF) _ _ _ _ $$ Hc
  ihave Hc := (show mcellsAny (GF := GF) m0.maps m0.size (rsHi true m0.size sz.toNat) ⊢
    mcellsAny m.maps m.size (rsHi true m.size sz.toNat) by rw [hsz0, hmp0]) $$ Hc
  rw [hann]
  by_cases he4 : e = W64 4
  · rw [decide_eq_true he4]
    wp_auto
    iapply IH $$ [Hown Hc] Hosfd Hfd HΦ
    iexists _; iframe; ipureintro; exact .inr rfl
  · rw [decide_eq_false he4]
    wp_auto
    have he0' : ¬ e = W64 0 := he
    rw [decide_eq_false he0']
    wp_auto
    wp_apply os.wp_wrapErrno_ok _ inner name e he0' $$ Hn Hsys as %pe #Hok
    iapply HΦ
    iframe
    isplitl []
    · (repeat' isplitl []) <;> iassumption
    isplitr
    · ipureintro; intro h; cases h
    iexact Hok

theorem os.File.Truncate.wp_proof_crashILBig :
    os.File.Truncate.specCrashILBig (GF := GF) (hG := hG) := by
  intro A _ f fd name dqf sz dq d N i γ γa γc Ok a m bs hi hfd0 hwr hsz hgrow hbig hN hT
  iintro %Φ ⟨#Hos, #Hinv, H⟩ HΦ
  iapply (os.File.Truncate.wp_proof_crashILBigR (GF := GF) (hG := hG)
    f fd name dqf sz dq d N i γ γa γc Ok (fun _ => iprop(emp)) a m bs hi hfd0 hwr hsz hgrow hbig hN hT) $$ [H]
  · isplitr
    · iexact Hos
    isplitr [H]
    · iapply csInvI_R; iexact Hinv
    · iexact H
  · iexact HΦ

end proof

end EtcdGrove
end Perennial
