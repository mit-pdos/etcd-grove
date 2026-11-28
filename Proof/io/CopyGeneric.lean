/-
**`io.CopyFiles.spec`'s fallback** (`genericReadFrom`'s `io.Copy(fileWithoutReadFrom{bf}, fileWithoutWriteTo{f})`):
`copyBuffer`'s 32 KiB loop of `File.Read` (`os.File.Read.wp_eof`) and `File.Write` (`os.File.Write.wp_long`)
from the copy's state at `j` (`io.cpS`: the destination the source's bytes `[o, o + j)`, both offsets at
their ends) to its end (`io.cpFin`: on `nil`, the destination the source's bytes from `o` on, both offsets
at the ends; on an error, the destination whole with any bytes). Lean-first.
-/
module

public import Proof.io.CopyPoll
public import Proof.os.OffLong

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

/-- `cpOk` after a `pwrite` at the end that announced `A` bytes and wrote `k ≤ A` (any `cz`). -/
theorem io.cpOk_pwPostE {m : OsMeta} (hm : io.cpOk m) {A k E : Nat} (hk : k ≤ A) :
    io.cpOk (os.pwPostE m m.size A k E) ∧ (os.pwPostE m m.size A k E).size = m.size + k := by
  obtain ⟨hmaps, hcut, hlo, z, hz, hzs⟩ := hm
  have hsz : (os.pwPostE m m.size A k E).size = m.size + k := by
    show pwSize m.size m.size k = _
    unfold pwSize; split <;> omega
  refine ⟨⟨?_, ?_, ?_, ?_⟩, hsz⟩
  · show (m.announce (min m.size m.size) (m.size + A) (max m.size (m.size + A))).maps = ∅
    rw [announce_maps]; exact hmaps
  · show (m.announce (min m.size m.size) (m.size + A) (max m.size (m.size + A))).cut = none
    simp only [OsMeta.announce, OsMeta.touch_cut]
    exact hcut
  · rw [hsz]
    show min m.lo (max m.size (m.size + A)) ≤ _
    omega
  · refine ⟨if min m.size m.size < m.size + A then max z (m.size + A) else z, ?_, ?_⟩
    · show (m.announce (min m.size m.size) (m.size + A) (max m.size (m.size + A))).zf = _
      rw [announce_zf, hz]; rfl
    · rw [hsz]; split <;> omega

/-- `pwPost` is `pwPostE` up to `cz`, which `cpOk` does not read. -/
theorem io.cpOk_pwPost' {m : OsMeta} (hm : io.cpOk m) {A k : Nat} (hk : k ≤ A) :
    io.cpOk (pwPost m m.size A k) ∧ (pwPost m m.size A k).size = m.size + k :=
  io.cpOk_pwPostE (E := 0) hm hk

/-- The bytes a write at the end leaves (`PwOut`'s and `PwOutA`'s first two facts): the data's first `k`. -/
theorem io.pwEnd_vals (sz : Nat) (data : List w8) (k : Nat) (ys : List ByteG) (hk : k ≤ data.length)
    (hl : ys.length = min (sz + data.length) (pwSize sz sz k) - sz)
    (hv : ∀ i (hi : i < ys.length), ys[i].1 = pwByte sz data k [] (sz + i)) :
    ys.map Prod.fst = data.take k ∧ ys.length = k := by
  have hlk : ys.length = k := by rw [hl]; unfold pwSize; split <;> omega
  refine ⟨?_, hlk⟩
  apply List.ext_getElem
  · rw [List.length_map, List.length_take]; omega
  · intro i h1 h2
    rw [List.getElem_map, hv i (by simpa using h1), List.getElem_take]
    rw [List.length_map] at h1
    simp only [pwByte, show sz + i < sz + k by omega, ↓reduceIte, show sz + i - sz = i by omega,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < data.length by omega),
      Option.getD_some]

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions]

/-- **The destination opened for a write of `n` bytes at its end** (`os.File.Write.wp_long`'s pre). -/
theorem io.copyDst_open (i : Ino) (vs : List w8) (n : Nat) :
    io.copyDst (GF := GF) i (· = vs) ⊢ ∃ (md : OsMeta) (xs : List ByteG),
      osMeta i (DFrac.own 1) md ∗ osBytes i 0 (DFrac.own 1) xs ∗ osBytes i vs.length (DFrac.own 1) [] ∗
      mcellsAny md.maps vs.length (vs.length + n) ∗
      ⌜io.cpOk md ∧ xs.length = md.size ∧ xs.map (·.1) = vs ∧ md.size = vs.length⌝ := by
  iintro H
  ihave ⟨%md, %xs, Hm, Hb, %h⟩ := io.copyDst_elim i _ $$ H
  obtain ⟨hok, hl, hv⟩ := h
  iexists md, xs
  iframe Hm Hb
  isplitr
  · unfold osBytes; iapply (bytesG_nil _ _ _ _).2; iempintro
  isplitr
  · rw [hok.1]; unfold mcellsAny; iapply BigSepM.bigSepM_empty.2; itrivial
  ipureintro
  refine ⟨hok, hl, hv, ?_⟩
  rw [← hl, ← hv, List.length_map]

/-- **The destination after a write at its end** that announced `A` bytes of `data` and wrote `k`
(`os.File.Write.wp_long`'s posts, success and failure): the bytes before it, then `data`'s first `k`. -/
theorem io.copyDst_wrote (i : Ino) (md M : OsMeta) (off : Nat) (xs ys : List ByteG) (data : List w8)
    (A k : Nat) (hoff : md.size = off)
    (hok : io.cpOk md) (hxl : xs.length = md.size) (hkA : k ≤ A) (hk : k ≤ data.length)
    (hM : M = pwPost md off A k ∨ ∃ E, M = os.pwPostE md off A k E)
    (hl : ys.length = min (off + data.length) (pwSize md.size off k) - off)
    (hv : ∀ j (hj : j < ys.length), ys[j].1 = pwByte off data k [] (off + j)) :
    osMeta (GF := GF) i (DFrac.own 1) M ∗ osBytes i 0 (DFrac.own 1) xs ∗
      osBytes i off (DFrac.own 1) ys ⊢
      io.copyDst i (· = xs.map (·.1) ++ data.take k) := by
  subst hoff
  iintro ⟨Hm, Hxs, Hys⟩
  have hp : io.cpOk M ∧ M.size = md.size + k := by
    rcases hM with rfl | ⟨E, rfl⟩
    · exact io.cpOk_pwPost' hok hkA
    · exact io.cpOk_pwPostE hok hkA
  obtain ⟨hyv, hyl⟩ := io.pwEnd_vals md.size data k ys hk hl hv
  ihave Hb : osBytes (GF := GF) i 0 (DFrac.own 1) (xs ++ ys) $$ [Hxs Hys]
  · iapply (io.osBytes_append i 0 _ xs _).2
    rw [Nat.zero_add, hxl]
    isplitl [Hxs]
    · iexact Hxs
    · iexact Hys
  iapply (io.copyDst_intro i _ _ (xs ++ ys) hp.1
    (by rw [List.length_append, hyl, hp.2, hxl])
    (by rw [List.map_append, hyv])) $$ [Hm Hb]
  iframe

/-- **The copy's state at `j`**, over the `*File`s: the destination `bf` holds the source's bytes
`[o, o + j)`, its offset `j`, the source `f`'s offset `o + j`. -/
def io.cpS (bf f : Loc) (i : Ino) (o : Nat) (bs : List ByteG) (j : Nat) : IProp GF :=
  iprop(⌜o + j ≤ bs.length⌝ ∗ os.ownOff bf (W64 j) ∗ os.ownOff f (W64 (o + j)) ∗
    io.copyDst i (· = ((bs.map Prod.fst).drop o).take j))

/-- **The copy's end** (`io.CopyFiles.spec`'s post): on `err = nil` the destination holds the source's
bytes from `o` on and both offsets are at the ends; otherwise the destination is whole, with any bytes. -/
def io.cpFin (bf f : Loc) (i : Ino) (o : Nat) (bs : List ByteG) (err : GoInterface) : IProp GF :=
  iprop(io.copyDst i (fun vs => err = interface.nil → vs = (bs.map (·.1)).drop o) ∗
    ∃ (od os' : w64), os.ownOff bf od ∗ os.ownOff f os' ∗
      ⌜err = interface.nil → os' = W64 bs.length ∧ od = W64 (bs.length - o)⌝)

/-- The copy at the source's end is finished, whatever the error. -/
theorem io.cpS_fin_end (bf f : Loc) (i : Ino) (o : Nat) (bs : List ByteG) (j : Nat) (err : GoInterface)
    (hj : o + j = bs.length) :
    io.cpS (GF := GF) bf f i o bs j ⊢ io.cpFin bf f i o bs err := by
  unfold io.cpS io.cpFin
  iintro ⟨-, Hd, Hs, Hc⟩
  isplitl [Hc]
  · iapply (io.copyDst_mono i _ _ ?_) $$ Hc
    intro vs h _
    rw [h, List.take_of_length_le]
    simp only [List.length_drop, List.length_map]; omega
  · iexists W64 j, W64 (o + j)
    iframe
    ipureintro
    intro _
    constructor
    · congr 1; push_cast; omega
    · congr 1; push_cast; omega

/-- A copy that failed is finished, wherever it stopped. -/
theorem io.cpS_fin_err (bf f : Loc) (i : Ino) (o : Nat) (bs : List ByteG) (j : Nat) (err : GoInterface)
    (he : err ≠ interface.nil) :
    io.cpS (GF := GF) bf f i o bs j ⊢ io.cpFin bf f i o bs err := by
  unfold io.cpS io.cpFin
  iintro ⟨-, Hd, Hs, Hc⟩
  isplitl [Hc]
  · iapply (io.copyDst_mono i _ _ ?_) $$ Hc
    intro vs _ h; exact absurd h he
  · iexists W64 j, W64 (o + j)
    iframe
    ipureintro
    intro h; exact absurd h he

/-- **The fallback's copy** (see the file header). -/
theorem io.wp_copyGeneric (wp_WriteAt : os.File.WriteAt.specLong (GF := GF) (hG := hG))
    (bf f : Loc) (fdd fds : w64) (nd ns : GoString) (dd ds : OsFd) (m : OsMeta) (qm qb : DFrac)
    (bs : List ByteG) (o j : Nat)
    (hfdd : 0 ≤ fdd.toInt) (hfds : 0 ≤ fds.toInt) (hwr : dd.writable = true) (hrd : ds.readable = true)
    (hbs : bs.length = m.size) (hm : m.size < 2 ^ 61) :
    {{ osInv (GF := GF) ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        os.ownFile bf fdd nd (DFrac.own 1) ∗ osFd fdd (DFrac.own 1) dd ∗
        os.ownFile f fds ns (DFrac.own 1) ∗ osFd fds (DFrac.own 1) ds ∗
        osMeta ds.ino qm m ∗ osBytes ds.ino 0 qb bs ∗ io.cpS bf f dd.ino o bs j }}
      (App (App (Val (@! _root_.Perennial.io.Copy))
        (Val #(interface.mkOk os.fileWithoutReadFrom.ty #(os.fileWithoutReadFrom.mk os.noReadFrom.mk bf))))
        (Val #(interface.mkOk os.fileWithoutWriteTo.ty #(os.fileWithoutWriteTo.mk os.noWriteTo.mk f))))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
        os.ownFile bf fdd nd (DFrac.own 1) ∗ osFd fdd (DFrac.own 1) dd ∗
        os.ownFile f fds ns (DFrac.own 1) ∗ osFd fds (DFrac.own 1) ds ∗
        osMeta ds.ino qm m ∗ osBytes ds.ino 0 qb bs ∗ io.cpFin bf f dd.ino o bs err }} := by
  wp_start as ⟨#Hinv, #Hio, Hbf, Hfdd, Hf, Hfds, Hm, Hbs, HS⟩
  ihave Hi := _root_.Perennial.io.isInit_access $$ Hio
  icases Hi with ⟨-, #HSW, #HIW, -, #HEOF, -⟩
  iunfold errors.newVar at HSW HIW HEOF
  icases HSW with ⟨%xsw, #HSW, -⟩
  icases HIW with ⟨%xiw, #HIW, -⟩
  icases HEOF with ⟨%xeof, #HEOF, -⟩
  have hwt : go.typeSetContains os.fileWithoutWriteTo.ty _root_.Perennial.io.WriterTo.ty = false := by
    rw [go.typeSetContains_underlying, go.typeSetElemsContains_cons,
      go.typeSetElemContains_method_none _ (by
        simp [go.methodSetLookup_cons, go.methodSetLookup_nil])]
  have hrf : go.typeSetContains os.fileWithoutReadFrom.ty _root_.Perennial.io.ReaderFrom.ty = false := by
    rw [go.typeSetContains_underlying, go.typeSetElemsContains_cons,
      go.typeSetElemContains_method_none _ (by
        simp [go.methodSetLookup_cons, go.methodSetLookup_nil])]
  wp_auto
  wp_func_call
  wp_call
  wp_auto
  simp only [hwt]
  wp_auto
  simp only [hrf]
  wp_auto
  wp_apply (wp_slice_make2 (V := w8) (W64 32768)) as %sl ⟨Hsl, -⟩
  · ipureintro; decide
  ihave HI : (∃ (j : Nat) (W : w64) (bv : List w8),
      "written" ∷ written_ptr ↦ W ∗ "err" ∷ err_ptr ↦ GoInterface.nil ∗ "buf" ∷ buf_ptr ↦ sl ∗
      "Hsl" ∷ sl ↦* bv ∗ "HS" ∷ io.cpS bf f dd.ino o bs j ∗
      "Hbf" ∷ os.ownFile bf fdd nd (DFrac.own 1) ∗ "Hfdd" ∷ osFd fdd (DFrac.own 1) dd ∗
      "Hf" ∷ os.ownFile f fds ns (DFrac.own 1) ∗ "Hfds" ∷ osFd fds (DFrac.own 1) ds ∗
      "Hm" ∷ osMeta ds.ino qm m ∗ "Hbs" ∷ osBytes ds.ino 0 qb bs ∗
      "%Hbv" ∷ ⌜bv.length = 32768⌝ : IProp GF) $$ [written err buf Hsl HS Hbf Hfdd Hf Hfds Hm Hbs]
  · iexists j, W64 0, _
    iframe
    unfold named
    ipureintro
    exact List.length_replicate ..
  wp_for HI
  try simp only [_root_.decide_true, ↓reduceIte]
  try wp_auto
  wp_method_call
  wp_call
  iunfold io.cpS at HS
  icases HS with ⟨%hj, Hod, Hos, Hdst⟩
  have hbvne : bv ≠ [] := by intro h; rw [h] at Hbv; simp at Hbv
  have hojI := os.cfr_natInt (o + j) (by omega)
  have hojN := (os.cfr_natZ (o + j) (by omega)).2
  push_cast at hojI hojN
  wp_apply (os.File.Read.wp_eof f fds ns (DFrac.own 1) sl bv (W64 (o + j)) (DFrac.own 1) qm qb ds m bs _
    hfds hrd (by omega) hbs (by rw [hojI, Hbv]; omega))
    $$ [Hf Hos Hsl Hfds Hm Hbs] as %nr %er ⟨Hf, Hfds, Hm, Hbs, %k, %hk, Hsl, Hos, Her⟩
  · iframe; iframe #
  obtain ⟨rfl, hkbv, hkbs⟩ := hk
  rw [hojN] at hkbs
  rw [hojN]
  have hkZ : sint.Z (W64 (k : Int)) = k := (os.cfr_natZ k (by omega)).1
  have hkN : (W64 (k : Int)).toNat = k := (os.cfr_natZ k (by omega)).2
  have hz0 : sint.Z (W64 0) = 0 := rfl
  icases Her with (%he | %he | ⟨%hk0, %pe, %hpe, -, %e, -, -⟩)
  · -- `nil`, `k > 0` bytes: write them
    obtain ⟨rfl, hk0⟩ := he
    have hkp : 0 < k := by rcases hk0 with h | h; exact h; exact absurd h hbvne
    rw [decide_eq_true (show sint.Z (W64 0) < sint.Z (W64 (k : Int)) by rw [hkZ, hz0]; omega)]
    wp_auto
    ihave %Hwf := ownSlice_wf $$ Hsl
    ihave %Hlen := ownSlice_len $$ Hsl
    have hrl : (((bs.map Prod.fst).drop (o + j)).take k ++ bv.drop k).length = 32768 := by
      simp only [List.length_append, List.length_take, List.length_drop, List.length_map]; omega
    have hsll : sint.Z sl.len = 32768 := by
      have h1 := Hlen.1; have h2 := Hlen.2
      simp only [sint.nat, sint.Z, List.length_append, List.length_take, List.length_drop,
        List.length_map] at h1 h2 ⊢; omega
    have hb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (W64 (k : Int)) ∧
        sint.Z (W64 (k : Int)) ≤ sint.Z sl.cap := by
      rw [hz0, hkZ]; refine ⟨Int.le_refl _, by omega, ?_⟩
      have := Hwf.2; simp only [sint.Z] at this hsll ⊢; omega
    simp only [hb, _root_.and_self, ↓reduceIte]
    wp_auto
    wp_method_call
    wp_call
    icases (ownSlice_split_all (W64 (k : Int)) sl _ _ ⟨by rw [hkZ]; omega, by rw [hkZ, hsll]; omega⟩).1 $$ Hsl
      with ⟨Hs1, Hs2⟩
    have hsk : sint.nat (W64 (k : Int)) = k := by
      have : sint.nat (W64 (k : Int)) = (sint.Z (W64 (k : Int))).toNat := rfl
      rw [this, hkZ]; simp
    have hdata : (((bs.map Prod.fst).drop (o + j)).take k ++ bv.drop k).take (sint.nat (W64 (k : Int))) =
        ((bs.map Prod.fst).drop (o + j)).take k := by
      have hl1 : k ≤ (((bs.map Prod.fst).drop (o + j)).take k).length := by
        simp only [List.length_take, List.length_drop, List.length_map]; omega
      rw [hsk, List.take_append_of_le_length hl1, List.take_take, Nat.min_self]
    rw [hdata]
    have hdl : (((bs.map Prod.fst).drop (o + j)).take k).length = k := by
      simp only [List.length_take, List.length_drop, List.length_map]; omega
    have hvl : (((bs.map Prod.fst).drop o).take j).length = j := by
      simp only [List.length_take, List.length_drop, List.length_map]; omega
    ihave ⟨%md, %xsd, Hdm, Hdb, Hde, Hmc, %hd⟩ := io.copyDst_open dd.ino _ k $$ Hdst
    obtain ⟨hok, hxl, hxv, hms⟩ := hd
    rw [hvl] at hms
    rw [hvl]
    have hjN := (os.cfr_natZ j (by omega)).2
    have hjI := os.cfr_natInt j (by omega)
    have hW := os.File.Write.wp_long wp_WriteAt bf fdd nd (DFrac.own 1)
      (slice.slice sl w8 (W64 0) (W64 (k : Int))) (((bs.map Prod.fst).drop (o + j)).take k)
      (DFrac.own 1) (W64 j) (DFrac.own 1) dd md [] hfdd hwr (by omega) (by rw [hjN]; omega) hok.2.2.1
      (by omega) (by rw [hjN, hdl, hms]; simp) (by rw [hjI, hdl]; omega)
    rw [hjN, hdl] at hW
    wp_apply hW $$ [Hbf Hod Hs1 Hfdd Hdm Hde Hmc] as %nw %ew ⟨Hbf, Hs1, Hfdd, -, Hwr, #Hew⟩
    · iframe; iframe #
    icases Hwr with (⟨%ys, %hs, Hdm, Hys, Hod⟩ | ⟨%j1, %A, %E, %ys, %hs, Hdm, Hys, Hod⟩)
    · -- the write succeeded
      obtain ⟨rfl, rfl, hpw⟩ := hs
      rw [decide_eq_false (show ¬ sint.Z (W64 (k : Int)) < sint.Z (W64 0) by rw [hkZ, hz0]; omega)]
      wp_auto
      rw [decide_eq_false (show ¬ sint.Z (W64 (k : Int)) < sint.Z (W64 (k : Int)) by omega)]
      wp_auto
      have hcw := io.copyDst_wrote (GF := GF) dd.ino md (pwPost md j k k) j xsd ys
        (((bs.map Prod.fst).drop (o + j)).take k) k k hms hok hxl (Nat.le_refl _) (by omega) (Or.inl rfl)
        hpw.1 (fun i hi => (hpw.2 i hi).1)
      have hval : xsd.map (·.1) ++ (((bs.map Prod.fst).drop (o + j)).take k).take k =
          ((bs.map Prod.fst).drop o).take (j + k) := by
        rw [hxv, List.take_take, Nat.min_self, List.take_add, List.drop_drop]
      rw [hval] at hcw
      ihave Hdst := hcw $$ [Hdm Hdb Hys]
      · iframe
      wp_for_post
      iframe
      iexists (j + k), _, (((bs.map Prod.fst).drop (o + j)).take k ++
        (((bs.map Prod.fst).drop (o + j)).take k ++ bv.drop k).drop (sint.nat (W64 (k : Int))))
      iframe
      isplitl [Hs1 Hs2]
      · have e := ownSlice_combine (GF := GF) (V := w8) (W64 (k : Int)) sl (DFrac.own 1)
          (((bs.map Prod.fst).drop (o + j)).take k)
          ((((bs.map Prod.fst).drop (o + j)).take k ++ bv.drop k).drop (sint.nat (W64 (k : Int))))
          (W64 0) sl.len ⟨by rw [hdl, hsk]; rfl, by decide, by rw [hz0, hkZ]; omega, by rw [hkZ, hsll]; omega⟩
        iapply ownSlice_trivial_slice_2
        iapply e $$ Hs1 Hs2
      isplitl [Hod Hos Hdst]
      · iunfold io.cpS
        rw [os.cfr_W64_addI, os.cfr_W64_addI]
        push_cast
        rw [show ((o : Int) + j + k) = o + (j + k) by omega]
        unfold named
        iframe
        ipureintro; omega
      ipureintro
      simp only [List.length_append, List.length_drop, List.length_take, List.length_map, hsk]
      omega
    · -- the write failed: the copy ends with its error
      obtain ⟨hew, hjA, hAk, hpw, -, -⟩ := hs
      have hcw := io.copyDst_wrote (GF := GF) dd.ino md (os.pwPostE md j A j1 E) j xsd ys
        (((bs.map Prod.fst).drop (o + j)).take k) A j1 hms hok hxl hjA (by omega) (Or.inr ⟨E, rfl⟩)
        hpw.1 (fun i hi => (hpw.2 i hi).1)
      ihave Hdst := hcw $$ [Hdm Hdb Hys]
      · iframe
      rcases ew with ei | _
      rotate_left
      · exact absurd rfl hew
      wp_if_destruct
      all_goals
        repeat (first | wp_if_destruct | wp_auto)
      all_goals
        wp_for_post
        iapply HΦ
        iframe
        iunfold io.cpFin
        isplitl [Hdst]
        · iapply (io.copyDst_mono _ _ _ ?_) $$ Hdst
          intro vs _ h; cases h
        · iexists _, _
          iframe
          ipureintro; intro h; cases h
  · -- `io.EOF` at the source's end: the copy is done
    obtain ⟨hk0, -, hend, rfl⟩ := he
    subst hk0
    rw [decide_eq_false (show ¬ sint.Z (W64 0) < sint.Z (W64 ((0 : Nat) : Int)) by decide)]
    repeat (first | wp_if_destruct | wp_auto)
    wp_for_post
    iapply HΦ
    iframe
    iapply (io.cpS_fin_end bf f dd.ino o bs j _ (by omega))
    iunfold io.cpS
    rw [show W64 ((o : Int) + j) + W64 ((0 : Nat) : Int) = W64 ((o : Int) + j) by simp]
    iframe
    ipureintro; omega
  · -- an errno: the copy ends with its error
    subst hk0 hpe
    rw [decide_eq_false (show ¬ sint.Z (W64 0) < sint.Z (W64 ((0 : Nat) : Int)) by decide)]
    repeat (first | wp_if_destruct | wp_auto)
    wp_for_post
    iapply HΦ
    iframe
    iapply (io.cpS_fin_err bf f dd.ino o bs j _ (by intro h; cases h))
    iunfold io.cpS
    rw [show W64 ((o : Int) + j) + W64 ((0 : Nat) : Int) = W64 ((o : Int) + j) by simp]
    iframe
    ipureintro; omega

end proof

end EtcdGrove
end Perennial
