/-
`io.Copy`'s specs (`Spec/io/Copy.lean`), proved over Perennial's translation of Go's `Copy`,
`copyBuffer` and `discard.ReadFrom`, from the reader's and the writer's stream contracts
(`io.streamReader`, `io.streamWriter`) and `io`'s package fact (`Discard` holds `discard{}`,
`blackHolePool` a pool of 8192-byte buffers). The lab assumed them (`KitStd.Axiom.io.Copy`).
-/
module

public import Spec.io.Copy
public import Perennial.Spec.sync.Pool__Get
public import Perennial.Spec.sync.Pool__Put

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : io.Assumptions]

theorem io.sintZ_of_lt (x : w64) (h : x.toNat < 2 ^ 63) : sint.Z x = x.toNat := by
  simp only [sint.Z]; rw [BitVec.toInt_eq_toNat_cond]; split <;> omega

theorem io.toNat_of_sintZ (x : w64) (h : 0 ≤ sint.Z x) : x.toNat = sint.nat x := by
  have : sint.nat x = (sint.Z x).toNat := rfl
  rw [this]; simp only [sint.Z] at h ⊢; rw [BitVec.toInt_eq_toNat_cond] at h ⊢; split at h <;> omega

/-- An `errors.New` variable's value is pointer-typed and not `nil`. -/
theorem io.newVar_val (x : Loc) :
    io.ptrTyped (interface.mkOk (go.GoType.PointerType errors.errorString.ty) #x) ∧
      interface.mkOk (go.GoType.PointerType errors.errorString.ty) #x ≠ interface.nil := by
  refine ⟨?_, by simp [interface.mkOk]⟩
  intro ii T h _; cases h; exact ⟨x, rfl⟩

/-- `copyBuffer(dst, src, nil)` of the generic loop: a reader `src` that is neither an
`io.WriterTo` nor a `*LimitedReader`, a writer `dst` that is not an `io.ReaderFrom`. -/
theorem io.wp_copyBuffer_stream (td ts : go.GoType) (vd vs : val) (R W : List w8 → IProp GF)
    (bs ws : List w8) (eof : GoInterface)
    (hwt : go.typeSetContains ts io.WriterTo.ty = false)
    (hlr : ts ≠ go.GoType.PointerType io.LimitedReader.ty)
    (hrf : go.typeSetContains td io.ReaderFrom.ty = false)
    (hbs : bs.length < 2 ^ 63) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.io ∗ globalAddr io.EOF ↦□ eof ∗ R bs ∗ W ws ∗
        io.streamReader (interface.mk ts vs) R eof ∗ io.streamWriter (interface.mk td vd) W }}
      (App (App (App (Val (@! io.copyBuffer)) (Val #(interface.mkOk td vd)))
        (Val #(interface.mkOk ts vs))) (Val #(slice.nil)))
    {{ (written : w64) (err : GoInterface), RET (PairV #written #err);
        ∃ kr kw : Nat, ⌜kw ≤ kr ∧ kr ≤ bs.length ∧ sint.Z written = kw ∧
          (err = interface.nil → kr = bs.length ∧ kw = bs.length)⌝ ∗
        R (bs.drop kr) ∗ W (ws ++ bs.take kw) }} := by
  wp_start as ⟨#Heof, HR, HW, #Hrd, #Hwr⟩
  iunfold io.streamReader at Hrd
  iunfold io.streamWriter at Hwr
  ihave Hi := io.isInit_access $$ Hpkg
  icases Hi with ⟨-, #HSW, -, -, #HEOF, -⟩
  iunfold errors.newVar at HSW HEOF
  icases HSW with ⟨%xsw, #HSW, -⟩
  icases HEOF with ⟨%xeof, #HEOF, -⟩
  icombine Heof HEOF gives %Heq
  subst Heq
  wp_auto
  simp only [hwt]
  wp_auto
  simp only [hrf]
  wp_auto
  simp only [hlr, ↓reduceIte, _root_.decide_false]
  wp_auto
  wp_apply (wp_slice_make2 (V := w8) (W64 32768)) as %sl ⟨Hsl, -⟩
  · ipureintro; decide
  ihave HI : (∃ (Wn : w64) (k : Nat) (bv : List w8),
      "written" ∷ written_ptr ↦ Wn ∗ "err" ∷ err_ptr ↦ GoInterface.nil ∗ "buf" ∷ buf_ptr ↦ sl ∗
      "Hsl" ∷ sl ↦* bv ∗ "HR" ∷ R (bs.drop k) ∗ "HW" ∷ W (ws ++ bs.take k) ∗
      "%Hinv" ∷ ⌜bv.length = 32768 ∧ Wn.toNat = k ∧ k ≤ bs.length⌝ : IProp GF)
      $$ [written err buf Hsl HR HW]
  · iexists W64 0, 0, _
    simp only [List.drop_zero, List.take_zero, List.append_nil]
    iframe
    ipureintro
    refine ⟨?_, rfl, Nat.zero_le _⟩
    rw [List.length_replicate]
  wp_for HI
  try simp only [_root_.decide_true, ↓reduceIte]
  try wp_auto
  obtain ⟨hbv, hWk, hkb⟩ := Hinv
  wp_apply Hrd $$ %sl %bv %(bs.drop k) [] HR Hsl as %n %er %Hn Hsl HR
  · ipureintro; omega
  obtain ⟨hn0, hnb, hnc, hne, hpt⟩ := Hn
  ihave %Hwf := ownSlice_wf $$ Hsl
  ihave %Hlen := ownSlice_len $$ Hsl
  have hnz : sint.Z n = sint.nat n := by
    have : sint.nat n = (sint.Z n).toNat := rfl
    omega
  have hdl : (bs.drop k).length = bs.length - k := List.length_drop
  have hbuf' : ((bs.drop k).take (sint.nat n) ++ bv.drop (sint.nat n)).length = bv.length := by
    simp only [List.length_append, List.length_take, List.length_drop]; omega
  have hsll : sint.Z sl.len = bv.length := by
    have h1 := Hlen.1; have h2 := Hlen.2
    rw [hbuf'] at h1
    have : sint.nat sl.len = (sint.Z sl.len).toNat := rfl
    omega
  have hWz : sint.Z Wn = k := by rw [io.sintZ_of_lt _ (by omega)]; omega
  wp_if_destruct
  · -- `nr > 0`: write `buf[0:nr]`
    rw [show sint.Z (W64 0) = 0 from rfl] at Hif
    have hb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z n ∧ sint.Z n ≤ sint.Z sl.cap := by
      rw [show sint.Z (W64 0) = 0 from rfl]; omega
    simp only [hb, _root_.and_self, ↓reduceIte]
    wp_auto
    icases (ownSlice_split_all n sl _ _ ⟨by omega, by omega⟩).1 $$ Hsl with ⟨Hs1, Hs2⟩
    have htk : ((bs.drop k).take (sint.nat n) ++ bv.drop (sint.nat n)).take (sint.nat n) =
        (bs.drop k).take (sint.nat n) := by
      have hl : ((bs.drop k).take (sint.nat n)).length = sint.nat n := by
        simp only [List.length_take]; omega
      rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
    rw [htk]
    wp_apply Hwr $$ %_ %((bs.drop k).take (sint.nat n)) %(ws ++ bs.take k) %(DFrac.own 1) HW Hs1
      as %nw %ew %Hnw HW Hs1
    obtain ⟨hnw0, hnwc⟩ := Hnw
    have htl : ((bs.drop k).take (sint.nat n)).length = sint.nat n := by
      simp only [List.length_take]; omega
    rw [htl] at hnwc
    have hnwz : sint.Z nw = sint.nat nw := by
      have : sint.nat nw = (sint.Z nw).toNat := rfl
      omega
    wp_if_destruct
    · exfalso; rw [show sint.Z (W64 0) = 0 from rfl] at Hif; omega
    wp_if_destruct
    · exfalso; omega
    try wp_auto
    have hWnw : (Wn + nw).toNat = k + sint.nat nw := by
      rw [BitVec.toNat_add, io.toNat_of_sintZ nw hnw0]; omega
    have hWnwz : sint.Z (Wn + nw) = (k + sint.nat nw : Nat) := by
      rw [io.sintZ_of_lt _ (by omega), hWnw]
    have hWtake : ws ++ bs.take k ++ ((bs.drop k).take (sint.nat n)).take (sint.nat nw) =
        ws ++ bs.take (k + sint.nat nw) := by
      rw [List.take_take, Nat.min_eq_left hnwc, List.take_add, List.append_assoc]
    rw [hWtake]
    have hdd : (bs.drop k).drop (sint.nat n) = bs.drop (k + sint.nat n) := by
      rw [List.drop_drop]
    rw [hdd]
    rcases ew with ei | _
    · -- the write failed: the loop ends
      wp_auto
      wp_for_post
      iapply HΦ
      iexists k + sint.nat n, k + sint.nat nw
      iframe
      ipureintro
      exact ⟨by omega, by omega, hWnwz, fun h => by cases h⟩
    wp_auto
    wp_if_destruct
    · -- `nr == nw`: on to `er`
      subst Hif
      rcases er with ei | _
      · -- `er != nil`: the loop ends
        obtain ⟨ty, v⟩ := ei
        wp_auto
        by_cases hty : ty = go.GoType.PointerType errors.errorString.ty
        · obtain ⟨l', hl'⟩ := hpt ⟨ty, v⟩ _ rfl hty
          simp only at hl'
          subst hty hl'
          simp only [↓reduceIte]
          wp_auto
          wp_if_destruct
          · -- `io.EOF`: `err` stays `nil`, and the stream is exhausted
            have hall : sint.nat n = (bs.drop k).length := hne (by rw [Hif])
            wp_for_post
            iapply HΦ
            iexists (k + sint.nat n), (k + sint.nat n)
            iframe
            ipureintro
            exact ⟨Nat.le_refl _, by omega, hWnwz, fun _ => ⟨by omega, by omega⟩⟩
          · -- not `io.EOF`: `err = er`
            wp_for_post
            iapply HΦ
            iexists (k + sint.nat n), (k + sint.nat n)
            iframe
            ipureintro
            exact ⟨Nat.le_refl _, by omega, hWnwz, fun h => by cases h⟩
        · simp only [hty, ↓reduceIte]
          wp_auto
          wp_for_post
          iapply HΦ
          iexists (k + sint.nat n), (k + sint.nat n)
          iframe
          ipureintro
          exact ⟨Nat.le_refl _, by omega, hWnwz, fun h => by cases h⟩
      · -- `er == nil`: next iteration
        wp_auto
        wp_for_post
        iframe
        have hd : ((bs.drop k).take (sint.nat n)).length = sint.nat n := by
          simp only [List.length_take]; omega
        iexists (Wn + n), (k + sint.nat n),
          ((bs.drop k).take (sint.nat n) ++
            ((bs.drop k).take (sint.nat n) ++ bv.drop (sint.nat n)).drop (sint.nat n))
        iframe
        isplitl [Hs1 Hs2]
        · have e := ownSlice_combine (GF := GF) (V := w8) n sl (DFrac.own 1)
            ((bs.drop k).take (sint.nat n))
            (((bs.drop k).take (sint.nat n) ++ bv.drop (sint.nat n)).drop (sint.nat n)) (W64 0) sl.len
            ⟨by rw [hd]; rfl, by decide, by omega, by omega⟩
          iapply ownSlice_trivial_slice_2
          iapply e $$ Hs1 Hs2
        ipureintro
        refine ⟨?_, by omega, by omega⟩
        simp only [List.length_append, List.length_drop, List.length_take]; omega
    · -- a short write: `ErrShortWrite`
      wp_for_post
      iapply HΦ
      iexists k + sint.nat n, k + sint.nat nw
      iframe
      ipureintro
      exact ⟨by omega, by omega, hWnwz, fun h => by simp [interface.mkOk] at h⟩
  · -- `nr == 0`: nothing written
    rw [show sint.Z (W64 0) = 0 from rfl] at Hif
    have hn00 : sint.nat n = 0 := by omega
    have hdd : (bs.drop k).drop (sint.nat n) = bs.drop k := by rw [hn00, List.drop_zero]
    rw [hdd]
    rcases er with ei | _
    · -- `er != nil`: the loop ends
      obtain ⟨ty, v⟩ := ei
      wp_auto
      by_cases hty : ty = go.GoType.PointerType errors.errorString.ty
      · obtain ⟨l', hl'⟩ := hpt ⟨ty, v⟩ _ rfl hty
        simp only at hl'
        subst hty hl'
        simp only [↓reduceIte]
        wp_auto
        wp_if_destruct
        · -- `io.EOF`: `err` stays `nil`, and the stream is exhausted
          have hall : sint.nat n = (bs.drop k).length := hne (by rw [Hif])
          wp_for_post
          iapply HΦ
          iexists k, k
          iframe
          ipureintro
          exact ⟨Nat.le_refl _, by omega, hWz, fun _ => ⟨by omega, by omega⟩⟩
        · -- not `io.EOF`: `err = er`
          wp_for_post
          iapply HΦ
          iexists k, k
          iframe
          ipureintro
          exact ⟨Nat.le_refl _, by omega, hWz, fun h => by cases h⟩
      · simp only [hty, ↓reduceIte]
        wp_auto
        wp_for_post
        iapply HΦ
        iexists k, k
        iframe
        ipureintro
        exact ⟨Nat.le_refl _, by omega, hWz, fun h => by cases h⟩
    · -- `er == nil`: next iteration
      wp_auto
      wp_for_post
      iframe
      iexists Wn, k, ((bs.drop k).take (sint.nat n) ++ bv.drop (sint.nat n))
      rw [show sint.nat n = 0 by omega, List.drop_zero]
      iframe
      ipureintro
      refine ⟨?_, hWk, hkb⟩
      simp only [List.take_zero, List.nil_append]; exact hbv

/-- `Copy(dst, src)` is `copyBuffer(dst, src, nil)` (`io.wp_copyBuffer_stream`). -/
theorem io.Copy.wp_proof : io.Copy.spec (GF := GF) (hG := hG) := by
  intro td ts vd vs R W bs ws eof hwt hlr hrf hbs
  wp_start as ⟨#Heof, HR, HW, #Hrd, #Hwr⟩
  wp_auto
  wp_apply io.wp_copyBuffer_stream td ts vd vs R W bs ws eof hwt hlr hrf hbs
    $$ [HR HW] as %wr %e ⟨%kr, %kw, %H, HR, HW⟩
  · iframe; iframe #
  try wp_auto
  iapply HΦ
  iexists kr, kw
  iframe
  ipureintro; exact H

/-- `discard{}.ReadFrom(src)`: reads `src` into a buffer of `blackHolePool` until an error;
`(n, nil)` on `io.EOF`. -/
theorem io.wp_discard_ReadFrom
    (wp_Get : sync.Pool.Get.spec (GF := GF) (hG := hG))
    (wp_Put : sync.Pool.Put.spec (GF := GF) (hG := hG))
    (ts : go.GoType) (vs : val) (R : List w8 → IProp GF) (bs : List w8) (eof : GoInterface)
    (hbs : bs.length < 2 ^ 63) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.io ∗ globalAddr io.EOF ↦□ eof ∗ R bs ∗
        io.streamReader (interface.mk ts vs) R eof }}
      (App (Val #(methods io.discard.ty go!"ReadFrom" #io.discard.mk)) (Val #(interface.mkOk ts vs)))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
        ∃ k : Nat, ⌜k ≤ bs.length ∧ sint.Z n = k ∧ (err = interface.nil → k = bs.length)⌝ ∗
          R (bs.drop k) }} := by
  wp_start as ⟨#Heof, HR, #Hrd⟩
  iunfold io.streamReader at Hrd
  ihave Hi := io.isInit_access $$ Hpkg
  icases Hi with ⟨-, -, -, -, #HEOF, -, -, -, -, -, -, ⟨%f, %Hf, #Hpool⟩, -⟩
  iunfold errors.newVar at HEOF
  icases HEOF with ⟨%xeof, #HEOF, -⟩
  icombine Heof HEOF gives %Heq
  subst Heq
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_Get (globalAddr io.blackHolePool) f iprop(True) io.blackHoleElem as %x ⟨Hx, -⟩
  · iframe #
  icases Hx with (Hx | ⟨%Hfn, -⟩)
  rotate_left
  · exact absurd Hfn Hf
  unfold io.blackHoleElem
  icases Hx with ⟨%l, %sl, %bv, %Hx, Hl, Hsl⟩
  obtain ⟨rfl, hbv⟩ := Hx
  wp_auto
  ihave HI : (∃ (N : w64) (k : Nat) (bv : List w8) (e : GoInterface) (rs : w64),
      "n" ∷ n_ptr ↦ N ∗ "err" ∷ err_ptr ↦ e ∗ "readSize" ∷ readSize_ptr ↦ rs ∗
      "Hsl" ∷ sl ↦* bv ∗ "HR" ∷ R (bs.drop k) ∗
      "%Hinv" ∷ ⌜bv.length = 8192 ∧ N.toNat = k ∧ k ≤ bs.length⌝ : IProp GF)
      $$ [n err readSize Hsl HR]
  · iexists W64 0, 0, bv, _, _
    simp only [List.drop_zero]
    iframe
    ipureintro
    exact ⟨hbv, rfl, Nat.zero_le _⟩
  wp_for HI
  try simp only [_root_.decide_true, ↓reduceIte]
  try wp_auto
  obtain ⟨hbv', hNk, hkb⟩ := Hinv
  wp_apply Hrd $$ %sl %bv %(bs.drop k) [] HR Hsl as %m %er %Hm Hsl HR
  · ipureintro; omega
  obtain ⟨hm0, hmb, hmc, hme, hpt⟩ := Hm
  have hdl : (bs.drop k).length = bs.length - k := List.length_drop
  have hmz : sint.Z m = sint.nat m := by
    have : sint.nat m = (sint.Z m).toNat := rfl
    omega
  have hbuf' : ((bs.drop k).take (sint.nat m) ++ bv.drop (sint.nat m)).length = 8192 := by
    simp only [List.length_append, List.length_take, List.length_drop]; omega
  have hdd : (bs.drop k).drop (sint.nat m) = bs.drop (k + sint.nat m) := by
    rw [List.drop_drop]
  rw [hdd]
  try wp_auto
  have hNm : (N + m).toNat = k + sint.nat m := by
    rw [BitVec.toNat_add, io.toNat_of_sintZ m hm0]; omega
  have hNmz : sint.Z (N + m) = (k + sint.nat m : Nat) := by
    rw [io.sintZ_of_lt _ (by omega), hNm]
  rcases er with ei | _
  · -- `err != nil`: back to the pool, and return
    wp_auto
    wp_apply wp_Put (globalAddr io.blackHolePool) f iprop(True) io.blackHoleElem
      (interface.mkOk (go.GoType.PointerType (go.GoType.SliceType go.byte)) #l) $$ [Hl Hsl]
    · unfold io.blackHoleElem
      iframe #
      iexists l, sl, _
      iframe
      ipureintro; exact ⟨rfl, hbuf'⟩
    obtain ⟨ty, v⟩ := ei
    wp_auto
    by_cases hty : ty = go.GoType.PointerType errors.errorString.ty
    · obtain ⟨l', hl'⟩ := hpt ⟨ty, v⟩ _ rfl hty
      simp only at hl'
      subst hty hl'
      simp only [↓reduceIte]
      wp_auto
      wp_if_destruct
      · -- `io.EOF`: `(n, nil)`, the stream exhausted
        have hall : sint.nat m = (bs.drop k).length := hme (by rw [Hif])
        wp_for_post
        iapply HΦ
        iexists k + sint.nat m
        iframe
        ipureintro
        exact ⟨by omega, hNmz, fun _ => by omega⟩
      · wp_for_post
        iapply HΦ
        iexists k + sint.nat m
        iframe
        ipureintro
        exact ⟨by omega, hNmz, fun h => by cases h⟩
    · simp only [hty, ↓reduceIte]
      wp_auto
      wp_for_post
      iapply HΦ
      iexists k + sint.nat m
      iframe
      ipureintro
      exact ⟨by omega, hNmz, fun h => by cases h⟩
  · -- `err == nil`: next iteration
    wp_auto
    wp_for_post
    iframe
    iexists (N + m), (k + sint.nat m), ((bs.drop k).take (sint.nat m) ++ bv.drop (sint.nat m)), _, _
    iframe
    ipureintro
    exact ⟨hbuf', hNm, by omega⟩

/-- `copyBuffer(io.Discard, src, nil)`, for a reader `src` that is not an `io.WriterTo`:
`discard{}` is an `io.ReaderFrom`, so `discard.ReadFrom(src)`, which reads into a buffer of
`blackHolePool` until an error. -/
theorem io.wp_copyBuffer_discard
    (wp_Get : sync.Pool.Get.spec (GF := GF) (hG := hG))
    (wp_Put : sync.Pool.Put.spec (GF := GF) (hG := hG))
    (ts : go.GoType) (vs : val) (R : List w8 → IProp GF) (bs : List w8) (eof : GoInterface)
    (hwt : go.typeSetContains ts io.WriterTo.ty = false) (hbs : bs.length < 2 ^ 63) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.io ∗ globalAddr io.EOF ↦□ eof ∗ R bs ∗
        io.streamReader (interface.mk ts vs) R eof }}
      (App (App (App (Val (@! io.copyBuffer))
        (Val #(interface.mkOk io.discard.ty #io.discard.mk)))
        (Val #(interface.mkOk ts vs))) (Val #(slice.nil)))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
        ∃ k : Nat, ⌜k ≤ bs.length ∧ sint.Z n = k ∧ (err = interface.nil → k = bs.length)⌝ ∗
          R (bs.drop k) }} := by
  wp_start as ⟨#Heof, HR, #Hrd⟩
  ihave Hi := io.isInit_access $$ Hpkg
  icases Hi with ⟨-, -, -, -, #HEOF, -, -, -, -, -, -, ⟨%f, %Hf, #Hpool⟩, -⟩
  iunfold errors.newVar at HEOF
  icases HEOF with ⟨%xeof, #HEOF, -⟩
  icombine Heof HEOF gives %Heq
  subst Heq
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  have hrf : go.typeSetContains io.discard.ty io.ReaderFrom.ty = true := by
    go_type_set
  wp_auto
  simp only [hwt]
  wp_auto
  simp only [hrf]
  wp_auto
  wp_apply io.wp_discard_ReadFrom wp_Get wp_Put ts vs R bs _ hbs $$ [HR] as %n %e ⟨%k, %Hk, HR⟩
  · iframe; iframe #
  try wp_auto
  iapply HΦ
  iexists k
  iframe
  ipureintro; exact Hk

/-- `Copy(io.Discard, src)`: `Discard` holds `discard{}` (`io`'s fact), so `copyBuffer` reads
`src` through `discard.ReadFrom` (`io.wp_copyBuffer_discard`). -/
theorem io.Copy_Discard.wp_proof
    (wp_Get : sync.Pool.Get.spec (GF := GF) (hG := hG))
    (wp_Put : sync.Pool.Put.spec (GF := GF) (hG := hG)) :
    io.Copy_Discard.spec (GF := GF) (hG := hG) := by
  intro w ts vs R bs eof hwt hbs
  wp_start as ⟨#Hd, #Heof, HR, #Hrd⟩
  ihave Hi := io.isInit_access $$ Hpkg
  icases Hi with ⟨-, -, -, -, -, -, -, -, -, -, #HDV, -⟩
  icombine Hd HDV gives %Hw
  subst Hw
  wp_auto
  wp_apply io.wp_copyBuffer_discard wp_Get wp_Put ts vs R bs eof hwt hbs
    $$ [HR] as %n %e ⟨%k, %Hk, HR⟩
  · iframe; iframe #
  try wp_auto
  iapply HΦ
  iexists k
  iframe
  ipureintro; exact Hk

end proof

end Perennial
