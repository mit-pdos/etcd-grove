/-
`io.CopyN` of a `*SectionReader` (see `Spec/io/CopyN.lean`), proved over Perennial's translation of
Go's `CopyN`, `Copy`, `copyBuffer`, `LimitReader` and the `Read`s of `LimitedReader` and
`SectionReader`, from the `ReaderAt` and `Writer` contracts (`io.readerAtOk`, `io.writerOk`). An
axiom until 2026-11-21 (S4, 2026-11-18).
-/
module

public import Spec.io.CopyN

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.io.Assumptions]

/-- The section reader of `r` from `off`, `n` bytes long, `W` bytes into it. -/
abbrev io.secAt (r : GoInterfaceOk) (off n W : w64) : _root_.Perennial.io.SectionReader :=
  { r' := GoInterface.ok r, base' := off, off' := off + W, limit' := off + n, n' := n }

/-- A call of `ReadAt`, with `readerAtOk` kept folded in the caller's context. -/
theorem io.wp_readerAt_ReadAt (r : GoInterfaceOk) (P : IProp GF) (Hd : Nat → w8 → Prop)
    (b : GoSlice) (vs : List w8) (o : w64)
    (h : 0 ≤ sint.Z o ∧ vs.length ≤ 32768 ∧ o.toNat + vs.length < 2 ^ 63) :
    {{ io.readerAtOk r P Hd ∗ P ∗ b ↦* vs }}
      (App (App (Val #(methods r.ty go!"ReadAt" r.v)) (Val #b)) (Val #o))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
        P ∗ ∃ vs' : List w8, b ↦* vs' ∗
          ⌜vs'.length = vs.length ∧ n.toNat ≤ vs.length ∧
            (∀ i x, vs'[i]? = some x → i < n.toNat → Hd (o.toNat + i) x) ∧
            _root_.Perennial.io.ptrTyped err⌝ }} := by
  iintro %Φ ⟨#Hr, HP, Hb⟩ HΦ
  unfold io.readerAtOk
  iapply Hr $$ %b %vs %o [HP Hb] HΦ
  iframe HP Hb
  ipureintro; exact h

/-- `sr.Read(p)` with `W < n` bytes of the section read and `len(p) ≤ n - W`: one `ReadAt(p, off + W)`. -/
theorem io.wp_secReader_Read (sr : Loc) (r : GoInterfaceOk) (off n W : w64) (P : IProp GF)
    (Hd : Nat → w8 → Prop) (p : GoSlice) (vs : List w8)
    (hsum : off.toNat + n.toNat < 2 ^ 63) (hW : W.toNat < n.toNat)
    (hvs : vs.length ≤ n.toNat - W.toNat) (hvs' : vs.length ≤ 32768) :
    {{ sr ↦ io.secAt r off n W ∗ io.readerAtOk r P Hd ∗ P ∗ p ↦* vs }}
      (App (Val #(methods (go.GoType.PointerType _root_.Perennial.io.SectionReader.ty) go!"Read"
        #sr)) (Val #p))
    {{ (k : w64) (err : GoInterface), RET (PairV #k #err);
        sr ↦ io.secAt r off n (W + k) ∗ P ∗ ∃ vs' : List w8, p ↦* vs' ∗
          ⌜vs'.length = vs.length ∧ k.toNat ≤ vs.length ∧
            (∀ i x, vs'[i]? = some x → i < k.toNat → Hd (off.toNat + W.toNat + i) x) ∧
            _root_.Perennial.io.ptrTyped err⌝ }} := by
  wp_start as ⟨Hsr, #Hr, HP, Hp⟩
  ihave %Hlen := ownSlice_len $$ Hp
  wp_auto
  have hz : ∀ x : w64, x.toNat < 2 ^ 63 → sint.Z x = x.toNat := by
    intro x hx; simp only [sint.Z]; rw [BitVec.toInt_eq_toNat_cond]; split <;> omega
  have hon : (off + n).toNat = off.toNat + n.toNat := by
    rw [BitVec.toNat_add]; omega
  have how : (off + W).toNat = off.toNat + W.toNat := by
    rw [BitVec.toNat_add]; omega
  wp_if_destruct
  · exfalso
    rw [hz _ (by omega), hz _ (by omega)] at Hif
    omega
  have hmax : (off + n - (off + W)).toNat = n.toNat - W.toNat := by
    rw [BitVec.toNat_sub, hon, how]; omega
  wp_if_destruct
  · exfalso
    rw [hz _ (by omega), hmax] at Hif
    have : sint.Z p.len = vs.length := by
      have h1 := Hlen.1; have h2 := Hlen.2; simp only [sint.nat, sint.Z] at h1 h2 ⊢; omega
    omega
  wp_apply io.wp_readerAt_ReadAt r P Hd p vs (off + W) ⟨by rw [hz _ (by omega)]; omega, hvs',
      by rw [how]; omega⟩ $$ [HP Hp] as %k %err ⟨HP, %vs', Hp, %Hk⟩
  · iframe Hr HP Hp
  try wp_auto
  iapply HΦ
  rw [show off + W + k = off + (W + k) by word]
  iframe Hsr HP
  iexists vs'
  iframe Hp
  ipureintro
  obtain ⟨h1, h2, h3, h4⟩ := Hk
  rw [how] at h3
  exact ⟨h1, h2, h3, h4⟩

/-- The limited reader over the section reader at `sr`, `W` of its `n` bytes read. -/
abbrev io.limAt (sr : Loc) (n W : w64) : _root_.Perennial.io.LimitedReader :=
  { R' := interface.mkOk (go.GoType.PointerType _root_.Perennial.io.SectionReader.ty) #sr,
    N' := n - W }

/-- `l.Read(p)` of the limited reader over the section reader, `W ≤ n` bytes read: at most
`n - W` bytes of the section from `off + W`. -/
theorem io.wp_limReader_Read (l sr : Loc) (r : GoInterfaceOk) (off n W : w64) (P : IProp GF)
    (Hd : Nat → w8 → Prop) (p : GoSlice) (vs : List w8) (eof : GoInterface)
    (hsum : off.toNat + n.toNat < 2 ^ 63) (hW : W.toNat ≤ n.toNat) (hvs' : vs.length ≤ 32768)
    (heof : _root_.Perennial.io.ptrTyped eof) :
    {{ globalAddr _root_.Perennial.io.EOF ↦□ eof ∗ l ↦ io.limAt sr n W ∗
        sr ↦ io.secAt r off n W ∗ io.readerAtOk r P Hd ∗ P ∗ p ↦* vs }}
      (App (Val #(methods (go.GoType.PointerType _root_.Perennial.io.LimitedReader.ty) go!"Read"
        #l)) (Val #p))
    {{ (k : w64) (err : GoInterface), RET (PairV #k #err);
        l ↦ io.limAt sr n (W + k) ∗ sr ↦ io.secAt r off n (W + k) ∗ P ∗ ∃ vs' : List w8, p ↦* vs' ∗
          ⌜vs'.length = vs.length ∧ k.toNat ≤ vs.length ∧ W.toNat + k.toNat ≤ n.toNat ∧
            (∀ i x, vs'[i]? = some x → i < k.toNat → Hd (off.toNat + W.toNat + i) x) ∧
            _root_.Perennial.io.ptrTyped err⌝ }} := by
  wp_start as ⟨#Heof, Hl, Hsr, #Hr, HP, Hp⟩
  ihave %Hlen := ownSlice_len $$ Hp
  ihave %Hwf := ownSlice_wf $$ Hp
  have hz : ∀ x : w64, x.toNat < 2 ^ 63 → sint.Z x = x.toNat := by
    intro x hx; simp only [sint.Z]; rw [BitVec.toInt_eq_toNat_cond]; split <;> omega
  have hnw : (n - W).toNat = n.toNat - W.toNat := by
    rw [BitVec.toNat_sub]; omega
  have hpl : sint.Z p.len = vs.length := by
    have h1 := Hlen.1; have h2 := Hlen.2; simp only [sint.nat, sint.Z] at h1 h2 ⊢; omega
  wp_auto
  wp_if_destruct
  · -- nothing left: `0, EOF`
    have hWn : W = n := by
      rw [hz _ (by omega), hnw, show sint.Z (W64 0) = 0 from rfl] at Hif
      apply BitVec.eq_of_toNat_eq; omega
    subst hWn
    try wp_auto
    iapply HΦ
    rw [show W + W64 0 = W by word]
    iframe Hl Hsr HP
    iexists vs
    iframe Hp
    ipureintro
    refine ⟨rfl, by simp, by simp, fun i x _ hi => by simp at hi, heof⟩
  rw [hz _ (by omega), hnw, show sint.Z (W64 0) = 0 from rfl] at Hif
  wp_if_destruct
  · -- `len(p) > N`: `p = p[0:N]`
    rw [hz _ (by omega), hnw, hpl] at Hif
    have hN : sint.Z (n - W) = (n.toNat - W.toNat : Nat) := by rw [hz _ (by omega), hnw]
    have hb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (n - W) ∧ sint.Z (n - W) ≤ sint.Z p.cap := by
      rw [show sint.Z (W64 0) = 0 from rfl, hN]; omega
    simp only [hb, _root_.and_self, ↓reduceIte]
    wp_auto
    icases (ownSlice_split_all (n - W) p _ _ ⟨by omega, by omega⟩).1 $$ Hp with ⟨Hp1, Hp2⟩
    have hsn : sint.nat (n - W) = n.toNat - W.toNat := by
      have : sint.nat (n - W) = (sint.Z (n - W)).toNat := rfl
      rw [this, hN]; simp
    rw [hsn]
    wp_apply io.wp_secReader_Read sr r off n W P Hd _ (vs.take (n.toNat - W.toNat)) hsum (by omega)
        (by simp only [List.length_take]; omega) (by simp only [List.length_take]; omega)
      $$ [Hsr HP Hp1] as %k %err ⟨Hsr, HP, %vs', Hp1, %Hk⟩
    · iframe Hsr Hr HP Hp1
    try wp_auto
    iapply HΦ
    rw [show n - W - k = n - (W + k) by word]
    iframe Hl Hsr HP
    obtain ⟨h1, h2, h3, h4⟩ := Hk
    have htl : (vs.take (n.toNat - W.toNat)).length = n.toNat - W.toNat := by
      simp only [List.length_take]; omega
    iexists vs' ++ vs.drop (n.toNat - W.toNat)
    isplitl [Hp1 Hp2]
    · have e := ownSlice_combine (GF := GF) (V := w8) (n - W) p (DFrac.own 1) vs'
        (vs.drop (sint.nat (n - W))) (W64 0) p.len ⟨by rw [h1, htl, hsn]; rfl, by decide, by omega, by omega⟩
      rw [hsn] at e
      iapply ownSlice_trivial_slice_2
      iapply e $$ Hp1 Hp2
    ipureintro
    refine ⟨by simp only [List.length_append, List.length_drop]; omega, by omega, by omega,
      fun i x hx hi => ?_, h4⟩
    have hi' : i < vs'.length := by omega
    rw [List.getElem?_append_left hi'] at hx
    exact h3 i x hx hi
  · rw [hz _ (by omega), hnw, hpl] at Hif
    wp_apply io.wp_secReader_Read sr r off n W P Hd p vs hsum (by omega) (by omega) hvs'
      $$ [Hsr HP Hp] as %k %err ⟨Hsr, HP, %vs', Hp, %Hk⟩
    · iframe Hsr Hr HP Hp
    try wp_auto
    iapply HΦ
    rw [show n - W - k = n - (W + k) by word]
    iframe Hl Hsr HP
    iexists vs'
    iframe Hp
    ipureintro
    obtain ⟨h1, h2, h3, h4⟩ := Hk
    exact ⟨h1, h2, by omega, h3, h4⟩

/-- `LimitReader(src, n)`: a fresh `*LimitedReader`. -/
theorem io.wp_LimitReader (src : GoInterface) (n : w64) :
    {{ (True : IProp GF) }}
      (App (App (Val (@! _root_.Perennial.io.LimitReader)) (Val #src)) (Val #n))
    {{ (l : Loc), RET #(interface.mkOk (go.GoType.PointerType _root_.Perennial.io.LimitedReader.ty)
        #l); l ↦ ({ R' := src, N' := n } : _root_.Perennial.io.LimitedReader) }} := by
  wp_start
  wp_auto
  wp_alloc l as Hl
  wp_auto
  iapply HΦ
  iexact Hl

/-- The size of `copyBuffer`'s buffer for a limited reader of `n` bytes. -/
def io.copySize (n : w64) : w64 :=
  if sint.Z n < 32768 then (if sint.Z n < 1 then W64 1 else n) else W64 32768

theorem io.copySize_bounds (n : w64) (hn : 0 ≤ sint.Z n) :
    1 ≤ sint.Z (io.copySize n) ∧ sint.Z (io.copySize n) ≤ 32768 ∧
      (sint.Z n < 1 ∨ sint.Z (io.copySize n) ≤ sint.Z n) := by
  unfold io.copySize
  split
  · split
    · exact ⟨by decide, by decide, Or.inl (by omega)⟩
    · refine ⟨by omega, by omega, Or.inr (Int.le_refl _)⟩
  · exact ⟨by decide, by decide, Or.inr (by rw [show sint.Z (W64 32768) = 32768 from rfl]; omega)⟩

/-- `copyBuffer(w, l, nil)` of the limited reader over a fresh section reader, `n` bytes long, and
a writer without `ReadFrom`: it appends at most `n` bytes of the section, in order. -/
theorem io.wp_copyBuffer (w : GoInterfaceOk) (Wr : Bool → List w8 → IProp GF) (c : Bool)
    (bs₀ : List w8) (l sr : Loc) (r : GoInterfaceOk) (off n : w64) (P : IProp GF)
    (Hd : Nat → w8 → Prop) (hplain : io.writerPlain w) (hn : 0 ≤ sint.Z n)
    (hsum : off.toNat + n.toNat < 2 ^ 63) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.io ∗ io.writerOk w Wr ∗ Wr c bs₀ ∗
        l ↦ io.limAt sr n (W64 0) ∗ sr ↦ io.secAt r off n (W64 0) ∗ io.readerAtOk r P Hd ∗ P }}
      (App (App (App (Val (@! _root_.Perennial.io.copyBuffer)) (Val #(GoInterface.ok w)))
        (Val #(interface.mkOk (go.GoType.PointerType _root_.Perennial.io.LimitedReader.ty) #l)))
        (Val #(slice.nil)))
    {{ (written : w64) (err : GoInterface), RET (PairV #written #err);
        ∃ (c' : Bool) (bs : List w8), P ∗ Wr c' (bs₀ ++ bs) ∗
          ⌜sint.Z written = bs.length ∧ bs.length ≤ n.toNat ∧
            (∀ j x, bs[j]? = some x → Hd (off.toNat + j) x) ∧
            (c' = true ∨ (c' = c ∧ bs = []))⌝ }} := by
  wp_start as ⟨#Hw, HWr, Hl, Hsr, #Hr, HP⟩
  have hwt : go.typeSetContains (go.GoType.PointerType _root_.Perennial.io.LimitedReader.ty)
      _root_.Perennial.io.WriterTo.ty = false := by
    rw [go.typeSetContains_underlying, go.typeSetElemsContains_cons,
      go.typeSetElemContains_method_none _ (by
        simp only [go.methodSetLookup_cons, go.methodSetLookup_nil]; decide)]
  have hrf : go.typeSetContains w.ty _root_.Perennial.io.ReaderFrom.ty = false := by
    rw [go.typeSetContains_underlying, go.typeSetElemsContains_cons]
    unfold io.writerPlain at hplain
    simp [go.typeSetElemContains, hplain]
  wp_auto
  simp only [hwt]
  wp_auto
  simp only [hrf]
  wp_auto
  rw [show n - W64 0 = n by word]
  have hsz := io.copySize_bounds n hn
  have h32 : sint.Z (W64 32768) = 32768 := rfl
  have h1 : sint.Z (W64 1) = 1 := rfl
  wp_if_destruct
  · have hc1 := Hif
    rw [h32] at hc1
    wp_if_destruct
    · rw [h1] at Hif
      have h : W64 1 = io.copySize n := by
        unfold io.copySize; simp only [hc1, Hif, ↓reduceIte]
      rw [h]
      done
    · rw [h1] at Hif
      have h : n = io.copySize n := by
        unfold io.copySize; simp only [hc1, Hif, ↓reduceIte]
      wp_auto
      rw [h]
      done
  · rw [h32] at Hif
    have h : W64 32768 = io.copySize n := by
      unfold io.copySize; simp only [Hif, ↓reduceIte]
    rw [h]
    done

theorem io.CopyN.wp_proof : io.CopyN.spec (GF := GF) (hG := hG) := by
  intro w Wr c bs₀ sr r off n P Hd hplain hn
  wp_start as ⟨#Hw, HWr, Hsr, #Hr, HP⟩
  wp_auto
  wp_apply io.wp_LimitReader as %l Hl
  done

end proof

end EtcdGrove
end Perennial
