/-
`shared.Write(p)` (U2 internal): the freelist page at `p`, its ids written through
`unsafe.Slice((*Pgid)(UnsafeAdd(p, 16)), l)` by `Copyall`. The byte-view lemmas are those of
Perennial's `unsafememory/Freelist.lean` (`decodeChunks`, `ownSlice_of_bytes`, ...), restated here.
-/
module

public import Proof.go_etcd_io.bbolt.internal.freelist.Impl.shared__Copyall
public import Proof.go_etcd_io.bbolt.internal.freelist.Impl.shared__Count
public import Proof.go_etcd_io.bbolt.internal.common.Lemmas.Layout
public import Spec.go_etcd_io.bbolt.internal.common.Page__SetFlags
public import Spec.go_etcd_io.bbolt.internal.common.Page__SetCount
public import Spec.go_etcd_io.bbolt.internal.common.UnsafeAdd

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt
namespace internal
namespace freelist

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.freelist

/-- `k` values of `n` bytes each, decoded from the bytes `bs`. -/
def decodeChunks {V : Type} {n : Nat} [ByteEncoding V n] : Nat → List w8 → List V
  | 0, _ => []
  | k + 1, bs => decode (bs.take n) :: decodeChunks k (bs.drop n)

theorem decodeChunks_length {V : Type} {n : Nat} [ByteEncoding V n] (k : Nat) (bs : List w8) :
    (decodeChunks (V := V) k bs).length = k := by
  induction k generalizing bs with
  | zero => rfl
  | succ k ih => simp [decodeChunks, ih]

theorem decodeChunks_flatMap {V : Type} {n : Nat} [ByteEncoding V n] (k : Nat) (bs : List w8)
    (h : bs.length = k * n) : (decodeChunks (V := V) k bs).flatMap encode = bs := by
  induction k generalizing bs with
  | zero => simp [decodeChunks] at h ⊢; simp [h]
  | succ k ih =>
    simp only [decodeChunks, List.flatMap_cons]
    rw [ByteEncoding.encode_decode _ (by simp; rw [Nat.succ_mul] at h; omega),
      ih _ (by simp; rw [Nat.succ_mul] at h; omega), List.take_append_drop]

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

/-- The bytes a freelist page of the free and pending ids holds after its header. -/
def flBody (fl : FLPg) : List w8 :=
  (if fl.allIds.length < 0xFFFF then [] else encode (W64 (fl.allIds.length : Int))) ++
    (sortPgids fl.allIds).flatMap encode


theorem ownSlice_of_bytes' {V : Type} {n : Nat} [ZeroVal V] [ByteEncoding V n]
    [TypedPointsto (GF := GF) V] [BytesView (GF := GF) V] (e : go.GoType) [TypeRepr e V] {a : Nat}
    (hlay : go.PlainLayout e n a) (s : GoSlice) (vs : List V) (dq : DFrac) (hl : 0 < s.ptr.addr)
    (hlen : sint.Z s.len = vs.length) (hcap : sint.Z s.len ≤ sint.Z s.cap) :
    bytesPointsto (GF := GF) s.ptr dq (vs.flatMap encode) ⊢ s ↦*{dq} vs := by
  rw [ownSlice_unseal]; unfold ownSliceDef
  iintro Hb
  iright
  isplitl [Hb]
  · iapply (typedPointsto_array_bytes e hlay s.ptr (sint.Z s.len) (array.mk _ vs) dq hl).2
    iframe Hb
    ipureintro; exact hlen.symm
  · ipureintro; exact hcap

theorem ownSlice_to_bytes' {V : Type} {n : Nat} [ZeroVal V] [ByteEncoding V n]
    [TypedPointsto (GF := GF) V] [BytesView (GF := GF) V] (e : go.GoType) [TypeRepr e V] {a : Nat}
    (hlay : go.PlainLayout e n a) (s : GoSlice) (vs : List V) (dq : DFrac) (hl : 0 < s.ptr.addr) :
    (s ↦*{dq} vs : IProp GF) ⊢ bytesPointsto s.ptr dq (vs.flatMap encode) := by
  iintro Hs
  icases ownSlice_bytes_acc e hlay s vs dq hl $$ Hs with ⟨Hb, _⟩
  iexact Hb

/-- `unsafe.Slice((*Pgid)(l), n)` for a non-null `l` and a slice that ends in the address space. -/
theorem wp_unsafe_slice_Pgid (l : Loc) (n : w64) (hn : 0 ≤ sint.Z n) (hl : 0 < l.addr)
    (hb : l.addr + sint.Z n * 8 ≤ 2 ^ 64) :
    {{ (True : IProp GF) }}
      (App (App (Val #(functions «unsafe».Slice [go_etcd_io.bbolt.internal.common.Pgid.ty, go.int]))
        (Val #l)) (Val #n))
    {{ RET #(slice.mk l n n); True }} := by
  iintro %Φ _ HΦ
  wp_func_call
  wp_call
  have hnn : l ≠ null := by intro h; subst h; simp [null] at hl
  rw [ite_eq_right (by omega), ite_eq_right hnn, ite_eq_right (by push_cast; omega)]
  wp_auto
  iapply HΦ; itrivial

/-- `t.Write(p)`: the freelist page at `p` (its header, and `R` zeroed bytes after it, room for
the ids and a count). -/
abbrev shared.Write.spec (I : FLImpl (GF := GF)) : Prop :=
  ∀ (s : Loc) (fl : FLPg) (p : Loc) (hdr : go_etcd_io.bbolt.internal.common.Page) (R : Nat),
  8 * (fl.allIds.length + 1) ≤ R → 0 < p.addr → p.addr + 16 + R ≤ maxAddr →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗
      ownSh s I.iface fl ∗ I.own fl.free ∗
      p ↦ hdr ∗ bytesPointsto (p +ₗ 16) (DFrac.own 1) (List.replicate R (W8 0)) }}
    (App (Val #(methods (go.GoType.PointerType shared.ty) go!"Write" #s)) (Val #p))
  {{ RET #(); ownSh s I.iface fl ∗ I.own fl.free ∗
      p ↦ (⟨hdr.id', W16 16,
        W16 ((if fl.allIds.length < 0xFFFF then fl.allIds.length else 0xFFFF : Nat) : Int),
        hdr.overflow'⟩ : go_etcd_io.bbolt.internal.common.Page) ∗
      bytesPointsto (p +ₗ 16) (DFrac.own 1)
        (flBody fl ++ List.replicate (R - (flBody fl).length) (W8 0)) }}

theorem shared.Write.wp_proof (I : FLImpl (GF := GF)) (hFC : I.FreeCountSpec)
    (hF : I.FreePageIdsSpec)
    (hMerge : _root_.Perennial.EtcdGrove.bbolt.Mergepgids.spec (GF := GF) (hG := hG))
    (hSF : _root_.Perennial.EtcdGrove.bbolt.internal.common.Page.SetFlags.spec (GF := GF) (hG := hG))
    (hSC : _root_.Perennial.EtcdGrove.bbolt.internal.common.Page.SetCount.spec (GF := GF) (hG := hG))
    (hUA : _root_.Perennial.EtcdGrove.bbolt.internal.common.UnsafeAdd.spec (GF := GF) (hG := hG)) :
    shared.Write.spec I := by
  intro s fl p hdr R HR Hp Hpb
  wp_start as ⟨Hsh, Hown, Hh, Hb⟩
  ihave #Hc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  wp_auto
  wp_apply (hSF p hdr) $$ [Hh] as Hh
  · iframe
  iunfold ownSh at Hsh
  icases Hsh with ⟨%c, Hsh, %Hok⟩
  have Hlen : fl.allIds.length < 2 ^ 63 := Hok.2.2.2.2.1
  wp_apply (shared.Count.wp_proof I hFC s fl c) $$ [Hsh Hown] as ⟨Hsh, Hown⟩
  · iframe
  ihave Hsh : ownSh s I.iface fl $$ [Hsh]
  · iunfold ownSh; iexists c; iframe; ipureintro; exact Hok
  wp_if_destruct
  · have hn0 : fl.allIds.length = 0 := by
      have := congrArg (fun w : w64 => w.toNat) Hif
      word
    wp_apply (hSC p _ _) $$ [Hh] as Hh
    · iframe
    iapply HΦ
    iframe
    have hb : flBody fl = [] := by
      simp [flBody, List.eq_nil_of_length_eq_zero hn0, sortPgids]
    rw [hb, hn0]
    try simp only [List.nil_append, List.length_nil, Nat.sub_zero]
    iframe
  · have hn0 : fl.allIds.length ≠ 0 := fun h => Hif (by rw [h]; rfl)
    have hsn : sint.Z (W64 (fl.allIds.length : Int)) = fl.allIds.length := by word
    have hsl : (sortPgids fl.allIds).length = fl.allIds.length := (sortPgids_perm _).length_eq
    have hadd : 0 ≤ (p +ₗ sint.Z (W64 16)).addr ∧ (p +ₗ sint.Z (W64 16)).addr ≤ maxAddr := by
      rw [show sint.Z (W64 16) = 16 from rfl]; simp only [Loc.add]; omega
    wp_if_destruct
    · have hsmall : fl.allIds.length < 65535 := by rw [hsn] at Hif; word
      wp_apply (hSC p _ _) $$ [Hh] as Hh
      · iframe
      try wp_auto
      wp_apply (hUA p (W64 16) hadd.1 hadd.2)
      rw [show sint.Z (W64 16) = 16 from rfl]
      wp_apply (wp_unsafe_slice_Pgid (p +ₗ 16) (W64 (fl.allIds.length : Int)) (by omega)
        (by simp only [Loc.add]; omega) (by simp only [Loc.add]; simp [maxAddr] at Hpb; omega))
      ihave Hb := bytesPointsto_congr _ _ _ _
        (List.take_append_drop (fl.allIds.length * 8) (List.replicate R (W8 0))).symm $$ Hb
      icases (bytesPointsto_app _ _ _ _).1 $$ Hb with ⟨Hb1, Hb2⟩
      have hb1l : (List.take (fl.allIds.length * 8) (List.replicate R (W8 0))).length =
          fl.allIds.length * 8 := by simp; omega
      ihave Hb1 := bytesPointsto_congr _ _ _ _
        (decodeChunks_flatMap (V := w64) fl.allIds.length _ hb1l).symm $$ Hb1
      ihave Hd := ownSlice_of_bytes' go_etcd_io.bbolt.internal.common.Pgid.ty
        go_etcd_io.bbolt.internal.common.Pgid.layout
        (slice.mk (p +ₗ 16) (W64 (fl.allIds.length : Int)) (W64 (fl.allIds.length : Int))) _ _
        (by simp [Loc.add]; omega) (by rw [decodeChunks_length]; exact hsn) (Int.le_refl _) $$ Hb1
      have HC := shared.Copyall.wp_proof I hF hMerge s fl
        (slice.mk (p +ₗ 16) (W64 (fl.allIds.length : Int)) (W64 (fl.allIds.length : Int)))
        (decodeChunks (V := w64) fl.allIds.length
          (List.take (fl.allIds.length * 8) (List.replicate R (W8 0))))
        (Nat.le_of_eq (decodeChunks_length _ _).symm)
      wp_apply HC $$ [Hsh Hown Hd] as ⟨Hsh, Hown, Hd⟩
      · iframe
      rw [List.drop_of_length_le (l := decodeChunks (V := w64) fl.allIds.length
        (List.take (fl.allIds.length * 8) (List.replicate R (W8 0))))
        (Nat.le_of_eq (decodeChunks_length _ _)), List.append_nil]
      ihave Hd := ownSlice_to_bytes' go_etcd_io.bbolt.internal.common.Pgid.ty
        go_etcd_io.bbolt.internal.common.Pgid.layout _ _ _ (by simp [Loc.add]; omega) $$ Hd
      iapply HΦ
      iframe
      have hfb : flBody fl = (sortPgids fl.allIds).flatMap encode := by
        simp [flBody, hsmall]
      have hfbl : (flBody fl).length = fl.allIds.length * 8 := by
        rw [hfb, flatMap_encode_length, hsl]
      isplitl [Hh]
      · iExactEq Hh
        simp only [hsmall, ↓reduceIte]
        congr 2
        word
      rw [hfbl, hfb]
      iapply (bytesPointsto_app _ _ _ _).2
      rw [flatMap_encode_length, hsl, hb1l]
      iframe
      iExactEq Hb2
      congr 1
      rw [List.drop_replicate]
    · have hbig : 65535 ≤ fl.allIds.length := by rw [hsn] at Hif; word
      wp_apply (hSC p _ _) $$ [Hh] as Hh
      · iframe
      try wp_auto
      wp_apply (hUA p (W64 16) hadd.1 hadd.2)
      rw [show sint.Z (W64 16) = 16 from rfl]
      have hn44 : fl.allIds.length < 2 ^ 44 := by simp [maxAddr] at Hpb; omega
      have hl1 : sint.Z (W64 (fl.allIds.length : Int) + W64 1) = fl.allIds.length + 1 := by word
      wp_apply (wp_unsafe_slice_Pgid (p +ₗ 16) (W64 (fl.allIds.length : Int) + W64 1)
        (by rw [hl1]; omega) (by simp only [Loc.add]; omega)
        (by rw [hl1]; simp only [Loc.add]; simp [maxAddr] at Hpb; omega))
      rw [ite_eq_left (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) <
          sint.Z (W64 (fl.allIds.length : Int) + W64 1) from
        ⟨by decide, by rw [hl1]; show (0 : Int) < _; omega⟩),
        show sliceIndexRef w64 (sint.Z (W64 0)) (slice.mk (p +ₗ 16) (W64 (fl.allIds.length : Int) + W64 1)
          (W64 (fl.allIds.length : Int) + W64 1)) = p +ₗ 16 from go.arrayIndexRef_0 _ _]
      ihave Hb := bytesPointsto_congr _ _ _ _
        (List.take_append_drop 8 (List.replicate R (W8 0))).symm $$ Hb
      icases (bytesPointsto_app _ _ _ _).1 $$ Hb with ⟨Hcb, Hb⟩
      icases (bytesPointsto_typed (V := w64) (p +ₗ 16) _ _ (by simp; omega)
        (by simp [Loc.add]; omega)).1 $$ Hcb with Hcb
      wp_auto
      rw [ite_eq_left (show 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) ≤
          sint.Z (W64 (fl.allIds.length : Int) + W64 1) ∧
          sint.Z (W64 (fl.allIds.length : Int) + W64 1) ≤ sint.Z (W64 (fl.allIds.length : Int) + W64 1) from
        ⟨by decide, by rw [hl1]; show (1 : Int) ≤ _; omega, Int.le_refl _⟩)]
      have hslc : slice.slice (slice.mk (p +ₗ 16) (W64 (fl.allIds.length : Int) + W64 1)
          (W64 (fl.allIds.length : Int) + W64 1)) w64 (W64 1) (W64 (fl.allIds.length : Int) + W64 1) =
          slice.mk (p +ₗ 16 +ₗ 8) (W64 (fl.allIds.length : Int)) (W64 (fl.allIds.length : Int)) := by
        have := sliceIndexRef_plain_W64 (V := w64) go_etcd_io.bbolt.internal.common.Pgid.ty
          go_etcd_io.bbolt.internal.common.Pgid.layout
          (slice.mk (p +ₗ 16) (W64 (fl.allIds.length : Int) + W64 1)
            (W64 (fl.allIds.length : Int) + W64 1)) 1 (by simp [Loc.add]; omega) (by decide)
        simp only [slice.slice]
        rw [show sint.Z (W64 1) = sint.Z (W64 ((1 : Nat) : Int)) from rfl, this]
        have e : W64 (fl.allIds.length : Int) + W64 1 - W64 1 = W64 (fl.allIds.length : Int) := by word
        rw [e]; rfl
      rw [hslc]
      rw [show (List.take 8 (List.replicate R (W8 0))).length = 8 by simp; omega]
      ihave Hb := bytesPointsto_congr _ _ _ _
        (List.take_append_drop (fl.allIds.length * 8) (List.drop 8 (List.replicate R (W8 0)))).symm $$ Hb
      icases (bytesPointsto_app _ _ _ _).1 $$ Hb with ⟨Hb1, Hb2⟩
      have hb1l : (List.take (fl.allIds.length * 8) (List.drop 8 (List.replicate R (W8 0)))).length =
          fl.allIds.length * 8 := by simp; omega
      ihave Hb1 := bytesPointsto_congr _ _ _ _
        (decodeChunks_flatMap (V := w64) fl.allIds.length _ hb1l).symm $$ Hb1
      ihave Hd := ownSlice_of_bytes' go_etcd_io.bbolt.internal.common.Pgid.ty
        go_etcd_io.bbolt.internal.common.Pgid.layout
        (slice.mk (p +ₗ 16 +ₗ 8) (W64 (fl.allIds.length : Int)) (W64 (fl.allIds.length : Int))) _ _
        (by simp [Loc.add]; omega) (by rw [decodeChunks_length]; exact hsn) (Int.le_refl _) $$ Hb1
      wp_auto
      have HC := shared.Copyall.wp_proof I hF hMerge s fl
        (slice.mk (p +ₗ 16 +ₗ 8) (W64 (fl.allIds.length : Int)) (W64 (fl.allIds.length : Int)))
        (decodeChunks (V := w64) fl.allIds.length
          (List.take (fl.allIds.length * 8) (List.drop 8 (List.replicate R (W8 0)))))
        (Nat.le_of_eq (decodeChunks_length _ _).symm)
      wp_apply HC $$ [Hsh Hown Hd] as ⟨Hsh, Hown, Hd⟩
      · iframe
      rw [List.drop_of_length_le (l := decodeChunks (V := w64) fl.allIds.length
        (List.take (fl.allIds.length * 8) (List.drop 8 (List.replicate R (W8 0)))))
        (Nat.le_of_eq (decodeChunks_length _ _)), List.append_nil]
      ihave Hd := ownSlice_to_bytes' go_etcd_io.bbolt.internal.common.Pgid.ty
        go_etcd_io.bbolt.internal.common.Pgid.layout _ _ _ (by simp [Loc.add]; omega) $$ Hd
      iapply HΦ
      iframe
      have hnsmall : ¬ fl.allIds.length < 65535 := by omega
      have hfb : flBody fl = encode (W64 (fl.allIds.length : Int)) ++
          (sortPgids fl.allIds).flatMap encode := by
        simp [flBody, hnsmall]
      have hfbl : (flBody fl).length = 8 + fl.allIds.length * 8 := by
        rw [hfb, List.length_append, ByteEncoding.encode_length, flatMap_encode_length, hsl]
      isplitl [Hh]
      · iExactEq Hh
        simp only [hnsmall, ↓reduceIte]
        rfl
      rw [hfbl, hfb, List.append_assoc]
      iapply (bytesPointsto_app _ _ _ _).2
      rw [ByteEncoding.encode_length]
      isplitl [Hcb]
      · iapply (typedPointsto_bytes _ _ _ (by simp [Loc.add]; omega)).1 $$ Hcb
      iapply (bytesPointsto_app _ _ _ _).2
      rw [flatMap_encode_length, hsl, show ((8 : Nat) : Int) = 8 from rfl]
      rw [hb1l]
      iframe
      iExactEq Hb2
      congr 1
      simp only [List.drop_replicate]
      congr 1
      omega

end proof

end freelist
end internal
end bbolt
end EtcdGrove
end Perennial
