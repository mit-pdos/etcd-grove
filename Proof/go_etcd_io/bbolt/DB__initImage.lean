/-
The proof of `Spec/go_etcd_io/bbolt/DB__initImage.lean` (split from `DB__init.lean`'s buffer, U11f of
`notes/bbolt-proof-plan.md`): the two meta pages built in the buffer by the loop (`initLoopBuf`),
then the empty freelist and root pages: `Open/InitImage.initImg`.
-/
module

public import Spec.go_etcd_io.bbolt.DB__initImage
public import Spec.go_etcd_io.bbolt.DB__pageInBuffer
public import Proof.go_etcd_io.bbolt.Inv.Locks
public import Proof.go_etcd_io.bbolt.Mmap.Infra
public import Proof.go_etcd_io.bbolt.Commit.MetaPage
public import Spec.go_etcd_io.bbolt.internal.common.Page__SetId
public import Spec.go_etcd_io.bbolt.internal.common.Page__SetFlags
public import Spec.go_etcd_io.bbolt.internal.common.Page__SetCount
public import Spec.go_etcd_io.bbolt.internal.common.Page__Meta
public import Spec.go_etcd_io.bbolt.internal.common.Meta__SetMagic
public import Spec.go_etcd_io.bbolt.internal.common.Meta__SetVersion
public import Spec.go_etcd_io.bbolt.internal.common.Meta__SetPageSize
public import Spec.go_etcd_io.bbolt.internal.common.Meta__SetFreelist
public import Spec.go_etcd_io.bbolt.internal.common.Meta__SetRootBucket
public import Spec.go_etcd_io.bbolt.internal.common.Meta__SetPgid
public import Spec.go_etcd_io.bbolt.internal.common.Meta__SetTxid
public import Spec.go_etcd_io.bbolt.internal.common.Meta__SetChecksum
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Sum64
public import Spec.go_etcd_io.bbolt.internal.common.NewInBucket
public import Proof.go_etcd_io.bbolt.internal.common.Lemmas.Bytes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section lemmas
variable [GooseExts]

/-- `init`'s buffer after `k` iterations of its meta loop. -/
def initLoopBuf : Nat → List w8
  | 0 => List.replicate 16384 (W8 0)
  | 1 => metaBuf (initMv 0) ++ List.replicate 12288 (W8 0)
  | _ => metaBuf (initMv 0) ++ metaBuf (initMv 1) ++ List.replicate 8192 (W8 0)

/-- The buffer's bytes before page `k`. -/
def initPre (k : Nat) : List w8 := if k = 0 then [] else metaBuf (initMv 0)

/-- The buffer's bytes after page `k` (`k < 2`). -/
def initPost (k : Nat) : List w8 := List.replicate (12288 - 4096 * k) (W8 0)

theorem initLoop_step (k : Nat) (hk : k < 2) :
    initLoopBuf k = initPre k ++ (List.replicate 4096 (W8 0) ++ initPost k) ∧
      initLoopBuf (k + 1) = initPre k ++ (metaBuf (initMv k) ++ initPost k) ∧
      (initPre k).length = 4096 * k := by
  rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
  · refine ⟨?_, ?_, rfl⟩
    · show List.replicate 16384 (W8 0) = [] ++ (List.replicate 4096 (W8 0) ++
        List.replicate (12288 - 4096 * 0) (W8 0))
      rw [List.nil_append, List.replicate_append_replicate]
    · show metaBuf (initMv 0) ++ List.replicate 12288 (W8 0) = [] ++ (metaBuf (initMv 0) ++
        List.replicate (12288 - 4096 * 0) (W8 0))
      rw [List.nil_append]
  · refine ⟨?_, ?_, metaBuf_length _⟩
    · show metaBuf (initMv 0) ++ List.replicate 12288 (W8 0) = metaBuf (initMv 0) ++
        (List.replicate 4096 (W8 0) ++ List.replicate (12288 - 4096 * 1) (W8 0))
      rw [List.replicate_append_replicate]
    · show metaBuf (initMv 0) ++ metaBuf (initMv 1) ++ List.replicate 8192 (W8 0) =
        metaBuf (initMv 0) ++ (metaBuf (initMv 1) ++ List.replicate (12288 - 4096 * 1) (W8 0))
      rw [List.append_assoc]

theorem initLoopBuf_two :
    initLoopBuf 2 = (metaBuf (initMv 0) ++ metaBuf (initMv 1)) ++
      (List.replicate 4096 (W8 0) ++ List.replicate 4096 (W8 0)) := by
  show metaBuf (initMv 0) ++ metaBuf (initMv 1) ++ List.replicate 8192 (W8 0) = _
  rw [List.replicate_append_replicate]

theorem metaHdr_initMv (k : Nat) (hk : k < 2) :
    metaHdr (initMv k) = { { zeroHdr with id' := W64 (k : Int) } with flags' := W16 4 } := by
  rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl <;> rfl

end lemmas

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- A zeroed page as a zero header and zeros. -/
theorem zeroPage_hdr (l : Loc) (hl : 0 < l.addr) :
    bytesPointsto (GF := GF) l (DFrac.own 1) (List.replicate 4096 (W8 0)) ⊢
      l ↦ zeroHdr ∗ bytesPointsto (l +ₗ ((16 : Nat) : Int)) (DFrac.own 1)
        (List.replicate 4080 (W8 0)) := by
  have e := bytesPointsto_app (GF := GF) l (DFrac.own 1) (List.replicate 16 (W8 0))
    (List.replicate 4080 (W8 0))
  simp only [List.length_replicate, List.replicate_append_replicate, Nat.reduceAdd] at e
  have t := bytesPointsto_typed (GF := GF) (V := Page) l (DFrac.own 1) (List.replicate 16 (W8 0))
    (by simp) hl
  exact e.1.trans (sep_mono t.1 .rfl)

/-- An empty page's header and zeros: its bytes. -/
theorem emptyPg_join (l : Loc) (id : Nat) (fl : w16) (hl : 0 < l.addr) :
    l ↦ emptyHdr id fl ∗ bytesPointsto (l +ₗ ((16 : Nat) : Int)) (DFrac.own 1)
        (List.replicate 4080 (W8 0)) ⊢
      bytesPointsto (GF := GF) l (DFrac.own 1) (emptyPg id fl) := by
  have e := bytesPointsto_app (GF := GF) l (DFrac.own 1) (encode (emptyHdr id fl))
    (List.replicate 4080 (W8 0))
  rw [ByteEncoding.encode_length] at e
  have t := typedPointsto_bytes (GF := GF) l (emptyHdr id fl) (DFrac.own 1) hl
  exact (sep_mono t.1 .rfl).trans e.2

end heap

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem DB.initImage.wp_proof (hPIB : DB.pageInBuffer.spec_own (GF := GF) (hG := hG))
    (hSetId : internal.common.Page.SetId.spec (GF := GF) (hG := hG))
    (hSetFlags : internal.common.Page.SetFlags.spec (GF := GF) (hG := hG))
    (hSetCount : internal.common.Page.SetCount.spec (GF := GF) (hG := hG))
    (hMeta : internal.common.Page.Meta.spec (GF := GF) (hG := hG))
    (hSetMagic : internal.common.Meta.SetMagic.spec (GF := GF) (hG := hG))
    (hSetVersion : internal.common.Meta.SetVersion.spec (GF := GF) (hG := hG))
    (hSetPageSize : internal.common.Meta.SetPageSize.spec (GF := GF) (hG := hG))
    (hSetFreelist : internal.common.Meta.SetFreelist.spec (GF := GF) (hG := hG))
    (hSetRoot : internal.common.Meta.SetRootBucket.spec (GF := GF) (hG := hG))
    (hSetPgid : internal.common.Meta.SetPgid.spec (GF := GF) (hG := hG))
    (hSetTxid : internal.common.Meta.SetTxid.spec (GF := GF) (hG := hG))
    (hSetChecksum : internal.common.Meta.SetChecksum.spec (GF := GF) (hG := hG))
    (hSum64 : internal.common.Meta.Sum64.spec (GF := GF) (hG := hG))
    (hNewIB : internal.common.NewInBucket.spec (GF := GF) (hG := hG)) :
    DB.initImage.spec (GF := GF) (hG := hG) := by
  intro db dq
  wp_start as Hps
  ihave #Hpkc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_slice_make2 (V := w8) $$ [] as %sl ⟨Hbuf, Hbcap⟩
  · ipureintro; decide
  rw [show (zero_val w8 : w8) = W8 0 from rfl, show sint.nat (W64 4096 * W64 4) = 16384 from rfl]
  ihave %Hlen := ownSlice_len _ _ _ $$ Hbuf
  ihave %Hbcw := ownSliceCap_wf _ _ $$ Hbcap
  ihave %Hpos := ownSlice_ptr_pos _ _ _
    (List.ne_nil_of_length_pos (by rw [List.length_replicate]; decide)) $$ Hbuf
  icases ownSlice_bytes_acc go.uint8 (.scalar _ _ .isPlainScalar_uint8) _ _ _ Hpos $$ Hbuf
    with ⟨Hb, Hback⟩
  rw [flatMap_encode_w8]
  have hslen : sl.len.toNat = 16384 := by
    have h1 := Hlen.1; have h2 := Hlen.2
    rw [List.length_replicate] at h1; simp only [sint.nat] at h1
    word
  ihave IH : (∃ (k : Nat), "i" ∷ i_ptr ↦ W64 (k : Int) ∗ "%Hk" ∷ ⌜k ≤ 2⌝ ∗
      "Hb" ∷ bytesPointsto sl.ptr (DFrac.own 1) (initLoopBuf k) ∗
      "db" ∷ db_ptr ↦ db ∗ "buf" ∷ buf_ptr ↦ sl ∗
      "Hps" ∷ db.[DB, go!"pageSize"] ↦{dq} W64 4096 : IProp GF) $$ [i Hb db buf Hps]
  · iexists 0; simp only [named]; iframe; ipureintro; omega
  wp_for IH
  have hk2 : sint.Z (W64 (k : Int)) = (k : Int) := by word
  rw [hk2, show sint.Z (W64 2) = 2 from rfl]
  by_cases hkl : (k : Int) < 2
  · rw [decide_eq_true hkl]
    simp only [↓reduceIte]
    have hk : k < 2 := by omega
    obtain ⟨hpre, hpost, hprel⟩ := initLoop_step k hk
    try wp_auto
    wp_apply hPIB db sl (W64 (k : Int)) dq (by rw [hslen]; simp; omega) (by rw [hslen]; decide) Hpos
      $$ [Hps] as Hps
    · iframe Hps; try iframe #
    have hoff : (((W64 (k : Int)).toNat * 4096 : Nat) : Int) = ((initPre k).length : Int) := by
      rw [hprel]; simp; omega
    rw [hoff, hpre]
    icases (bytesPointsto_app _ _ _ _).1 $$ Hb with ⟨Hpre, Hb⟩
    icases (bytesPointsto_app _ _ _ _).1 $$ Hb with ⟨Hz, Hpost⟩
    obtain ⟨l, hl⟩ : ∃ l, l = sl.ptr +ₗ ((initPre k).length : Int) := ⟨_, rfl⟩
    rw [← hl]
    have hlp : 0 < l.addr := by rw [hl]; simp only [Loc.add]; omega
    icases zeroPage_meta l hlp $$ Hz with ⟨%Hmax, Hh, Hm0, Hz⟩
    rw [show (decode (List.replicate 64 (W8 0)) : Meta) =
      ⟨W32 0, W32 0, W32 0, W32 0, ⟨W64 0, W64 0⟩, W64 0, W64 0, W64 0, W64 0⟩ from rfl]
    try wp_auto
    wp_apply hSetId $$ [Hh] as Hh
    · iframe #; iframe
    try wp_auto
    wp_apply hSetFlags $$ [Hh] as Hh
    · iframe #; iframe
    try wp_auto
    wp_apply hMeta l hlp (by omega)
    try wp_auto
    try rw [show Magic = #(W32 3977042669) from rfl]
    wp_apply hSetMagic $$ [Hm0] as Hm0
    · iframe #; iframe
    try wp_auto
    try rw [show Version = #(W32 2) from rfl]
    wp_apply hSetVersion $$ [Hm0] as Hm0
    · iframe #; iframe
    try wp_auto
    wp_apply hSetPageSize $$ [Hm0] as Hm0
    · iframe #; iframe
    try wp_auto
    wp_apply hSetFreelist $$ [Hm0] as Hm0
    · iframe #; iframe
    try wp_auto
    wp_apply hNewIB
    try wp_auto
    wp_apply hSetRoot $$ [Hm0] as Hm0
    · iframe #; iframe
    try wp_auto
    wp_apply hSetPgid $$ [Hm0] as Hm0
    · iframe #; iframe
    try wp_auto
    wp_apply hSetTxid $$ [Hm0] as Hm0
    · iframe #; iframe
    try wp_auto
    icases internal.common.typedPointsto_of_eq _ _ (initMv k) _ $$ [Hm0] with Hm0
    · iframe
      ipureintro
      simp only [initMv]
      rfl
    have hl16 : 0 < (l +ₗ (16 : Int)).addr := by simp only [Loc.add]; omega
    wp_apply hSum64 (l +ₗ 16) (initMv k) (DFrac.own 1) hl16 $$ [Hm0] as Hm0
    · iframe #; iframe
    try wp_auto
    wp_apply hSetChecksum $$ [Hm0] as Hm0
    · iframe #; iframe
    try wp_auto
    ihave Hm0 : (l +ₗ 16) ↦ metaSummed (initMv k) $$ [Hm0]
    · unfold metaSummed; iexact Hm0
    ihave Hh : l ↦ metaHdr (initMv k) $$ [Hh]
    · rw [metaHdr_initMv k hk]; iexact Hh
    ihave Hz := metaPage_bytes l (initMv k) hlp $$ [Hh Hm0 Hz]
    · iframe
    ihave Hpost : bytesPointsto (l +ₗ ((metaBuf (initMv k)).length : Int)) (DFrac.own 1)
        (initPost k) $$ [Hpost]
    · rw [metaBuf_length]; rw [List.length_replicate]; iexact Hpost
    ihave Hb := (bytesPointsto_app l (DFrac.own 1) (metaBuf (initMv k)) (initPost k)).2 $$ [Hz Hpost]
    · iframe
    rw [hl]
    ihave Hb := (bytesPointsto_app sl.ptr (DFrac.own 1) (initPre k)
      (metaBuf (initMv k) ++ initPost k)).2 $$ [Hpre Hb]
    · iframe
    rw [← hpost]
    wp_for_post
    iframe
    iexists (k + 1)
    rw [show W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) by push_cast; word]
    simp only [named]
    iframe
    ipureintro; omega
  · rw [decide_eq_false hkl]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hk : k = 2 := by omega
    subst hk
    try wp_auto
    rw [initLoopBuf_two]
    icases (bytesPointsto_app _ _ _ _).1 $$ Hb with ⟨Hm01, Hb⟩
    icases (bytesPointsto_app _ _ _ _).1 $$ Hb with ⟨Hz2, Hz3⟩
    have hl01 : (metaBuf (initMv 0) ++ metaBuf (initMv 1)).length = 8192 := by
      simp only [List.length_append, metaBuf_length]
    rw [hl01, List.length_replicate]
    try wp_auto
    -- page 2: the freelist's, empty
    wp_apply hPIB db sl (W64 2) dq (by rw [hslen]; decide) (by rw [hslen]; decide) Hpos
      $$ [Hps] as Hps
    · iframe Hps; try iframe #
    rw [show (((2 * 4096 : Nat)) : Int) = ((8192 : Nat) : Int) from rfl]
    have hl2 : 0 < (sl.ptr +ₗ ((8192 : Nat) : Int)).addr := by simp only [Loc.add]; omega
    icases zeroPage_hdr _ hl2 $$ Hz2 with ⟨Hh, Hz⟩
    try wp_auto
    wp_apply hSetId $$ [Hh] as Hh
    · iframe #; iframe
    try wp_auto
    wp_apply hSetFlags $$ [Hh] as Hh
    · iframe #; iframe
    try wp_auto
    wp_apply hSetCount $$ [Hh] as Hh
    · iframe #; iframe
    try wp_auto
    icases internal.common.typedPointsto_of_eq _ _ (emptyHdr 2 (W16 16)) _ $$ [Hh] with Hh
    · iframe; ipureintro; rfl
    ihave Hz2 := emptyPg_join _ 2 (W16 16) hl2 $$ [Hh Hz]
    · iframe
    -- page 3: the root, an empty leaf
    wp_apply hPIB db sl (W64 3) dq (by rw [hslen]; decide) (by rw [hslen]; decide) Hpos
      $$ [Hps] as Hps
    · iframe Hps; try iframe #
    rw [List.length_replicate, show (((3 * 4096 : Nat)) : Int) = ((12288 : Nat) : Int) from rfl,
      show sl.ptr +ₗ ((8192 : Nat) : Int) +ₗ ((4096 : Nat) : Int) = sl.ptr +ₗ ((12288 : Nat) : Int)
        by rw [loc_add_assoc]; rfl]
    have hl3 : 0 < (sl.ptr +ₗ ((12288 : Nat) : Int)).addr := by simp only [Loc.add]; omega
    icases zeroPage_hdr _ hl3 $$ Hz3 with ⟨Hh, Hz⟩
    try wp_auto
    wp_apply hSetId $$ [Hh] as Hh
    · iframe #; iframe
    try wp_auto
    wp_apply hSetFlags $$ [Hh] as Hh
    · iframe #; iframe
    try wp_auto
    wp_apply hSetCount $$ [Hh] as Hh
    · iframe #; iframe
    try wp_auto
    icases internal.common.typedPointsto_of_eq _ _ (emptyHdr 3 (W16 2)) _ $$ [Hh] with Hh
    · iframe; ipureintro; rfl
    ihave Hz3 := emptyPg_join _ 3 (W16 2) hl3 $$ [Hh Hz]
    · iframe
    -- the buffer: the image
    ihave Hz3 : bytesPointsto (sl.ptr +ₗ ((8192 : Nat) : Int) +ₗ
        (((emptyPg 2 (W16 16)).length : Nat) : Int)) (DFrac.own 1) (emptyPg 3 (W16 2)) $$ [Hz3]
    · rw [emptyPg_length, loc_add_assoc,
        show ((8192 : Nat) : Int) + ((4096 : Nat) : Int) = ((12288 : Nat) : Int) from rfl]
      iexact Hz3
    ihave Hb := (bytesPointsto_app _ (DFrac.own 1) (emptyPg 2 (W16 16)) (emptyPg 3 (W16 2))).2
      $$ [Hz2 Hz3]
    · iframe
    rw [← hl01]
    ihave Hb := (bytesPointsto_app sl.ptr (DFrac.own 1) (metaBuf (initMv 0) ++ metaBuf (initMv 1))
      (emptyPg 2 (W16 16) ++ emptyPg 3 (W16 2))).2 $$ [Hm01 Hb]
    · iframe
    rw [← initImg_split]
    ihave Hsl := Hback $$ %initImg %initImg_length [Hb]
    · rw [flatMap_encode_w8]; iexact Hb
    try wp_auto
    iapply HΦ
    iframe Hps Hbcap
    iexact Hsl

end proof

end bbolt
end EtcdGrove
end Perennial
