module
public import Spec.go_etcd_io.bbolt.DB__init
public import Spec.go_etcd_io.bbolt.DB__pageInBuffer
public import Spec.go_etcd_io.bbolt.DB__Logger
public import Spec.go_etcd_io.bbolt.fdatasync
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
public import Spec.os.File__WriteAt
public import Proof.go_etcd_io.bbolt.AllocPage

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- The zero meta. -/
abbrev zeroMeta : Meta :=
  Meta.mk (W32 0) (W32 0) (W32 0) (W32 0) (InBucket.mk (W64 0) (W64 0)) (W64 0) (W64 0) (W64 0)
    (W64 0)

theorem leBytes_zero (n : Nat) : leBytes n 0 = List.replicate n (W8 0) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [leBytes, Int.zero_ediv, ih, List.replicate_succ]; try rfl

theorem metaBytes_zero : metaBytes zeroMeta = List.replicate 64 (W8 0) := by
  unfold metaBytes inBucketBytes zeroMeta
  simp only [BitVec.toNat_ofInt]
  simp [leBytes_zero, List.replicate_append_replicate]

theorem loc_add_nat (l : Loc) (a b : Nat) :
    l +ₗ (a : Int) +ₗ (b : Int) = l +ₗ ((a + b : Nat) : Int) := by
  rw [loc_add_assoc]; push_cast; rfl

/-- A zeroed page region is a zero header, a zero meta and zeros. -/
theorem zero_region (l : Loc) (ps : Nat) (hl : l.locCar ≠ 0) (hps : 80 ≤ ps) :
    bytesPointsto (GF := GF) l (DFrac.own 1) (List.replicate ps (W8 0)) ⊢
      l ↦ Page.mk (W64 0) (W16 0) (W16 0) (W32 0) ∗ (l +ₗ (16 : Nat)) ↦ zeroMeta ∗
        bytesPointsto (l +ₗ (80 : Nat)) (DFrac.own 1) (List.replicate (ps - 80) (W8 0)) := by
  have hl16 : (l +ₗ ((16 : Nat) : Int)).locCar ≠ 0 := by simpa [Loc.add] using hl
  iintro H
  icases (zero_page (hG := hG) l ps hl (by omega)).1 $$ H with ⟨Hp, Hz⟩
  rw [show ps - 16 = 64 + (ps - 80) by omega, ← List.replicate_append_replicate]
  icases (bytesPointsto_app _ _ _ _).1 $$ Hz with ⟨Hm, Hz⟩
  rw [List.length_replicate, show l +ₗ (16 : Int) +ₗ ((64 : Nat) : Int) = l +ₗ ((80 : Nat) : Int) by
    rw [loc_add_assoc]; rfl]
  rw [← metaBytes_zero]
  ihave Hm := (Meta_bytes (hG := hG) (l +ₗ ((16 : Nat) : Int)) zeroMeta _ hl16).2 $$ Hm
  iframe

/-- A meta page's header, meta and zeros: its bytes. -/
theorem meta_page_join (l : Loc) (ps k : Nat) (hl : l.locCar ≠ 0) :
    l ↦ Page.mk (W64 (k : Int)) (W16 4) (W16 0) (W32 0) ∗ (l +ₗ (16 : Nat)) ↦ initMeta ps k ∗
      bytesPointsto (l +ₗ (80 : Nat)) (DFrac.own 1) (List.replicate (ps - 80) (W8 0)) ⊢
    bytesPointsto (GF := GF) l (DFrac.own 1) (initMetaPage ps k) := by
  have hl16 : (l +ₗ ((16 : Nat) : Int)).locCar ≠ 0 := by simpa [Loc.add] using hl
  iintro ⟨Hp, Hm, Hz⟩
  ihave Hp := (Page_bytes (hG := hG) l _ _ hl).1 $$ Hp
  ihave Hm := (Meta_bytes (hG := hG) _ _ _ hl16).1 $$ Hm
  unfold initMetaPage
  iapply (bytesPointsto_app _ _ _ _).2
  rw [List.length_append, show (pageBytes (Page.mk (W64 (k : Int)) (W16 4) (W16 0) (W32 0))).length +
      (metaBytes (initMeta ps k)).length = 80 by simp [pageBytes, metaBytes_length, leBytes_length]]
  iframe
  iapply (bytesPointsto_app _ _ _ _).2
  rw [show (pageBytes (Page.mk (W64 (k : Int)) (W16 4) (W16 0) (W32 0))).length = 16 by
    simp [pageBytes, leBytes_length]]
  iframe

/-- An empty page's header and zeros: its bytes. -/
theorem empty_page_join (l : Loc) (ps id : Nat) (fl : w16) (hl : l.locCar ≠ 0) :
    l ↦ Page.mk (W64 (id : Int)) fl (W16 0) (W32 0) ∗
      bytesPointsto (l +ₗ (16 : Nat)) (DFrac.own 1) (List.replicate (ps - 16) (W8 0)) ⊢
    bytesPointsto (GF := GF) l (DFrac.own 1) (initEmptyPage ps id fl) := by
  iintro ⟨Hp, Hz⟩
  ihave Hp := (Page_bytes (hG := hG) l _ _ hl).1 $$ Hp
  unfold initEmptyPage
  iapply (bytesPointsto_app _ _ _ _).2
  rw [show (pageBytes (Page.mk (W64 (id : Int)) fl (W16 0) (W32 0))).length = 16 by
    simp [pageBytes, leBytes_length]]
  iframe

/-- What page region `t` holds after `k` iterations of `init`'s loop. -/
def initReg (ps k t : Nat) : List w8 :=
  if t < k then initMetaPage ps t else List.replicate ps (W8 0)

/-- The loop's step on its two regions: region `k` taken (zeros), given back as meta page `k`. -/
theorem regs_acc (s : Loc) (ps k : Nat) (hk : k < 2) :
    bytesPointsto (GF := GF) s (DFrac.own 1) (initReg ps k 0) ∗
      bytesPointsto (s +ₗ (ps : Nat)) (DFrac.own 1) (initReg ps k 1) ⊢
    bytesPointsto (s +ₗ ((k * ps : Nat) : Int)) (DFrac.own 1) (List.replicate ps (W8 0)) ∗
      (bytesPointsto (s +ₗ ((k * ps : Nat) : Int)) (DFrac.own 1) (initMetaPage ps k) -∗
        bytesPointsto s (DFrac.own 1) (initReg ps (k + 1) 0) ∗
          bytesPointsto (s +ₗ (ps : Nat)) (DFrac.own 1) (initReg ps (k + 1) 1)) := by
  rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
  · simp only [initReg, Nat.lt_irrefl, Nat.not_lt_zero, ↓reduceIte, Nat.zero_mul,
      show (0 : Nat) < 0 + 1 from Nat.zero_lt_one, show ¬ (1 < 0 + 1) by omega]
    rw [show s +ₗ ((0 : Nat) : Int) = s by simp [Loc.add]]
    iintro ⟨H0, H1⟩
    iframe
    iintro H0
    iframe
  · simp only [initReg, Nat.lt_irrefl, ↓reduceIte, Nat.one_mul, show (0 : Nat) < 1 from Nat.zero_lt_one,
      show (0 : Nat) < 1 + 1 by omega, show (1 : Nat) < 1 + 1 by omega]
    iintro ⟨H0, H1⟩
    iframe
    iintro H1
    iframe

/-- A buffer of four pages is its four pages. -/
theorem bytes_app4 (s : Loc) (ps : Nat) (c0 c1 c2 c3 : List w8) (h0 : c0.length = ps)
    (h1 : c1.length = ps) (h2 : c2.length = ps) :
    bytesPointsto (GF := GF) s (DFrac.own 1) (c0 ++ (c1 ++ (c2 ++ c3))) ⊣⊢
      bytesPointsto s (DFrac.own 1) c0 ∗ bytesPointsto (s +ₗ (ps : Nat)) (DFrac.own 1) c1 ∗
        bytesPointsto (s +ₗ ((2 * ps : Nat) : Int)) (DFrac.own 1) c2 ∗
        bytesPointsto (s +ₗ ((3 * ps : Nat) : Int)) (DFrac.own 1) c3 := by
  refine (bytesPointsto_app _ _ _ _).trans (sep_congr .rfl ?_)
  rw [h0]
  refine (bytesPointsto_app _ _ _ _).trans (sep_congr .rfl ?_)
  rw [h1, loc_add_nat, show ps + ps = 2 * ps by omega]
  refine (bytesPointsto_app _ _ _ _).trans (sep_congr .rfl ?_)
  rw [h2, loc_add_nat, show 2 * ps + ps = 3 * ps by omega]
  exact .rfl

theorem initMetaPage_length (ps k : Nat) (h : 80 ≤ ps) : (initMetaPage ps k).length = ps := by
  simp [initMetaPage, pageBytes, leBytes_length, metaBytes_length]; omega

theorem initEmptyPage_length (ps id : Nat) (fl : w16) (h : 16 ≤ ps) :
    (initEmptyPage ps id fl).length = ps := by
  simp [initEmptyPage, pageBytes, leBytes_length]; omega

theorem initBytes_length (ps : Nat) (h : 80 ≤ ps) : (initBytes ps).length = ps * 4 := by
  simp only [initBytes, List.length_append, initMetaPage_length ps _ h,
    initEmptyPage_length ps _ _ (by omega)]
  omega

theorem writeBytes_empty (ds : List w8) : writeBytes [] 0 ds = ds := by
  simp [writeBytes]

theorem init_sint (k : Nat) (h : k < 2 ^ 62) : sint.Z (W64 (k : Int)) = k := by word

theorem init_mul4 (ps : Nat) (h : ps < 2 ^ 32) :
    sint.Z (W64 (ps : Int) * W64 4) = ps * 4 := by
  have h1 : uint.Z (W64 (ps : Int)) = ps := by word
  have h4' : uint.Z (W64 4) = 4 := by decide
  have h2 : uint.Z (W64 (ps : Int)) * uint.Z (W64 4) < 2 ^ 64 := by
    rw [h1, h4']; omega
  have h3 := word.unsigned_mul_nowrap _ _ h2
  have h4 : uint.Z (W64 (ps : Int) * W64 4) < 2 ^ 63 := by rw [h3, h1, h4']; omega
  have h5 : sint.Z (W64 (ps : Int) * W64 4) = uint.Z (W64 (ps : Int) * W64 4) := by word
  rw [h5, h3, h1, h4']

theorem init_mul4_nat (ps : Nat) (h : ps < 2 ^ 32) :
    sint.nat (W64 (ps : Int) * W64 4) = ps * 4 := by
  rw [show sint.nat (W64 (ps : Int) * W64 4) = (sint.Z (W64 (ps : Int) * W64 4)).toNat from rfl,
    init_mul4 ps h]
  omega

/-- Page `k` of the buffer: `k * ps` bytes in. -/
theorem init_pg (ps k : Nat) (h : ps < 2 ^ 32) (hk : k < 4) :
    sint.Z (W64 (k : Int) * W64 (ps : Int)) = ((k * ps : Nat) : Int) := by
  have h1 : uint.Z (W64 (ps : Int)) = ps := by word
  have hk1 : uint.Z (W64 (k : Int)) = k := by word
  have hlt : k * ps < 2 ^ 34 := by
    have := Nat.mul_le_mul_right ps (show k ≤ 4 by omega); omega
  have h2 : uint.Z (W64 (k : Int)) * uint.Z (W64 (ps : Int)) < 2 ^ 64 := by
    rw [h1, hk1]; omega
  have h3 := word.unsigned_mul_nowrap _ _ h2
  have h4 : uint.Z (W64 (k : Int) * W64 (ps : Int)) < 2 ^ 63 := by rw [h3, h1, hk1]; omega
  have h5 : sint.Z (W64 (k : Int) * W64 (ps : Int)) = uint.Z (W64 (k : Int) * W64 (ps : Int)) := by
    word
  rw [h5, h3, h1, hk1]; push_cast; rfl

end lemmas

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]
variable [linux : GOOSLinux]

set_option maxHeartbeats 1000000 in
theorem DB.init.wp_proof (hpib : DB.pageInBuffer.spec (GF := GF) (hG := hG))
    (hSetId : _root_.Perennial.EtcdGrove.bbolt.Page.SetId.spec (GF := GF) (hG := hG))
    (hSetFlags : _root_.Perennial.EtcdGrove.bbolt.Page.SetFlags.spec (GF := GF) (hG := hG))
    (hSetCount : _root_.Perennial.EtcdGrove.bbolt.Page.SetCount.spec (GF := GF) (hG := hG))
    (hMeta : _root_.Perennial.EtcdGrove.bbolt.Page.Meta.spec (GF := GF) (hG := hG))
    (hSetMagic : _root_.Perennial.EtcdGrove.bbolt.Meta.SetMagic.spec (GF := GF) (hG := hG))
    (hSetVersion : _root_.Perennial.EtcdGrove.bbolt.Meta.SetVersion.spec (GF := GF) (hG := hG))
    (hSetPageSize : _root_.Perennial.EtcdGrove.bbolt.Meta.SetPageSize.spec (GF := GF) (hG := hG))
    (hSetFreelist : _root_.Perennial.EtcdGrove.bbolt.Meta.SetFreelist.spec (GF := GF) (hG := hG))
    (hSetRoot : _root_.Perennial.EtcdGrove.bbolt.Meta.SetRootBucket.spec (GF := GF) (hG := hG))
    (hSetPgid : _root_.Perennial.EtcdGrove.bbolt.Meta.SetPgid.spec (GF := GF) (hG := hG))
    (hSetTxid : _root_.Perennial.EtcdGrove.bbolt.Meta.SetTxid.spec (GF := GF) (hG := hG))
    (hSetChecksum : _root_.Perennial.EtcdGrove.bbolt.Meta.SetChecksum.spec (GF := GF) (hG := hG))
    (hSum64 : _root_.Perennial.EtcdGrove.bbolt.Meta.Sum64.spec (GF := GF) (hG := hG))
    (hNewIB : _root_.Perennial.EtcdGrove.bbolt.NewInBucket.spec (GF := GF) (hG := hG))
    (hWriteAt : os.File.WriteAt.spec (GF := GF) (hG := hG))
    (hfdatasync : _root_.Perennial.EtcdGrove.bbolt.fdatasync.spec (GF := GF) (hG := hG))
    (hLogger : DB.Logger.spec (GF := GF) (hG := hG))
    (hErrorf : DefaultLogger.Errorf.spec (GF := GF) (hG := hG)) :
    DB.init.spec (GF := GF) (hG := hG) := by
  intro dbl f fd ps lg dl wa dq Hdbl Hps80 Hps32 Hlg Hwa
  wp_start as ⟨#Hlogger, #Hdl, #Hdlok, Hps, Hf, Hwa', #Hof, Hfb, Hmap⟩
  wp_auto
  wp_apply wp_slice_make2 (V := w8) as %s ⟨Hs, -⟩
  · ipureintro; rw [init_mul4 ps Hps32]; omega
  try wp_auto
  rw [init_mul4_nat ps Hps32, show (zero_val w8 : w8) = W8 0 from rfl]
  have hne : List.replicate (ps * 4) (W8 0) ≠ [] :=
    List.ne_nil_of_length_pos (by rw [List.length_replicate]; omega)
  icases (ownSlice_bytes s _ _ hne).1 $$ Hs with ⟨Hs, %Hslen⟩
  icases persistent_entails_left (bytesPointsto_car s.ptr _ _ hne) $$ Hs with ⟨Hs, %Hcar⟩
  rw [show ps * 4 = ps + (ps + (ps + ps)) by omega, ← List.replicate_append_replicate,
    ← List.replicate_append_replicate, ← List.replicate_append_replicate]
  icases (bytes_app4 (hG := hG) s.ptr ps _ _ _ _ (by simp) (by simp) (by simp)).1 $$ Hs
    with ⟨R0, R1, R2, R3⟩
  ihave IH : iprop(∃ (k : Nat), "i" ∷ i_ptr ↦ W64 (k : Int) ∗ "%Hk" ∷ ⌜k ≤ 2⌝ ∗
      "R0" ∷ bytesPointsto s.ptr (DFrac.own 1) (initReg ps k 0) ∗
      "R1" ∷ bytesPointsto (s.ptr +ₗ (ps : Nat)) (DFrac.own 1) (initReg ps k 1) ∗
      "Hps" ∷ structFieldRef DB go!"pageSize" dbl ↦{dq} W64 (ps : Int) ∗
      "db" ∷ db_ptr ↦ dbl ∗ "buf" ∷ buf_ptr ↦ s) $$ [i R0 R1 Hps db buf]
  · iexists 0; simp only [initReg, Nat.not_lt_zero, ↓reduceIte]; iframe; ipureintro; omega
  wp_for IH
  rw [init_sint k (by omega), show sint.Z (W64 2) = 2 from rfl]
  by_cases hk2 : (k : Int) < 2
  · rw [decide_eq_true hk2]
    simp only [↓reduceIte]
    try wp_auto
    have hkn : k < 2 := by omega
    have hlen : sint.Z s.len = ps * 4 := by
      have := Hslen.1; rw [List.length_replicate] at this; omega
    wp_apply hpib dbl (W64 (ps : Int)) dq s (W64 (k : Int)) Hcar
      (by rw [init_pg ps k Hps32 (by omega)]; omega)
      (by rw [init_pg ps k Hps32 (by omega), hlen]; push_cast
          have := Nat.mul_le_mul_right ps (show k ≤ 1 by omega); omega) $$ [Hps] as Hps
    · iframe
    try wp_auto
    rw [init_pg ps k Hps32 (by omega)]
    icases regs_acc s.ptr ps k hkn $$ [R0 R1] with ⟨Hreg, Hback⟩
    · iframe
    have hcark : (s.ptr +ₗ ((k * ps : Nat) : Int)).locCar ≠ 0 := by simpa [Loc.add] using Hcar
    icases zero_region (hG := hG) _ ps hcark Hps80 $$ Hreg with ⟨Hpg, Hm, Hz⟩
    wp_apply hSetId _ _ _ $$ [Hpg] as Hpg
    · iframe
    try wp_auto
    wp_apply hSetFlags _ _ _ $$ [Hpg] as Hpg
    · iframe
    try wp_auto
    wp_apply hMeta _
    try wp_auto
    have hcarm : (s.ptr +ₗ ((k * ps : Nat) : Int) +ₗ 16).locCar ≠ 0 := by simpa [Loc.add] using Hcar
    rw [show Magic = #(W32 3977042669) from rfl]
    wp_apply hSetMagic _ _ _ $$ [Hm] as Hm
    · iframe
    try wp_auto
    rw [show Version = #(W32 2) from rfl]
    wp_apply hSetVersion _ _ _ $$ [Hm] as Hm
    · iframe
    try wp_auto
    wp_apply hSetPageSize _ _ _ $$ [Hm] as Hm
    · iframe
    try wp_auto
    wp_apply hSetFreelist _ _ _ $$ [Hm] as Hm
    · iframe
    try wp_auto
    wp_apply hNewIB
    try wp_auto
    wp_apply hSetRoot _ _ _ $$ [Hm] as Hm
    · iframe
    try wp_auto
    wp_apply hSetPgid _ _ _ $$ [Hm] as Hm
    · iframe
    try wp_auto
    wp_apply hSetTxid _ _ _ $$ [Hm] as Hm
    · iframe
    try wp_auto
    rw [init_sint ps (by omega)]
    ihave Hm : (s.ptr +ₗ ((k * ps : Nat) : Int) +ₗ 16) ↦ initMeta0 ps k $$ [Hm]
    · unfold initMeta0; iexact Hm
    wp_apply hSum64 _ _ _ hcarm $$ [Hm] as Hm
    · iframe
    try wp_auto
    wp_apply hSetChecksum _ _ _ $$ [Hm] as Hm
    · iframe
    try wp_auto
    ihave Hm : (s.ptr +ₗ ((k * ps : Nat) : Int) +ₗ 16) ↦ initMeta ps k $$ [Hm]
    · unfold initMeta; iexact Hm
    ihave Hpg : (s.ptr +ₗ ((k * ps : Nat) : Int)) ↦ Page.mk (W64 (k : Int)) (W16 4) (W16 0) (W32 0)
      $$ [Hpg]
    · iexact Hpg
    ihave Hreg := meta_page_join (hG := hG) (s.ptr +ₗ ((k * ps : Nat) : Int)) ps k hcark $$ [Hpg Hm Hz]
    · iframe
    ihave HR := Hback $$ Hreg
    icases HR with ⟨R0, R1⟩
    wp_for_post
    try wp_auto
    iframe
    iexists (k + 1)
    rw [show W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) by push_cast; word]
    iframe
    ipureintro; omega
  · rw [decide_eq_false hk2]
    simp only [Bool.false_eq_true, ↓reduceIte]
    try wp_auto
    have hk : k = 2 := by omega
    subst hk
    have hlen : sint.Z s.len = ps * 4 := by
      have := Hslen.1; rw [List.length_replicate] at this; omega
    -- page 2: the freelist's, empty
    wp_apply hpib dbl (W64 (ps : Int)) dq s (W64 2) Hcar
      (by rw [show (W64 2 : w64) = W64 ((2 : Nat) : Int) from rfl, init_pg ps 2 Hps32 (by omega)]; omega)
      (by rw [show (W64 2 : w64) = W64 ((2 : Nat) : Int) from rfl, init_pg ps 2 Hps32 (by omega), hlen]
          push_cast; omega) $$ [Hps] as Hps
    · iframe
    try wp_auto
    rw [show (W64 2 : w64) = W64 ((2 : Nat) : Int) from rfl, init_pg ps 2 Hps32 (by omega)]
    have hc2 : (s.ptr +ₗ ((2 * ps : Nat) : Int)).locCar ≠ 0 := by simpa [Loc.add] using Hcar
    icases (zero_page (hG := hG) _ ps hc2 (by omega)).1 $$ R2 with ⟨Hpg, Hz⟩
    wp_apply hSetId _ _ _ $$ [Hpg] as Hpg
    · iframe
    try wp_auto
    wp_apply hSetFlags _ _ _ $$ [Hpg] as Hpg
    · iframe
    try wp_auto
    wp_apply hSetCount _ _ _ $$ [Hpg] as Hpg
    · iframe
    try wp_auto
    ihave Hpg : (s.ptr +ₗ ((2 * ps : Nat) : Int)) ↦ Page.mk (W64 ((2 : Nat) : Int)) (W16 16) (W16 0) (W32 0)
      $$ [Hpg]
    · iexact Hpg
    ihave R2 := empty_page_join (hG := hG) _ ps 2 (W16 16) hc2 $$ [Hpg Hz]
    · iframe
    -- page 3: the root, an empty leaf
    wp_apply hpib dbl (W64 (ps : Int)) dq s (W64 3) Hcar
      (by rw [show (W64 3 : w64) = W64 ((3 : Nat) : Int) from rfl, init_pg ps 3 Hps32 (by omega)]; omega)
      (by rw [show (W64 3 : w64) = W64 ((3 : Nat) : Int) from rfl, init_pg ps 3 Hps32 (by omega), hlen]
          push_cast; omega) $$ [Hps] as Hps
    · iframe
    try wp_auto
    rw [show (W64 3 : w64) = W64 ((3 : Nat) : Int) from rfl, init_pg ps 3 Hps32 (by omega)]
    have hc3 : (s.ptr +ₗ ((3 * ps : Nat) : Int)).locCar ≠ 0 := by simpa [Loc.add] using Hcar
    icases (zero_page (hG := hG) _ ps hc3 (by omega)).1 $$ R3 with ⟨Hpg, Hz⟩
    wp_apply hSetId _ _ _ $$ [Hpg] as Hpg
    · iframe
    try wp_auto
    wp_apply hSetFlags _ _ _ $$ [Hpg] as Hpg
    · iframe
    try wp_auto
    wp_apply hSetCount _ _ _ $$ [Hpg] as Hpg
    · iframe
    try wp_auto
    ihave Hpg : (s.ptr +ₗ ((3 * ps : Nat) : Int)) ↦ Page.mk (W64 ((3 : Nat) : Int)) (W16 2) (W16 0) (W32 0)
      $$ [Hpg]
    · iexact Hpg
    ihave R3 := empty_page_join (hG := hG) _ ps 3 (W16 2) hc3 $$ [Hpg Hz]
    · iframe
    -- the buffer: a fresh database
    simp only [initReg, show (0 : Nat) < 2 by omega, show (1 : Nat) < 2 by omega, ↓reduceIte]
    ihave Hs := (bytes_app4 (hG := hG) s.ptr ps _ _ _ _ (initMetaPage_length ps 0 Hps80)
      (initMetaPage_length ps 1 Hps80) (initEmptyPage_length ps 2 _ (by omega))).2 $$ [R0 R1 R2 R3]
    · iframe
    have hib : initBytes ps = initMetaPage ps 0 ++ (initMetaPage ps 1 ++
        (initEmptyPage ps 2 (W16 16) ++ initEmptyPage ps 3 (W16 2))) := by
      simp only [initBytes, List.append_assoc]
    rw [← hib]
    have hne' : initBytes ps ≠ [] :=
      List.ne_nil_of_length_pos (by rw [initBytes_length ps Hps80]; omega)
    ihave Hs := (ownSlice_bytes s _ _ hne').2 $$ [Hs]
    · iframe; ipureintro
      rw [initBytes_length ps Hps80]; exact ⟨by omega, Hslen.2⟩
    rw [Hwa]
    ihave Hmr : mapRange (GF := GF) none [] (min (sint.nat (W64 0)) 0) (sint.nat (W64 0) +
      (initBytes ps).length) $$ []
    · simp only [mapRange]; itrivial
    wp_apply hWriteAt f fd [] none s (initBytes ps) (DFrac.own 1) (W64 0) (by decide)
      $$ [Hof Hfb Hmap Hs Hmr] as %n %werr ⟨%kw, %hkw, Hfb, Hmap, Hs, -⟩
    · iframe; iframe #
    try wp_auto
    have hDl : (if lg = interface.nil then discardIface dl else lg) = discardIface dl := by
      rcases Hlg with h | h <;> rw [h] <;> simp [discardIface, interface.mkOk]
    cases werr with
    | ok ewi =>
      -- the write failed: log it, the error
      try wp_auto
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, -⟩
      try wp_auto
      wp_apply hLogger dbl DFrac.discard lg dl Hdbl $$ [Hlogger Hdl] as -
      · iframe; iframe #
      rw [hDl]
      try wp_auto
      wp_apply hErrorf dl _ _ $$ [Hdlok]
      · iframe; iexact Hdlok
      try wp_auto
      iapply HΦ
      iframe
      iright
      isplitr
      · ipureintro; intro h; cases h
      iexists _; iframe
    | nil =>
      obtain ⟨hk1, -, hk3⟩ := hkw
      have hk : kw = (initBytes ps).length := hk3 rfl
      subst hk
      try rw [List.take_length]
      rw [writeBytes_empty]
      try wp_auto
      wp_apply hfdatasync dbl f fd dq $$ [Hf Hof] as %ferr Hf
      · iframe; iframe #
      try wp_auto
      cases ferr with
      | ok efi =>
        try wp_auto
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %sl ⟨Hsl, -⟩
        try wp_auto
        rw [GOOSLinux.goos]
        try wp_auto
        wp_apply hLogger dbl DFrac.discard lg dl Hdbl $$ [Hlogger Hdl] as -
        · iframe; iframe #
        rw [hDl]
        try wp_auto
        wp_apply hErrorf dl _ _ $$ [Hdlok]
        · iframe; iexact Hdlok
        try wp_auto
        iapply HΦ
        iframe
        iright
        ipureintro; intro h; cases h
      | nil =>
        try wp_auto
        iapply HΦ
        iframe
        ileft
        iframe
        ipureintro; rfl

end proof

end bbolt
end EtcdGrove
end Perennial
