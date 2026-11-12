/-
`db.init()` (U11f of `notes/bbolt-proof-plan.md`; the fork's crash-safe `init`,
`nonissues/bbolt-init-not-crash-safe.md`): on an empty file, the four pages `Open/InitImage.initImg`
written in two `pwrite`s (the freelist and root pages after zeroed meta slots, synced; then the
two meta pages, synced). Its spec is internal (`init` is called only by `Open`): an empty file,
unmapped; on success the file holds `initImg`, on an error (`fmt` formats it) its contents are
unknown.
-/
module

public import Proof.go_etcd_io.bbolt.Open.InitImage
public import Proof.go_etcd_io.bbolt.Inv.Locks
public import Proof.go_etcd_io.bbolt.Mmap.Logger
public import Proof.go_etcd_io.bbolt.Mmap.Infra
public import Proof.go_etcd_io.bbolt.Commit.MetaPage
public import Proof.go_etcd_io.bbolt.Commit.PwMeta
public import Spec.go_etcd_io.bbolt.DB__pageInBuffer
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
public import Proof.go_etcd_io.bbolt.internal.common.Lemmas.Bytes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **`db.init()` on an empty, unmapped file** `p` (`Open`'s fresh case): on success the file
holds `initImg` (still unmapped); on an error (`fmt` formats it) only its `OsMeta` is left. -/
abbrev DB.init.spec : Prop :=
  ∀ (db f : Loc) (fd : w64) (p : BFile) (lg : GoInterface) (m : OsMeta) (dqf dqw : DFrac),
  db ≠ null → m.size = 0 → m.maps = ∅ →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ osInv (GF := GF) ∗
      db.[DB, go!"pageSize"] ↦□ W64 4096 ∗ db.[DB, go!"logger"] ↦□ lg ∗ boltLogger lg ∗
      (db.[DB, go!"ops"]).[dbOps, go!"writeAt"] ↦{dqw}
        methods (go.GoType.PointerType os.File.ty) go!"WriteAt" #f ∗
      db.[DB, go!"file"] ↦{dqf} f ∗ fileOwn f fd p.path (DFrac.own 1) ∗
      osFd fd (DFrac.own 1) ⟨p.ino, true, true⟩ ∗ osMeta p.ino (DFrac.own 1) m ∗
      osBytes p.ino 0 (DFrac.own 1) [] }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"init")) (Val #()))
  {{ (err : GoInterface), RET #err;
      (db.[DB, go!"ops"]).[dbOps, go!"writeAt"] ↦{dqw}
        methods (go.GoType.PointerType os.File.ty) go!"WriteAt" #f ∗
      db.[DB, go!"file"] ↦{dqf} f ∗ fileOwn f fd p.path (DFrac.own 1) ∗
      osFd fd (DFrac.own 1) ⟨p.ino, true, true⟩ ∗
      ((⌜err = interface.nil⌝ ∗ ∃ (m' : OsMeta) (xs : List ByteG),
          osMeta p.ino (DFrac.own 1) m' ∗ osBytes p.ino 0 (DFrac.own 1) xs ∗
          ⌜m'.maps = ∅ ∧ xs.length = m'.size ∧ xs.map Prod.fst = initImg⌝) ∨
       (⌜err ≠ interface.nil⌝ ∗ fmtErrorOk err ∗ ∃ m' : OsMeta, osMeta p.ino (DFrac.own 1) m')) }}

end spec

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

theorem initImg_split :
    initImg = (metaBuf (initMv 0) ++ metaBuf (initMv 1)) ++
      (emptyPg 2 (W16 16) ++ emptyPg 3 (W16 2)) := by
  simp only [initImg, List.append_assoc]

/-- The first write's data: the meta slots zero, then the freelist and root pages. -/
def initPages : List w8 := List.replicate 8192 (W8 0) ++ (emptyPg 2 (W16 16) ++ emptyPg 3 (W16 2))

theorem emptyPgs_length : (emptyPg 2 (W16 16) ++ emptyPg 3 (W16 2)).length = 8192 := by
  simp only [List.length_append, emptyPg_length]

theorem metaBufs_length : (metaBuf (initMv 0) ++ metaBuf (initMv 1)).length = 8192 := by
  simp only [List.length_append, metaBuf_length]

theorem initPages_length : initPages.length = 16384 := by
  simp only [initPages, List.length_append, List.length_replicate, emptyPg_length]

omit [GooseExts] in
/-- A 16384-byte list's halves, as `ownSlice_slice` cuts it at 8192. -/
theorem halves_parts (l1 l2 : List w8) (h1 : l1.length = 8192) (h2 : l2.length = 8192) :
    (l1 ++ l2).take (sint.nat (W64 8192)) = l1 ∧
      subslice (sint.nat (W64 8192)) (sint.nat (W64 16384)) (l1 ++ l2) = l2 ∧
      (l1 ++ l2).drop (sint.nat (W64 16384)) = [] := by
  have hl : (l1 ++ l2).length = 16384 := by simp only [List.length_append, h1, h2]
  rw [show sint.nat (W64 8192) = 8192 from rfl, show sint.nat (W64 16384) = 16384 from rfl]
  refine ⟨List.take_left' h1, ?_, List.drop_of_length_le (by omega)⟩
  unfold subslice
  rw [List.take_of_length_le (by omega), List.drop_left' h1]

omit [GooseExts] in
theorem copy_result (E : List w8) (hE : E.length = 8192) :
    E.take (List.replicate 8192 (W8 0)).length ++ (List.replicate 8192 (W8 0)).drop E.length = E := by
  rw [List.length_replicate, List.drop_replicate, hE, Nat.sub_self, List.replicate_zero,
    List.append_nil, ← hE, List.take_length]

omit [GooseExts] in
/-- **A `pwrite` of all of `data` to an empty file**: the file's bytes are `data`. -/
theorem pwBytes_fresh (data : List w8) (h : 0 < data.length) :
    (pwBytes 0 0 data data.length []).map Prod.fst = data := by
  have hs : pwSize 0 0 data.length = data.length := by unfold pwSize; split <;> omega
  unfold pwBytes
  rw [hs, show min (0 + data.length) data.length - min 0 0 = data.length by omega]
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    unfold pwByte
    simp only [Nat.not_lt_zero, ↓reduceIte, Nat.zero_add, Nat.sub_zero, Nat.min_self]
    have hi : i < data.length := by simp at h1; omega
    simp only [hi, ↓reduceIte]
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by simp at h1; omega), Option.getD_some]

omit [GooseExts] in
theorem pwSize_fresh (n : Nat) (h : 0 < n) : pwSize 0 0 n = n := by
  unfold pwSize; split <;> omega

theorem initImg_join :
    metaBuf (initMv 0) ++ metaBuf (initMv 1) ++ initPages.drop 8192 = initImg := by
  rw [initImg_split]; unfold initPages
  rw [List.drop_left' (List.length_replicate (n := 8192) (a := W8 0))]

omit [GooseExts] in
theorem errorf_mem : go!"Errorf" ∈ boltLogMethods := by decide

omit [GooseExts] in
set_option maxRecDepth 20000 in
theorem fmtVerbs_writeAt : fmtVerbs go!"writeAt failed: %v" = some [W8 118] := by decide

omit [GooseExts] in
set_option maxRecDepth 20000 in
theorem fmtVerbs_sync :
    fmtVerbs go!"[GOOS: %s, GOARCH: %s] fdatasync failed: %v" = some [W8 115, W8 115, W8 118] := by
  decide

omit [GooseExts] in
/-- A 16384-byte list's first half, as `ownSlice_slice` cuts it at `[0, 8192)`. -/
theorem first_half (l1 l2 : List w8) (h1 : l1.length = 8192) :
    (l1 ++ l2).take (sint.nat (W64 0)) = [] ∧
      subslice (sint.nat (W64 0)) (sint.nat (W64 8192)) (l1 ++ l2) = l1 := by
  rw [show sint.nat (W64 0) = 0 from rfl, show sint.nat (W64 8192) = 8192 from rfl]
  refine ⟨List.take_zero, ?_⟩
  unfold subslice
  rw [List.drop_zero, List.take_left' h1]

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

omit package_sem go_gctx sem in
/-- A file's page-cache bytes, cut in two. -/
theorem osBytes_app (p : BFile) (off : Nat) (dq : DFrac) (xs ys : List ByteG) :
    osBytes (GF := GF) p.ino off dq (xs ++ ys) ⊣⊢
      osBytes (GF := GF) p.ino off dq xs ∗ osBytes (GF := GF) p.ino (off + xs.length) dq ys := by
  unfold osBytes; exact bytesG_append _ _ _ _ _ _

theorem DB.init.wp_proof (hLogger : DB.Logger.spec (GF := GF) (hG := hG))
    (hPIB : DB.pageInBuffer.spec (GF := GF) (hG := hG))
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
    (hNewIB : internal.common.NewInBucket.spec (GF := GF) (hG := hG))
    (hWriteAt : os.File.WriteAt.spec (GF := GF) (hG := hG))
    (hSync : fdatasync.spec (GF := GF) (hG := hG)) :
    DB.init.spec (GF := GF) (hG := hG) := by
  intro db f fd p lg m dqf dqw hdb hsz hmaps
  wp_start as ⟨#Hos, #Hps, #Hlg, #Hlgok, Hwa, Hf, Hfo, Hfd, Hm, Hxs⟩
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
      "db" ∷ db_ptr ↦ db ∗ "buf" ∷ buf_ptr ↦ sl : IProp GF) $$ [i Hb db buf]
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
    wp_apply hPIB db sl (W64 (k : Int)) (by rw [hslen]; simp; omega) (by rw [hslen]; decide) Hpos
      $$ []
    · iframe #
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
    -- page 2: the freelist's, empty
    wp_apply hPIB db sl (W64 2) (by rw [hslen]; decide) (by rw [hslen]; decide) Hpos $$ []
    · iframe #
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
    wp_apply hPIB db sl (W64 3) (by rw [hslen]; decide) (by rw [hslen]; decide) Hpos $$ []
    · iframe #
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
    wp_apply wp_slice_make2 (V := w8) $$ [] as %pg ⟨Hpg, Hpcap⟩
    · ipureintro; decide
    rw [show (zero_val w8 : w8) = W8 0 from rfl, show sint.nat (W64 4096 * W64 4) = 16384 from rfl]
    ihave %Hplen := ownSlice_len _ _ _ $$ Hpg
    ihave %Hpcw := ownSliceCap_wf _ _ $$ Hpcap
    have hpl : pg.len = W64 16384 := by
      have h1 := Hplen.1; rw [List.length_replicate] at h1; simp only [sint.nat] at h1; word
    have hsl : sl.len = W64 16384 := by word
    rw [hpl] at Hpcw
    rw [hsl] at Hbcw
    try wp_auto
    rw [show W64 4096 * W64 2 = W64 8192 from rfl, hpl]
    rw [ite_eq_left ⟨by decide, by decide, Hpcw.2⟩]
    try wp_auto
    rw [show W64 4096 * W64 2 = W64 8192 from rfl, hsl]
    rw [ite_eq_left ⟨by decide, by decide, Hbcw.2⟩]
    try wp_auto
    -- the copy of the freelist and root pages
    ihave Hpg : pg ↦* (List.replicate 8192 (W8 0) ++ List.replicate 8192 (W8 0)) $$ [Hpg]
    · rw [List.replicate_append_replicate]; iexact Hpg
    have hpr := halves_parts _ _ (List.length_replicate (n := 8192) (a := W8 0))
      (List.length_replicate (n := 8192) (a := W8 0))
    icases (ownSlice_slice (W64 8192) (W64 16384) pg (DFrac.own 1) _
      ⟨by decide, by decide, by rw [hpl]; decide⟩).1 $$ Hpg with ⟨HpA, HpB, HpC⟩
    rw [hpr.1, hpr.2.1, hpr.2.2]
    rw [initImg_split] at *
    have hsr := halves_parts _ _ metaBufs_length emptyPgs_length
    icases (ownSlice_slice (W64 8192) (W64 16384) sl (DFrac.own 1) _
      ⟨by decide, by decide, by rw [hsl]; decide⟩).1 $$ Hsl with ⟨HsA, HsB, HsC⟩
    rw [hsr.1, hsr.2.1, hsr.2.2]
    wp_apply wp_slice_copy (V := w8) _ _ _ _ (DFrac.own 1) $$ [HpB HsB] as %_n ⟨-, HpB, HsB⟩
    · iframe
    rw [copy_result _ emptyPgs_length]
    ihave Hpg := (ownSlice_slice (W64 8192) (W64 16384) pg (DFrac.own 1) initPages
      ⟨by decide, by decide, by rw [hpl]; decide⟩).2 $$ [HpA HpB HpC]
    · have hq := halves_parts _ _ (List.length_replicate (n := 8192) (a := W8 0)) emptyPgs_length
      unfold initPages
      rw [hq.1, hq.2.1, hq.2.2]
      iframe
    ihave Hsl := (ownSlice_slice (W64 8192) (W64 16384) sl (DFrac.own 1) _
      ⟨by decide, by decide, by rw [hsl]; decide⟩).2 $$ [HsA HsB HsC]
    · rw [hsr.1, hsr.2.1, hsr.2.2]
      iframe
    try wp_auto
    -- the first write: the freelist and root pages, the meta slots zero
    have hm0 : min (W64 0).toNat m.size = 0 := by rw [hsz]; simp
    wp_apply hWriteAt f fd p (DFrac.own 1) pg initPages (DFrac.own 1) (W64 0) (DFrac.own 1)
      ⟨p.ino, true, true⟩ 1 m [] rfl (by decide) (by rw [initPages_length]; decide)
      (by rw [initPages_length]; decide) (by rw [hsz]; simp) (fun _ => rfl)
      $$ [Hfo Hpg Hfd Hm Hxs] as %n %err ⟨Hfo, Hpg, Hfd, %j, %ys, %h, %Hj, Hm, Hys, Hc, Herr⟩
    · iframe #
      rw [← fileOwn_eq, hm0]
      iframe Hfo Hpg Hfd Hm Hxs
      rw [hmaps]; unfold mcellsAny; iapply BigSepM.bigSepM_empty.2; iempintro
    obtain ⟨hjle, hysp, -, -, hres⟩ := Hj
    cases lg with
    | nil => unfold boltLogger; iexfalso; iexact Hlgok
    | ok li =>
    cases err with
    | ok ei =>
      -- the write failed: log, return the error
      simp only [fmtErrorOkOrNil]
      icases Herr with #Herr
      try wp_auto
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl2 ⟨Hsl2, -⟩
      try wp_auto
      wp_apply hLogger db (.ok li) hdb $$ []
      · iframe #
      try wp_auto
      wp_apply wp_boltLog li _ _ [W8 118] _ [GoInterface.ok ei] _ iprop(True) _
        errorf_mem fmtVerbs_writeAt rfl $$ Hlgok [Hsl2] [] [] as Hsl2 -
      · iexact Hsl2
      · simp only [List.zip_cons_cons, List.zip_nil_left, Iris.BI.BigSepL.bigSepL_cons,
          Iris.BI.BigSepL.bigSepL_nil]
        isplitr
        · iapply logArgOk_of_fmtErrorOk
          · simp [methodVerbs]
          iexact Herr
        iempintro
      wp_auto
      iapply HΦ
      rw [← fileOwn_eq]
      iframe Hwa Hf Hfo Hfd
      iright
      isplitr
      · ipureintro; exact fun h => nomatch h
      iframe Herr
      iexists _; iexact Hm
    | nil =>
      have hj : j = initPages.length := by
        rcases hres with ⟨h1, -, -⟩ | ⟨-, h2⟩
        · exact h1
        · exact absurd rfl h2
      subst hj
      rw [hsz, show (W64 0).toNat = 0 from rfl,
        pwBytes_fresh _ (by rw [initPages_length]; decide)] at hysp
      rw [hsz, show (W64 0).toNat = 0 from rfl, pwSize_fresh _ (by rw [initPages_length]; decide),
        initPages_length] at *
      rw [show min 0 0 = 0 from rfl] at *
      have hysl : ys.length = 16384 := by
        have := congrArg List.length hysp; simp only [List.length_map] at this
        rw [this, initPages_length]
      try wp_auto
      -- the first sync
      ihave Hfo : fileOwn f fd p.path (DFrac.own 1) $$ [Hfo]
      · rw [fileOwn_eq]; iexact Hfo
      wp_apply hSync db f fd p _ dqf (DFrac.own 1) $$ [Hf Hfo Hfd Hm]
        as %e2 ⟨Hf, Hfo, Hfd, ⟨%m2, Hm, %Hm2⟩, Hr⟩
      · iframe #; iframe
      icases Hr with (%He | ⟨%He, #Hfe⟩)
      rotate_left
      · -- the sync failed: log, return the error
        cases e2 with
        | nil => exact absurd rfl He
        | ok e2 =>
        ihave %hgoos : ⌜goosLinux⌝ $$ []
        · iapply goosLinux_of_pkgInit $$ Hpkg
        ihave %hgoarch : ⌜goarchAmd64⌝ $$ []
        · iapply goarchAmd64_of_pkgInit $$ Hpkg
        unfold goosLinux at hgoos
        unfold goarchAmd64 at hgoarch
        clear hysp hysl Hm2 hpr hsr hres hjle hm0
        try wp_auto
        try rw [hgoos, hgoarch]
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %sl3 ⟨Hsl3, -⟩
        try wp_auto
        wp_apply hLogger db (.ok li) hdb $$ []
        · iframe #
        try wp_auto
        wp_apply wp_boltLog li _ _ [W8 115, W8 115, W8 118] _
          [interface.mkOk go.string #(go!"linux"), interface.mkOk go.string #(go!"amd64"),
            GoInterface.ok e2] _ iprop(True) _
          errorf_mem fmtVerbs_sync rfl $$ Hlgok [Hsl3] [] [] as Hsl3 -
        · simp only [show sint.nat (W64 (0 + 1)) = 1 from rfl,
            show sint.nat (W64 (0 + 1 + 1)) = 2 from rfl, List.set_cons_succ, List.set_cons_zero]
          iexact Hsl3
        · log_args_ok
        wp_auto
        iapply HΦ
        iframe Hwa Hf Hfo Hfd
        iright
        isplitr
        · ipureintro; exact fun h => nomatch h
        iframe Hfe
        iexists _; iexact Hm
      subst He
      try wp_auto
      -- the second write: the two meta pages
      have hm2s : m2.size = 16384 := by rw [Hm2.1]
      have hm2m : m2.maps = ∅ := by rw [Hm2.2]; exact hmaps
      rw [show W64 4096 * W64 2 = W64 8192 from rfl]
      have hc8 : sint.Z (W64 8192) ≤ sint.Z sl.cap := by
        have h := Hbcw.2; rw [show sint.Z (W64 16384) = 16384 from rfl] at h
        rw [show sint.Z (W64 8192) = 8192 from rfl]; omega
      rw [ite_eq_left ⟨by decide, by decide, hc8⟩]
      try wp_auto
      have hfh := first_half _ (emptyPg 2 (W16 16) ++ emptyPg 3 (W16 2)) metaBufs_length
      icases (ownSlice_slice (W64 0) (W64 8192) sl (DFrac.own 1) _
        ⟨by decide, by decide, by rw [hsl]; decide⟩).1 $$ Hsl with ⟨HsA, HsB, HsC⟩
      rw [hfh.1, hfh.2]
      ihave Hys : osBytes p.ino 0 (DFrac.own 1) (ys.take 8192 ++ ys.drop 8192) $$ [Hys]
      · rw [List.take_append_drop]; iexact Hys
      icases (osBytes_app p 0 (DFrac.own 1) (ys.take 8192) (ys.drop 8192)).1 $$ Hys
        with ⟨Hy1, Hy2⟩
      have hy1 : (ys.take 8192).length = 8192 := by simp [hysl]
      have hm20 : min (W64 0).toNat m2.size = 0 := by simp
      wp_apply hWriteAt f fd p (DFrac.own 1) _ (metaBuf (initMv 0) ++ metaBuf (initMv 1))
        (DFrac.own 1) (W64 0) (DFrac.own 1) ⟨p.ino, true, true⟩ 1 m2 (ys.take 8192) rfl (by decide)
        (by rw [metaBufs_length]; decide) (by rw [metaBufs_length]; decide)
        (by rw [hy1, metaBufs_length, hm2s]; simp) (fun _ => rfl)
        $$ [Hfo HsB Hfd Hm Hy1] as %n2 %err2 ⟨Hfo, HsB, Hfd, %j2, %ys2, %h2, %Hj2, Hm, Hys2, Hc,
          Herr2⟩
      · iframe #
        rw [← fileOwn_eq, hm20]
        iframe Hfo HsB Hfd Hm Hy1
        rw [hm2m]; unfold mcellsAny; iapply BigSepM.bigSepM_empty.2; iempintro
      obtain ⟨hjle2, hysp2, -, -, hres2⟩ := Hj2
      cases err2 with
      | ok ei =>
        -- the write failed: log, return the error
        simp only [fmtErrorOkOrNil]
        icases Herr2 with #Herr
        clear hysp hysl Hm2 hpr hsr hres hjle hm0 hysp2 hres2
        try wp_auto
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %sl2 ⟨Hsl2, -⟩
        try wp_auto
        wp_apply hLogger db (.ok li) hdb $$ []
        · iframe #
        try wp_auto
        wp_apply wp_boltLog li _ _ [W8 118] _ [GoInterface.ok ei] _ iprop(True) _
          errorf_mem fmtVerbs_writeAt rfl $$ Hlgok [Hsl2] [] [] as Hsl2 -
        · iexact Hsl2
        · simp only [List.zip_cons_cons, List.zip_nil_left, Iris.BI.BigSepL.bigSepL_cons,
            Iris.BI.BigSepL.bigSepL_nil]
          isplitr
          · iapply logArgOk_of_fmtErrorOk
            · simp [methodVerbs]
            iexact Herr
          iempintro
        wp_auto
        iapply HΦ
        rw [← fileOwn_eq]
        iframe Hwa Hf Hfo Hfd
        iright
        isplitr
        · ipureintro; exact fun h => nomatch h
        iframe Herr
        iexists _; iexact Hm
      | nil =>
        have hj2 : j2 = (metaBuf (initMv 0) ++ metaBuf (initMv 1)).length := by
          rcases hres2 with ⟨h1, -, -⟩ | ⟨-, h2⟩
          · exact h1
          · exact absurd rfl h2
        have hys2 : ys2.map Prod.fst = metaBuf (initMv 0) ++ metaBuf (initMv 1) := by
          rw [hysp2]
          have := pwBytes_inside_fst m2.size (W64 0).toNat (metaBuf (initMv 0) ++ metaBuf (initMv 1))
            j2 (ys.take 8192) (by rw [metaBufs_length, hm2s]; decide)
            (by rw [hy1, metaBufs_length]) (Or.inr hj2)
          rw [this, if_neg (by rw [hj2, metaBufs_length]; decide)]
        have hys2l : ys2.length = 8192 := by
          have := congrArg List.length hys2; simp only [List.length_map] at this
          rw [this, metaBufs_length]
        have hsz2 : pwSize m2.size (W64 0).toNat j2 = 16384 := by
          rw [hm2s]; exact pwSize_inside _ _ _ 8192 (by rw [hj2, metaBufs_length]; exact Nat.le_refl _) (by decide)
        have hsz2' : pwSize m2.size 0 j2 = 16384 := by simpa using hsz2
        rw [hsz2, hm20] at *
        try wp_auto
        -- the second sync
        ihave Hfo : fileOwn f fd p.path (DFrac.own 1) $$ [Hfo]
        · rw [fileOwn_eq]; iexact Hfo
        wp_apply hSync db f fd p _ dqf (DFrac.own 1) $$ [Hf Hfo Hfd Hm]
          as %e3 ⟨Hf, Hfo, Hfd, ⟨%m3, Hm, %Hm3⟩, Hr⟩
        · iframe #; iframe
        icases Hr with (%He | ⟨%He, #Hfe⟩)
        rotate_left
        · -- the sync failed: log, return the error
          cases e3 with
          | nil => exact absurd rfl He
          | ok e3 =>
          ihave %hgoos : ⌜goosLinux⌝ $$ []
          · iapply goosLinux_of_pkgInit $$ Hpkg
          ihave %hgoarch : ⌜goarchAmd64⌝ $$ []
          · iapply goarchAmd64_of_pkgInit $$ Hpkg
          unfold goosLinux at hgoos
          unfold goarchAmd64 at hgoarch
          clear hysp hysl Hm2 hpr hsr hres hjle hm0 hysp2 hres2 hys2 Hm3
          try wp_auto
          try rw [hgoos, hgoarch]
          wp_apply wp_slice_literal
          isplitr
          · ipureintro; rfl
          iintro %sl3 ⟨Hsl3, -⟩
          try wp_auto
          wp_apply hLogger db (.ok li) hdb $$ []
          · iframe #
          try wp_auto
          wp_apply wp_boltLog li _ _ [W8 115, W8 115, W8 118] _
            [interface.mkOk go.string #(go!"linux"), interface.mkOk go.string #(go!"amd64"),
              GoInterface.ok e3] _ iprop(True) _
            errorf_mem fmtVerbs_sync rfl $$ Hlgok [Hsl3] [] [] as Hsl3 -
          · simp only [show sint.nat (W64 (0 + 1)) = 1 from rfl,
              show sint.nat (W64 (0 + 1 + 1)) = 2 from rfl, List.set_cons_succ,
              List.set_cons_zero]
            iexact Hsl3
          · log_args_ok
          wp_auto
          iapply HΦ
          iframe Hwa Hf Hfo Hfd
          iright
          isplitr
          · ipureintro; exact fun h => nomatch h
          iframe Hfe
          iexists _; iexact Hm
        subst He
        try wp_auto
        iapply HΦ
        iframe Hwa Hf Hfo Hfd
        ileft
        isplitr
        · ipureintro; rfl
        iexists m3, ys2 ++ ys.drop 8192
        iframe Hm
        isplitl [Hys2 Hy2]
        · iapply (osBytes_app p 0 (DFrac.own 1) ys2 (ys.drop 8192)).2
          rw [hys2l]
          rw [hy1] at *
          iframe
        ipureintro
        refine ⟨by rw [Hm3.2, Hm2.2]; exact hmaps, ?_, ?_⟩
        · rw [Hm3.1]; simp [hys2l, hysl, hsz2']
        · rw [List.map_append, hys2, List.map_drop, hysp, initImg_join, initImg_split]

end proof

end bbolt
end EtcdGrove
end Perennial
