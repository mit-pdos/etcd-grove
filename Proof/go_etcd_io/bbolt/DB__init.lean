/-
`db.init()` (U11f of `notes/bbolt-proof-plan.md`; the fork's crash-safe `init`,
`issues/bbolt-init-not-crash-safe.md`): on a file of at most four pages (empty, or what an
interrupted `init` left), the four pages `Open/InitImage.initImg` (`DB.initImage`'s) written in two
`pwrite`s (the freelist and root pages after zeroed meta slots, synced; then the two meta pages,
synced), each over the whole of what the file held. Its spec is internal (`init` is called only by
`Open`): a file of at most four pages, unmapped; on success the file holds `initImg`, on an error
(`fmt` formats it) its contents are unknown.
-/
module

public import Proof.go_etcd_io.bbolt.Open.InitImage
public import Spec.go_etcd_io.bbolt.DB__initImage
public import Proof.go_etcd_io.bbolt.Inv.Locks
public import Proof.go_etcd_io.bbolt.Mmap.Logger
public import Proof.go_etcd_io.bbolt.Mmap.Infra
public import Proof.go_etcd_io.bbolt.Commit.MetaPage
public import Spec.go_etcd_io.bbolt.DB__pageInBuffer
public import Spec.go_etcd_io.bbolt.fdatasync
public import Proof.go_etcd_io.bbolt.Open.FdatasyncW
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

/-- **`db.init()` on an unmapped file `p` of at most four pages** (`Open`'s case of a new file or
one an interrupted `init` left: its first write covers all the bytes `xs` the file holds): on
success the file holds `initImg` (still unmapped); on an error (`fmt` formats it) only its
`OsMeta` is left. -/
abbrev DB.init.spec : Prop :=
  ∀ (db f : Loc) (fd : w64) (p : BFile) (lg : GoInterface) (m : OsMeta) (xs : List ByteG)
    (dqf dqw : DFrac),
  db ≠ null → m.size ≤ 16384 → xs.length = m.size → m.maps = ∅ →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ osInv (GF := GF) ∗
      db.[DB, go!"pageSize"] ↦□ W64 4096 ∗ db.[DB, go!"logger"] ↦□ lg ∗ boltLogger lg ∗
      (db.[DB, go!"ops"]).[dbOps, go!"writeAt"] ↦{dqw}
        methods (go.GoType.PointerType os.File.ty) go!"WriteAt" #f ∗
      db.[DB, go!"file"] ↦{dqf} f ∗ fileOwn f fd p.path (DFrac.own 1) ∗
      osFd fd (DFrac.own 1) (dbFd p.ino) ∗ osMeta p.ino (DFrac.own 1) m ∗
      osBytes p.ino 0 (DFrac.own 1) xs }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"init")) (Val #()))
  {{ (err : GoInterface), RET #err;
      (db.[DB, go!"ops"]).[dbOps, go!"writeAt"] ↦{dqw}
        methods (go.GoType.PointerType os.File.ty) go!"WriteAt" #f ∗
      db.[DB, go!"file"] ↦{dqf} f ∗ fileOwn f fd p.path (DFrac.own 1) ∗
      osFd fd (DFrac.own 1) (dbFd p.ino) ∗
      ((⌜err = interface.nil⌝ ∗ ∃ (m' : OsMeta) (xs : List ByteG),
          osMeta p.ino (DFrac.own 1) m' ∗ osBytes p.ino 0 (DFrac.own 1) xs ∗
          ⌜m'.maps = ∅ ∧ xs.length = m'.size ∧ xs.map Prod.fst = initImg⌝) ∨
       (⌜err ≠ interface.nil ∧ ¬ FsNoErr⌝ ∗ fmtErrorOk err ∗
          ∃ m' : OsMeta, osMeta p.ino (DFrac.own 1) m')) }}

end spec

section lemmas
variable [GooseExts]

/-- The first write's data: the meta slots zero, then the freelist and root pages. -/
def initPages : List w8 := List.replicate 8192 (W8 0) ++ (emptyPg 2 (W16 16) ++ emptyPg 3 (W16 2))

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
/-- **A `pwrite` that wrote all of `data`** (`os.PwOut` with `j = len(data) > 0`): the range's
bytes are `data`. -/
theorem pwOut_full {m : OsMeta} {off : Nat} {data : List w8} {xs ys : List ByteG}
    (h : os.PwOut m off data data.length xs ys) (h0 : 0 < data.length) :
    ys.length = data.length ∧ ys.map Prod.fst = data := by
  obtain ⟨hl, hv⟩ := h
  have hl' : ys.length = data.length := by
    rw [hl]; unfold pwSize; simp only [show ¬ data.length = 0 by omega, ↓reduceIte]; omega
  refine ⟨hl', ?_⟩
  apply List.ext_getElem (by simp [hl'])
  intro i h1 h2
  simp only [List.getElem_map]
  rw [(hv i (by simpa using h1)).1]
  have hi : i < data.length := by simpa [hl'] using h1
  simp only [pwByte, show off + i < off + data.length by omega, ↓reduceIte, Nat.add_sub_cancel_left,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

omit [GooseExts] in
/-- A `pwrite` at 0 of `n` bytes over a file of at most `n` bytes leaves `n`. -/
theorem pwSize_cover (sz n : Nat) (h : 0 < n) (hs : sz ≤ n) : pwSize sz 0 n = n := by
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

end lemmas

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
    (hImage : DB.initImage.spec (GF := GF) (hG := hG))
    (hWriteAt : os.File.WriteAt.spec (GF := GF) (hG := hG))
    (hSync : fdatasync.specW (GF := GF) (hG := hG)) :
    DB.init.spec (GF := GF) (hG := hG) := by
  intro db f fd p lg m xs dqf dqw hdb hsz hxl hmaps
  wp_start as ⟨#Hos, #Hps, #Hlg, #Hlgok, Hwa, Hf, Hfo, Hfd, Hm, Hxs⟩
  wp_auto
  wp_apply hImage db DFrac.discard $$ [] as %sl ⟨-, Hsl, Hbcap⟩
  · iframe #
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  ihave %Hbcw := ownSliceCap_wf _ _ $$ Hbcap
  have hslen : sl.len.toNat = 16384 := by
    have h1 := Hlen.1; have h2 := Hlen.2
    rw [initImg_length] at h1; simp only [sint.nat] at h1
    word
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
  have hm0 : min (W64 0).toNat m.size = 0 := by simp
  wp_apply hWriteAt f fd p.path (DFrac.own 1) pg initPages (DFrac.own 1) (W64 0) (DFrac.own 1)
    (dbFd p.ino) m xs rfl (by decide) (by simp) (by rw [initPages_length]; decide)
    (by rw [initPages_length]; decide) (by rw [initPages_length]; decide)
    (by rw [initPages_length, show (W64 0).toNat = 0 from rfl]; omega)
    $$ [Hfo Hpg Hfd Hm Hxs] as %n %err ⟨Hfo, Hpg, Hfd, %j, %ys, %Hj, Hm, Hys, Hc, Herr⟩
  · iframe #
    rw [← fileOwn_eq, show (W64 0).toNat = 0 from rfl]
    iframe Hfo Hpg Hfd Hm Hxs
    rw [hmaps]; unfold mcellsAny; iapply BigSepM.bigSepM_empty.2; iempintro
  obtain ⟨hjle, hysp, -, hres⟩ := Hj
  cases lg with
  | nil => unfold boltLogger; iexfalso; iexact Hlgok
  | ok li =>
  cases err with
  | ok ei =>
    -- the write failed: log, return the error
    have hfs : ¬ FsNoErr := by
      rcases hres with ⟨-, -, h⟩ | ⟨-, -, h⟩
      · cases h
      · exact h.resolve_right (by rw [initPages_length]; decide)
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
    · ipureintro; exact ⟨(fun h => nomatch h), hfs⟩
    iframe Herr
    iexists _; iexact Hm
  | nil =>
    have hj : j = initPages.length := by
      rcases hres with ⟨h1, -, -⟩ | ⟨-, h2⟩
      · exact h1
      · exact absurd rfl h2.1
    subst hj
    obtain ⟨hysl, hysp⟩ := pwOut_full hysp (by rw [initPages_length]; decide)
    rw [initPages_length] at hysl
    have hpsz : (pwPost m 0 initPages.length initPages.length).size = 16384 := by
      simp only [pwPost]
      rw [pwSize_cover _ _ (by rw [initPages_length]; decide) (by rw [initPages_length]; omega),
        initPages_length]
    have hpmaps : (pwPost m 0 initPages.length initPages.length).maps = m.maps := by
      simp only [pwPost, announce_maps]
    generalize pwPost m 0 initPages.length initPages.length = m1 at hpsz hpmaps ⊢
    try wp_auto
    -- the first sync
    ihave Hfo : fileOwn f fd p.path (DFrac.own 1) $$ [Hfo]
    · rw [fileOwn_eq]; iexact Hfo
    wp_apply hSync db f fd p p.ino _ dqf (DFrac.own 1) $$ [Hf Hfo Hfd Hm]
      as %e2 ⟨Hf, Hfo, Hfd, ⟨%m2, Hm, %Hm2⟩, Hr⟩
    · iframe #; iframe
    icases Hr with (%He | ⟨%He, #Hfe⟩)
    rotate_left
    · -- the sync failed: log, return the error
      cases e2 with
      | nil => exact absurd rfl He.1
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
      · ipureintro; exact ⟨(fun h => nomatch h), He.2⟩
      iframe Hfe
      iexists _; iexact Hm
    subst He
    try wp_auto
    -- the second write: the two meta pages
    have hm2s : m2.size = 16384 := by rw [Hm2.1, hpsz]
    have hm2m : m2.maps = ∅ := by rw [Hm2.2, hpmaps]; exact hmaps
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
    wp_apply hWriteAt f fd p.path (DFrac.own 1) _ (metaBuf (initMv 0) ++ metaBuf (initMv 1))
      (DFrac.own 1) (W64 0) (DFrac.own 1) (dbFd p.ino) m2 (ys.take 8192) rfl (by decide)
      (by simp) (by rw [metaBufs_length]; decide) (by rw [metaBufs_length]; decide)
      (by rw [metaBufs_length]; decide) (by rw [hy1, metaBufs_length, hm2s]; simp)
      $$ [Hfo HsB Hfd Hm Hy1] as %n2 %err2 ⟨Hfo, HsB, Hfd, %j2, %ys2, %Hj2, Hm, Hys2, Hc,
        Herr2⟩
    · iframe #
      rw [← fileOwn_eq, show (W64 0).toNat = 0 from rfl]
      iframe Hfo HsB Hfd Hm Hy1
      rw [hm2m]; unfold mcellsAny; iapply BigSepM.bigSepM_empty.2; iempintro
    obtain ⟨hjle2, hysp2, -, hres2⟩ := Hj2
    cases err2 with
    | ok ei =>
      -- the write failed: log, return the error
      have hfs : ¬ FsNoErr := by
        rcases hres2 with ⟨-, -, h⟩ | ⟨-, -, h⟩
        · cases h
        · exact h.resolve_right (by rw [metaBufs_length]; decide)
      simp only [fmtErrorOkOrNil]
      icases Herr2 with #Herr
      clear hysp hysl Hm2 hpr hsr hres hjle hm0 hysp2
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
      · ipureintro; exact ⟨(fun h => nomatch h), hfs⟩
      iframe Herr
      iexists _; iexact Hm
    | nil =>
      have hj2 : j2 = (metaBuf (initMv 0) ++ metaBuf (initMv 1)).length := by
        rcases hres2 with ⟨h1, -, -⟩ | ⟨-, h2⟩
        · exact h1
        · exact absurd rfl h2.1
      subst hj2
      obtain ⟨hys2l, hys2⟩ := pwOut_full hysp2 (by rw [metaBufs_length]; decide)
      rw [metaBufs_length] at hys2l
      have hsz2' : (pwPost m2 0 (metaBuf (initMv 0) ++ metaBuf (initMv 1)).length
          (metaBuf (initMv 0) ++ metaBuf (initMv 1)).length).size = 16384 := by
        simp only [pwPost, pwSize, hm2s, metaBufs_length]; decide
      have hpmaps2 : (pwPost m2 0 (metaBuf (initMv 0) ++ metaBuf (initMv 1)).length
          (metaBuf (initMv 0) ++ metaBuf (initMv 1)).length).maps = m2.maps := by
        simp only [pwPost, announce_maps]
      try wp_auto
      -- the second sync
      ihave Hfo : fileOwn f fd p.path (DFrac.own 1) $$ [Hfo]
      · rw [fileOwn_eq]; iexact Hfo
      wp_apply hSync db f fd p p.ino _ dqf (DFrac.own 1) $$ [Hf Hfo Hfd Hm]
        as %e3 ⟨Hf, Hfo, Hfd, ⟨%m3, Hm, %Hm3⟩, Hr⟩
      · iframe #; iframe
      icases Hr with (%He | ⟨%He, #Hfe⟩)
      rotate_left
      · -- the sync failed: log, return the error
        cases e3 with
        | nil => exact absurd rfl He.1
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
        · ipureintro; exact ⟨(fun h => nomatch h), He.2⟩
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
      refine ⟨by rw [Hm3.2, hpmaps2]; exact hm2m, ?_, ?_⟩
      · rw [Hm3.1, hsz2']; simp [hys2l, hysl]
      · rw [List.map_append, hys2, List.map_drop, hysp, initImg_join, initImg_split]

end proof

end bbolt
end EtcdGrove
end Perennial
