/-
The definitions and lemmas of `DB__commit.lean`'s proof, in a module of their own so that the
crash proofs (`DB__commitCrash.lean`) import them without the proof (import tiers, 2026-11-18).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.DB__commit
public import Spec.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.DB__mmap
public import Spec.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.pageAt
public import Spec.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.Page__meta
public import Spec.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.Meta__write
public import Spec.os.File__Truncate
public import Spec.os.File__Sync
public import Spec.os.File__WriteAt
public import Spec.os.File__Fd
public import Spec.syscall.Fdatasync
public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.Publish
public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.InitLayout
public import Perennial.Proof.sync.Results

@[expose] public section

noncomputable section

namespace Perennial

open Fs
namespace EtcdGrove
namespace osfs_bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs

section proof
-- `curMeta` stays folded (`wp_auto` unfolding it cost repeated unifications: DB__Snapshot.lean)
attribute [local irreducible] curMeta
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.Assumptions]

/-- `commit`'s error result, besides the error (see the spec). -/
def commitErr (γ : DBNames) (db f : Loc) (fd : w64) (p : GoString) (t : Nat) : IProp GF :=
  iprop((∃ n, dbOwner (GF := GF) γ t n) ∗
    ∃ (mp' : List w8) (fl : Bool) (hwm : Nat) (st' : MapSt) (m' : OsMeta),
      writerStF (GF := GF) γ db f fd p mp' fl hwm st' m' ∗
      (⌜fl = false⌝ ∨ (⌜fl = true⌝ ∗ dbFailed (GF := GF) γ)))

/-- An error exit of `commit` while the handle is not yet failed, with a mapping. -/
theorem commitErr_of (γ : DBNames) (db f : Loc) (fd : w64) (p : GoString) (mp : List w8)
    (hwm : Nat) (base : Loc) (len : Nat) (γm : GName) (m2 : OsMeta)
    (mxc tail : List ByteG) (fsz t n : Nat)
    (h : m2.maps = {[base := len]} ∧ m2.size ≤ len ∧ 0 < base.addr ∧ len ≤ 2 ^ 41 ∧ 2 ≤ hwm ∧
      4096 * hwm ≤ m2.size ∧ mxc.length = 8192 ∧ tail.length = m2.size - 4096 * hwm) :
    dbOwner (GF := GF) γ t n ∗ ghostVar γ.cur (1 : Qp).half.half (mp, false, hwm) ∗
      ghostVar γ.map (1 : Qp).half (some (base, len, γm)) ∗ ghostVar γ.out (1 : Qp).half.half false ∗
      mapFields (GF := GF) db (DFrac.own (1 : Qp).half) (some (base, len, γm)) ∗
      clsOpen (GF := GF) γ fd ∗ ghostVar γm (1 : Qp).half () ∗
      mapInv (GF := GF) γ γ.ino base len γm ∗ writerCells (GF := GF) base hwm len ∗
      db.[DB, go!"filesz"] ↦ W64 fsz ∗ db.[DB, go!"datasz"] ↦ W64 len ∗
      os.ownFile (GF := GF) f fd p (DFrac.own (1 : Qp).half) ∗
      osFd (GF := GF) fd (DFrac.own (1 : Qp).half) ⟨γ.ino, true, true, none, some true⟩ ∗
      osMeta (GF := GF) γ.ino (DFrac.own 1) m2 ∗ osBytes (GF := GF) γ.ino 0 (DFrac.own (1 : Qp).half) mxc ∗
      osBytes (GF := GF) γ.ino (4096 * hwm) (DFrac.own 1) tail ⊢
      commitErr (GF := GF) γ db f fd p t := by
  iintro ⟨Hown, Hcur, Hmap, Hout, Hflds, Hcls, Htok, #Hinv, Hwc, Hfsz, Hdsz, Hf, Hfd, Hm, Hmx, Htail⟩
  ihave Hown : ∃ n', dbOwner (GF := GF) γ t n' $$ [Hown]
  · iexists n; iexact Hown
  unfold commitErr writerStF writerFile
  iframe
  dsimp only [mapLen]
  iframe; iframe #
  isplitr
  · ipureintro
    exact ⟨⟨h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2, fun h => by cases h⟩,
      h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  · ileft; ipureintro; rfl

/-- The writer's cells, with their top part. -/
theorem writerCells_top (base : Loc) (hwm len : Nat) :
    writerCells (GF := GF) base hwm len ⊣⊢
      ((∃ vf, cellsR (GF := GF) base 0 16 vf) ∗ (∃ vf, cellsR (GF := GF) base 80 4016 vf) ∗
        (∃ vf, cellsR (GF := GF) base 4096 16 vf) ∗ (∃ vf, cellsR (GF := GF) base 4176 4016 vf)) ∗
      cellsAny (GF := GF) base (4096 * hwm) (len - 4096 * hwm) := by
  unfold writerCells cellsAny
  exact ⟨by iintro ⟨H0, H1, H2, H3, H4⟩; iframe, by iintro ⟨⟨H0, H1, H2, H3⟩, H4⟩; iframe⟩

/-- A grown file (`Truncate` to the mapping's length `len`), as the writer's: its bytes from the
high water mark on and their cells. -/
theorem grown_writer (p : Ino) (base : Loc) (m' : OsMeta) (len hwm : Nat)
    (tail : List ByteG) (vf : Nat → val) (hmaps : m'.maps = {[base := len]})
    (hsz : m'.size ≤ len) (h4 : 4096 * hwm ≤ m'.size) (htl : tail.length = m'.size - 4096 * hwm) :
    os.ftDone (GF := GF) p m' len ∗ osBytes (GF := GF) p (4096 * hwm) (DFrac.own 1) tail ∗
      cellsR (GF := GF) base (4096 * hwm) (m'.size - 4096 * hwm) vf ⊢
      ∃ tail2, ⌜tail2.length = len - 4096 * hwm⌝ ∗ osMeta (GF := GF) p (DFrac.own 1) (rsPost true m' len len) ∗
        osBytes (GF := GF) p (4096 * hwm) (DFrac.own 1) tail2 ∗
        cellsAny (GF := GF) base (4096 * hwm) (len - 4096 * hwm) := by
  iintro ⟨Hg, Htail, Hlow⟩
  iunfold os.ftDone at Hg
  icases Hg with ⟨%zs, %hzl, Hm, Hz, Hc⟩
  iexists tail ++ zs.map (fun c => ((0 : w8), c))
  iframe Hm
  isplitr
  · ipureintro; simp; omega
  isplitl [Htail Hz]
  · iapply (osBytes_app p (4096 * hwm) _ tail _).2
    rw [htl, show 4096 * hwm + (m'.size - 4096 * hwm) = m'.size by omega]
    iframe
  rw [hmaps] at *
  rw [show min m'.size len = m'.size by omega]
  have hR := le_rsHi true m'.size len
  icases (mcells_single_past (GF := GF) base len m'.size (rsHi true m'.size len) _ hsz (by omega)).1
    $$ Hc with Hc
  rw [show len - 4096 * hwm = (m'.size - 4096 * hwm) + (len - m'.size) by omega]
  iapply cellsAny_append
  isplitl [Hlow]
  · unfold cellsAny; iexists vf; iexact Hlow
  rw [show 4096 * hwm + (m'.size - 4096 * hwm) = m'.size by omega]
  unfold cellsAny; iexists _; iexact Hc

/-- The cells past the file's end, back with the writer's. -/
theorem cells_back (base : Loc) (m' : OsMeta) (len hwm hi : Nat) (vf : Nat → val)
    (hmaps : m'.maps = {[base := len]}) (hsz : m'.size ≤ len) (h4 : 4096 * hwm ≤ m'.size)
    (hhi : len ≤ hi) :
    mcellsAny (GF := GF) m'.maps m'.size hi ∗ cellsR (GF := GF) base (4096 * hwm) (m'.size - 4096 * hwm) vf ⊢
      cellsAny (GF := GF) base (4096 * hwm) (len - 4096 * hwm) := by
  iintro ⟨Hc, Hlow⟩
  rw [hmaps]
  icases (mcellsAny_single_past (GF := GF) base len m'.size hi hsz hhi).1 $$ Hc with Hc
  rw [show len - 4096 * hwm = (m'.size - 4096 * hwm) + (len - m'.size) by omega]
  iapply cellsAny_append
  isplitl [Hlow]
  · unfold cellsAny; iexists vf; iexact Hlow
  rw [show 4096 * hwm + (m'.size - 4096 * hwm) = m'.size by omega]
  iexact Hc

/-- A page's bytes holding a header and a `w64` after it (a leaf page of one value): a typed
header, the typed value 16 bytes on, and the rest. -/
theorem valPage_view (l : Loc) (dq : DFrac) (hdr : Page) (x : w64) (rest : List w8)
    (hl : 0 < l.addr) :
    bytesPointsto (GF := GF) l dq (encode hdr ++ encode x ++ rest) ⊣⊢
      l ↦{dq} hdr ∗ (l +ₗ 16) ↦{dq} x ∗ bytesPointsto (l +ₗ 24) dq rest := by
  have h16 : 0 < (l +ₗ 16).addr := by simp only [Loc.add]; omega
  have hs1 := bytesPointsto_app (GF := GF) l dq (encode hdr ++ encode x) rest
  have hs2 := bytesPointsto_app (GF := GF) l dq (encode hdr) (encode x)
  have e1 : (((encode hdr).length : Nat) : Int) = 16 := by rw [ByteEncoding.encode_length]; rfl
  have e2 : (((encode hdr ++ encode x).length : Nat) : Int) = 24 := by
    simp only [List.length_append, ByteEncoding.encode_length]; rfl
  rw [e2] at hs1
  rw [e1] at hs2
  have th := typedPointsto_bytes (GF := GF) l hdr dq hl
  have tv := typedPointsto_bytes (GF := GF) (l +ₗ 16) x dq h16
  constructor
  · iintro H
    icases hs1.1 $$ H with ⟨H1, H2⟩
    icases hs2.1 $$ H1 with ⟨Hh, Hv⟩
    iframe H2
    isplitl [Hh]
    · iapply th.2 $$ Hh
    · iapply tv.2 $$ Hv
  · iintro ⟨Hh, Hv, H2⟩
    iapply hs1.2
    iframe H2
    iapply hs2.2
    isplitl [Hh]
    · iapply th.1 $$ Hh
    · iapply tv.1 $$ Hv

/-- The header of `commit`'s data page `pg`: a leaf page of one element. -/
def dataHdr (pg : w64) : Page := ⟨pg, W16 2, W16 1, W32 0⟩

/-- `commit`'s data page `pg`, holding `v`. -/
def dataPage (pg v : w64) : List w8 := encode (dataHdr pg) ++ encode v ++ List.replicate 4072 0

theorem dataPage_length (pg v : w64) : (dataPage pg v).length = 4096 := by
  simp only [dataPage, List.length_append, ByteEncoding.encode_length, List.length_replicate]

theorem dataPage_val (pg v : w64) : pageVal (dataPage pg v) = some v := by
  unfold pageVal dataPage pageHdrOf
  rw [List.append_assoc, List.take_left' (ByteEncoding.encode_length _), ByteEncoding.decode_encode]
  simp only [dataHdr, if_pos]
  rw [List.drop_left' (ByteEncoding.encode_length _), List.take_left' (ByteEncoding.encode_length _),
    ByteEncoding.decode_encode]

theorem zeroPage_val : List.replicate 4096 (0 : w8) =
    encode (pageHdr (W64 0) (W16 0)) ++ encode (W64 0 : w64) ++ List.replicate 4072 0 := by
  rw [encode_pageHdr_zero, show encode (W64 0 : w64) = List.replicate 8 0 from rfl]
  simp only [zeroBytes, List.replicate_append_replicate]

theorem pwSize_inside (sz off k : Nat) (h : off + k ≤ sz) : pwSize sz off k = sz := by
  unfold pwSize; split <;> omega

/-- A page's bytes and cells back with the rest of the writer's, from the high water mark on. -/
theorem page_rejoin (p : Ino) (base : Loc) (hwm len : Nat) (ys rest : List ByteG)
    (hys : ys.length = 4096) (hl : 4096 * hwm + 4096 ≤ len) :
    osBytes (GF := GF) p (4096 * hwm) (DFrac.own 1) ys ∗
      osBytes (GF := GF) p (4096 * hwm + 4096) (DFrac.own 1) rest ∗
      cellsAny (GF := GF) base (4096 * hwm) 4096 ∗
      cellsAny (GF := GF) base (4096 * hwm + 4096) (len - 4096 * hwm - 4096) ⊢
      osBytes (GF := GF) p (4096 * hwm) (DFrac.own 1) (ys ++ rest) ∗
        cellsAny (GF := GF) base (4096 * hwm) (len - 4096 * hwm) := by
  iintro ⟨H1, H2, C1, C2⟩
  isplitl [H1 H2]
  · iapply (osBytes_app p _ _ ys rest).2
    rw [hys]
    isplitl [H1]
    · iexact H1
    · iexact H2
  · obtain ⟨k, hk⟩ : ∃ k, len - 4096 * hwm - 4096 = k := ⟨_, rfl⟩
    rw [hk, show len - 4096 * hwm = 4096 + k by omega]
    iapply (cellsAny_append base (4096 * hwm) 4096 k)
    isplitl [C1]
    · iexact C1
    · iexact C2

/-- An error exit of `commit` while writing the data page (not yet failed): its bytes and cells
back with the writer's. -/
theorem dataErr (γ : DBNames) (db f : Loc) (fd : w64) (p : GoString) (mp : List w8)
    (hwm : Nat) (base : Loc) (len : Nat) (γm : GName) (m3 : OsMeta)
    (mxc ys rest : List ByteG) (fsz t n : Nat)
    (h : m3.maps = {[base := len]} ∧ m3.size ≤ len ∧ 0 < base.addr ∧ len ≤ 2 ^ 41 ∧ 2 ≤ hwm ∧
      4096 * hwm + 4096 ≤ m3.size ∧ mxc.length = 8192 ∧ ys.length = 4096 ∧
      rest.length = m3.size - 4096 * hwm - 4096) :
    dbOwner (GF := GF) γ t n ∗ ghostVar γ.cur (1 : Qp).half.half (mp, false, hwm) ∗
      ghostVar γ.map (1 : Qp).half (some (base, len, γm)) ∗ ghostVar γ.out (1 : Qp).half.half false ∗
      mapFields (GF := GF) db (DFrac.own (1 : Qp).half) (some (base, len, γm)) ∗
      clsOpen (GF := GF) γ fd ∗ ghostVar γm (1 : Qp).half () ∗
      mapInv (GF := GF) γ γ.ino base len γm ∗
      ((∃ vf, cellsR (GF := GF) base 0 16 vf) ∗ (∃ vf, cellsR (GF := GF) base 80 4016 vf) ∗
        (∃ vf, cellsR (GF := GF) base 4096 16 vf) ∗ (∃ vf, cellsR (GF := GF) base 4176 4016 vf)) ∗
      cellsAny (GF := GF) base (4096 * hwm) 4096 ∗
      cellsAny (GF := GF) base (4096 * hwm + 4096) (len - 4096 * hwm - 4096) ∗
      db.[DB, go!"filesz"] ↦ W64 fsz ∗ db.[DB, go!"datasz"] ↦ W64 len ∗
      os.ownFile (GF := GF) f fd p (DFrac.own (1 : Qp).half) ∗
      osFd (GF := GF) fd (DFrac.own (1 : Qp).half) ⟨γ.ino, true, true, none, some true⟩ ∗
      osMeta (GF := GF) γ.ino (DFrac.own 1) m3 ∗ osBytes (GF := GF) γ.ino 0 (DFrac.own (1 : Qp).half) mxc ∗
      osBytes (GF := GF) γ.ino (4096 * hwm) (DFrac.own 1) ys ∗
      osBytes (GF := GF) γ.ino (4096 * hwm + 4096) (DFrac.own 1) rest ⊢
      commitErr (GF := GF) γ db f fd p t := by
  iintro ⟨Hown, Hcur, Hmap, Hout, Hflds, Hcls, Htok, #Hinv, Hwc4, Hpc, Htop, Hfsz, Hdsz, Hf, Hfd, Hm,
    Hmx, Hpg, Hrest⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  icases page_rejoin γ.ino base hwm len ys rest h8 (by omega) $$ [Hpg Hrest Hpc Htop] with ⟨Htail, Htop⟩
  · iframe Hpg Hrest Hpc Htop
  ihave Hwc := (writerCells_top base hwm len).2 $$ [Hwc4 Htop]
  · iframe Hwc4 Htop
  iapply commitErr_of γ db f fd p mp hwm base len γm m3 mxc (ys ++ rest) fsz t n
    ⟨h1, h2, h3, h4, h5, by omega, h7, by simp only [List.length_append]; omega⟩
  iframe Hown Hcur Hmap Hout Hflds Hcls Htok Hwc Hfsz Hdsz Hf Hfd Hm Hmx Htail
  iframe #

/-- The writer's cells of meta page `i` besides its meta: its header and its tail. -/
def hdrTail (base : Loc) (i : Nat) : IProp GF :=
  iprop((∃ vf, cellsR (GF := GF) base (4096 * i) 16 vf) ∗
    (∃ vf, cellsR (GF := GF) base (4096 * i + 80) 4016 vf))

theorem hdrTails (base : Loc) :
    ((∃ vf, cellsR (GF := GF) base 0 16 vf) ∗ (∃ vf, cellsR (GF := GF) base 80 4016 vf) ∗
      (∃ vf, cellsR (GF := GF) base 4096 16 vf) ∗ (∃ vf, cellsR (GF := GF) base 4176 4016 vf)) ⊣⊢
      hdrTail (GF := GF) base 0 ∗ hdrTail (GF := GF) base 1 := by
  unfold hdrTail
  rw [show 4096 * 0 = 0 from rfl, show 0 + 80 = 80 from rfl, show 4096 * 1 = 4096 from rfl,
    show 4096 + 80 = 4176 from rfl]
  exact ⟨by iintro ⟨H0, H1, H2, H3⟩; iframe H0 H1 H2 H3, by iintro ⟨⟨H0, H1⟩, H2, H3⟩; iframe H0 H1 H2 H3⟩

/-- Meta page `i`'s cells, from its header, its meta and its tail. -/
theorem metaPage_cells (base : Loc) (i : Nat) :
    hdrTail (GF := GF) base i ∗ cellsAny (GF := GF) base (4096 * i + 16) 64 ⊢
      cellsAny (GF := GF) base (4096 * i) 4096 := by
  unfold hdrTail
  iintro ⟨⟨⟨%v0, H0⟩, ⟨%v1, H1⟩⟩, Hm⟩
  rw [show (4096 : Nat) = 16 + 4080 from rfl]
  iapply (cellsAny_append base (4096 * i) 16 4080)
  isplitl [H0]
  · unfold cellsAny; iexists v0; iexact H0
  rw [show (4080 : Nat) = 64 + 4016 from rfl]
  iapply (cellsAny_append base (4096 * i + 16) 64 4016)
  isplitl [Hm]
  · iexact Hm
  rw [show 4096 * i + 16 + 64 = 4096 * i + 80 by omega]
  unfold cellsAny; iexists v1; iexact H1

/-- Meta page `i`'s cells, as its header, its meta and its tail. -/
theorem metaPage_cells_split (base : Loc) (i : Nat) :
    cellsAny (GF := GF) base (4096 * i) 4096 ⊢
      hdrTail (GF := GF) base i ∗ cellsAny (GF := GF) base (4096 * i + 16) 64 := by
  unfold hdrTail
  iintro H
  rw [show (4096 : Nat) = 16 + 4080 from rfl]
  icases (cellsAny_split base (4096 * i) 16 4080) $$ H with ⟨H0, H⟩
  rw [show (4080 : Nat) = 64 + 4016 from rfl]
  icases (cellsAny_split base (4096 * i + 16) 64 4016) $$ H with ⟨Hm, H1⟩
  unfold cellsAny
  icases H0 with ⟨%v0, H0⟩
  icases H1 with ⟨%v1, H1⟩
  rw [show 4096 * i + 16 + 64 = 4096 * i + 80 by omega]
  iframe Hm
  isplitl [H0]
  · iexists v0; iexact H0
  · iexists v1; iexact H1

/-- An error exit of `commit` once it failed the handle (the meta's write or sync), with a mapping:
the writer's half of the meta pages' bytes `mxc`, the data page's bytes and cells back with the
rest. -/
theorem dataErrT (γ : DBNames) (db f : Loc) (fd : w64) (p : GoString) (mp : List w8)
    (hwm : Nat) (base : Loc) (len : Nat) (γm : GName) (m3 : OsMeta)
    (mxc ys rest : List ByteG) (fsz t n : Nat)
    (h : m3.maps = {[base := len]} ∧ m3.size ≤ len ∧ 0 < base.addr ∧ len ≤ 2 ^ 41 ∧ 2 ≤ hwm ∧
      4096 * hwm + 4096 ≤ m3.size ∧ mxc.length = 8192 ∧ ys.length = 4096 ∧
      rest.length = m3.size - 4096 * hwm - 4096) :
    dbOwner (GF := GF) γ t n ∗ dbFailed (GF := GF) γ ∗ ghostVar γ.cur (1 : Qp).half.half (mp, true, hwm) ∗
      ghostVar γ.map (1 : Qp).half (some (base, len, γm)) ∗ ghostVar γ.out (1 : Qp).half.half false ∗
      mapFields (GF := GF) db (DFrac.own (1 : Qp).half) (some (base, len, γm)) ∗
      clsOpen (GF := GF) γ fd ∗ ghostVar γm (1 : Qp).half () ∗
      mapInv (GF := GF) γ γ.ino base len γm ∗ hdrTail (GF := GF) base 0 ∗ hdrTail (GF := GF) base 1 ∗
      cellsAny (GF := GF) base (4096 * hwm) 4096 ∗
      cellsAny (GF := GF) base (4096 * hwm + 4096) (len - 4096 * hwm - 4096) ∗
      db.[DB, go!"filesz"] ↦ W64 fsz ∗ db.[DB, go!"datasz"] ↦ W64 len ∗
      os.ownFile (GF := GF) f fd p (DFrac.own (1 : Qp).half) ∗
      osFd (GF := GF) fd (DFrac.own (1 : Qp).half) ⟨γ.ino, true, true, none, some true⟩ ∗
      osMeta (GF := GF) γ.ino (DFrac.own 1) m3 ∗ osBytes (GF := GF) γ.ino 0 (DFrac.own (1 : Qp).half) mxc ∗
      osBytes (GF := GF) γ.ino (4096 * hwm) (DFrac.own 1) ys ∗
      osBytes (GF := GF) γ.ino (4096 * hwm + 4096) (DFrac.own 1) rest ⊢
      commitErr (GF := GF) γ db f fd p t := by
  iintro ⟨Hown, #Hfailed, Hcur, Hmap, Hout, Hflds, Hcls, Htok, #Hinv, T0, T1, Hpc, Htop, Hfsz, Hdsz, Hf,
    Hfd, Hm, Hmx, Hpg, Hrest⟩
  ihave Hown : ∃ n', dbOwner (GF := GF) γ t n' $$ [Hown]
  · iexists n; iexact Hown
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  icases page_rejoin γ.ino base hwm len ys rest h8 (by omega) $$ [Hpg Hrest Hpc Htop] with ⟨Htail, Htop⟩
  · iframe Hpg Hrest Hpc Htop
  ihave Hwc4 := (hdrTails base).2 $$ [T0 T1]
  · iframe T0 T1
  ihave Hwc := (writerCells_top base hwm len).2 $$ [Hwc4 Htop]
  · iframe Hwc4 Htop
  unfold commitErr writerStF writerFile
  iframe Hown Hcur Hmap Hout Hflds Hcls
  iexists m3
  dsimp only [mapLen]
  isplitl [Hfsz Hdsz Hf Hfd Hm Hmx Htail Htok Hwc]
  · isplitl [Hfsz Hdsz Hf Hfd Hm Hmx Htail]
    · iexists mxc, ys ++ rest, fsz
      iframe
      ipureintro
      exact ⟨h5, by omega, h7, by simp only [List.length_append]; omega, fun h => by cases h⟩
    · iframe; iframe #; ipureintro; exact ⟨h1, h2, h3, h4⟩
  · iright; iframe #; ipureintro; rfl

/-- The two metas' bytes of meta pages' bytes `xs`. -/
theorem metas_length (xs : List ByteG) (h : xs.length = 8192) :
    (((xs.map Prod.fst).drop 16).take 64 ++ ((xs.map Prod.fst).drop 4112).take 64).length = 128 := by
  rw [List.length_append, List.length_take, List.length_take, List.length_drop, List.length_drop,
    List.length_map, h]
  rfl

/-- The header of the meta page `commit` writes after `mv`. -/
def metaHdrOf (mv : Meta) : Page :=
  { pageHdr (W64 0) (W16 0) with id' := (nextMeta mv).txid' % W64 2, flags' := W16 4 }

/-- The meta page `commit` writes after `mv`. -/
def metaPageOf (mv : Meta) : List w8 :=
  encode (metaHdrOf mv) ++ encode (commitOf mv) ++ zeroBytes (pageBytes - 80)

theorem metaPageOf_length (mv : Meta) : (metaPageOf mv).length = 4096 := by
  simp only [metaPageOf, List.length_append, ByteEncoding.encode_length, List.length_replicate, pageBytes]

theorem metaPageOf_meta (mv : Meta) : pageMeta (metaPageOf mv) = commitOf mv := by
  unfold metaPageOf; exact pageMeta_encode _ _ _

/-- One of two things, by its index. -/
theorem pick_page (P : Nat → IProp GF) (i : Nat) (hi : i < 2) :
    P 0 ∗ P 1 ⊣⊢ P i ∗ P (1 - i) := by
  have : i = 0 ∨ i = 1 := by omega
  rcases this with rfl | rfl
  · exact .rfl
  · exact ⟨by iintro ⟨H0, H1⟩; iframe H0 H1, by iintro ⟨H1, H0⟩; iframe H0 H1⟩

/-- A window of the meta pages' bytes, rewritten, back with the others. -/
theorem window_join (p : Ino) (dq : DFrac) (xs ys : List ByteG) (a n : Nat)
    (h : a + n ≤ xs.length) (hy : ys.length = n) :
    osBytes (GF := GF) p 0 dq (xs.take a) ∗ osBytes (GF := GF) p a dq ys ∗
      osBytes (GF := GF) p (a + n) dq ((xs.drop a).drop n) ⊢
      osBytes (GF := GF) p 0 dq (xs.take a ++ ys ++ (xs.drop a).drop n) := by
  iintro ⟨H0, H1, H2⟩
  iapply (osBytes_app p 0 dq _ _).2
  rw [List.length_append, List.length_take, hy, show 0 + (min a xs.length + n) = a + n by omega]
  iframe H2
  iapply (osBytes_app p 0 dq _ _).2
  rw [List.length_take, show 0 + min a xs.length = a by omega]
  iframe H0 H1

theorem window_join_length (xs ys : List ByteG) (a n : Nat) (h : a + n ≤ xs.length)
    (hy : ys.length = n) : (xs.take a ++ ys ++ (xs.drop a).drop n).length = xs.length := by
  simp only [List.length_append, List.length_take, List.length_drop, hy]; omega

/-- Bytes of a file, as two halves. -/
theorem osBytes_halves (p : Ino) :
    ∀ (xs : List ByteG) (off : Nat),
    osBytes (GF := GF) p off (DFrac.own 1) xs ⊢
      osBytes (GF := GF) p off (DFrac.own (1 : Qp).half) xs ∗
        osBytes (GF := GF) p off (DFrac.own (1 : Qp).half) xs
  | [], off => by
    iintro _
    isplitl
    · iapply (osBytes_nil p off _).2; iempintro
    · iapply (osBytes_nil p off _).2; iempintro
  | x :: xs, off => by
    iintro H
    icases (osBytes_cons p off _ x xs).1 $$ H with ⟨Hx, H⟩
    icases osBytes_halves p xs (off + 1) $$ H with ⟨H1, H2⟩
    unfold osByte
    icases (gElem_split _ _ (p, off) (1 : Qp).half (1 : Qp).half x).1 $$ [Hx] with ⟨Hx1, Hx2⟩
    · rw [Qp.half_add_half]; iexact Hx
    isplitl [Hx1 H1]
    · iapply (osBytes_cons p off _ x xs).2; unfold osByte; iframe Hx1 H1
    · iapply (osBytes_cons p off _ x xs).2; unfold osByte; iframe Hx2 H2

end proof

end osfs_bboltfs
end EtcdGrove
end Perennial
