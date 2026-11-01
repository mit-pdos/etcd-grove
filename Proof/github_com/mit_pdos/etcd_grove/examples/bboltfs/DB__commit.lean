/- Lean-first (no Rocq counterpart). The proof of `db.commit(m, v)`: remap (`mmap`) if the next
high water mark passes the mapping; grow the file (`Truncate`, `Sync`); write the data page at the
high water mark and `Fdatasync` it (its bytes clean, it is a committed page); then, under
`metalock`, take the meta cells out of the mapping's invariant, write the meta page `txid % 2`
and `Fdatasync` it (the meta pages clean), and publish the new meta pages: `cur`, the new
committed page's cells into the invariant, `own`, `last` and the transaction map. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__commit
public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__mmap
public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.pageAt
public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.Page__meta
public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.Meta__write
public import Spec.os.File__Truncate
public import Spec.os.File__Sync
public import Spec.os.File__WriteAt
public import Spec.os.File__Fd
public import Spec.syscall.Fdatasync
public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.Writer
public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.InitLayout
public import Perennial.Proof.sync.Results

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.bboltfs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.bboltfs.Assumptions]

/-- `commit`'s error result, besides the error (see the spec). -/
def commitErr (γ : DBNames) (db f : Loc) (fd : w64) (p : GoString) (t n : Nat) : IProp GF :=
  iprop(dbOwner (GF := GF) γ t n ∗
    ∃ (mp' : List w8) (fl : Bool) (hwm : Nat) (st' : MapSt) (m' : OsMeta),
      writerStF (GF := GF) γ db f fd p mp' fl hwm st' m' ∗
      (⌜fl = false⌝ ∨ (⌜fl = true⌝ ∗ dbFailed (GF := GF) γ)))

/-- An error exit of `commit` while the handle is not yet failed, with a mapping. -/
theorem commitErr_of (γ : DBNames) (db f : Loc) (fd : w64) (p : GoString) (mp : List w8)
    (hwm : Nat) (base : Loc) (len : Nat) (γm : GName) (m2 : OsMeta)
    (mxc tail : List (w8 × Bool)) (fsz t n : Nat)
    (h : m2.maps = {[base := len]} ∧ m2.size ≤ len ∧ 0 < base.addr ∧ len ≤ 2 ^ 41 ∧ 2 ≤ hwm ∧
      4096 * hwm ≤ m2.size ∧ mxc.length = 8192 ∧ tail.length = m2.size - 4096 * hwm) :
    dbOwner (GF := GF) γ t n ∗ ghostVar γ.cur (1 : Qp).half.half (mp, false, hwm) ∗
      ghostVar γ.map (1 : Qp).half (some (base, len, γm)) ∗ ghostVar γ.out (1 : Qp).half.half false ∗
      mapFields (GF := GF) db (DFrac.own (1 : Qp).half) (some (base, len, γm)) ∗
      ghostVar γ.cls (1 : Qp).half false ∗ ghostVar γm (1 : Qp).half () ∗
      mapInv (GF := GF) γ p base len γm ∗ writerCells (GF := GF) base hwm len ∗
      db.[DB, go!"filesz"] ↦ W64 fsz ∗ db.[DB, go!"datasz"] ↦ W64 len ∗
      os.ownFile (GF := GF) f fd p (DFrac.own (1 : Qp).half) ∗
      osFd (GF := GF) fd (DFrac.own (1 : Qp).half) ⟨p, true, true⟩ ∗
      osMeta (GF := GF) p (DFrac.own 1) (some m2) ∗ osBytes (GF := GF) p 0 (DFrac.own (1 : Qp).half) mxc ∗
      osBytes (GF := GF) p (4096 * hwm) (DFrac.own 1) tail ⊢
      commitErr (GF := GF) γ db f fd p t n := by
  iintro ⟨Hown, Hcur, Hmap, Hout, Hflds, Hcls, Htok, #Hinv, Hwc, Hfsz, Hdsz, Hf, Hfd, Hm, Hmx, Htail⟩
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
theorem grown_writer (p : GoString) (base : Loc) (m' : OsMeta) (len hwm : Nat)
    (tail : List (w8 × Bool)) (vf : Nat → val) (hmaps : m'.maps = {[base := len]})
    (hsz : m'.size ≤ len) (h4 : 4096 * hwm ≤ m'.size) (htl : tail.length = m'.size - 4096 * hwm) :
    osGrown (GF := GF) p m' len len ∗ osBytes (GF := GF) p (4096 * hwm) (DFrac.own 1) tail ∗
      cellsR (GF := GF) base (4096 * hwm) (m'.size - 4096 * hwm) vf ⊢
      ∃ tail2, ⌜tail2.length = len - 4096 * hwm⌝ ∗ osMeta (GF := GF) p (DFrac.own 1) (some (m'.grown len)) ∗
        osBytes (GF := GF) p (4096 * hwm) (DFrac.own 1) tail2 ∗
        cellsAny (GF := GF) base (4096 * hwm) (len - 4096 * hwm) := by
  iintro ⟨Hg, Htail, Hlow⟩
  iunfold osGrown at Hg
  icases Hg with ⟨Hm, Hz, Hc, -⟩
  iexists tail ++ List.replicate (len - m'.size) (0, false)
  iframe Hm
  isplitr
  · ipureintro; simp; omega
  isplitl [Htail Hz]
  · iapply (osBytes_app p (4096 * hwm) _ tail _).2
    rw [htl, show 4096 * hwm + (m'.size - 4096 * hwm) = m'.size by omega]
    iframe
  rw [hmaps] at *
  icases (mcells_single (GF := GF) base len m'.size len _ hsz (Nat.le_refl _)).1 $$ Hc with Hc
  rw [show len - 4096 * hwm = (m'.size - 4096 * hwm) + (len - m'.size) by omega]
  iapply cellsAny_append
  isplitl [Hlow]
  · unfold cellsAny; iexists vf; iexact Hlow
  rw [show 4096 * hwm + (m'.size - 4096 * hwm) = m'.size by omega]
  unfold cellsAny; iexists _; iexact Hc

/-- The cells past the file's end, back with the writer's. -/
theorem cells_back (base : Loc) (m' : OsMeta) (len hwm : Nat) (vf : Nat → val)
    (hmaps : m'.maps = {[base := len]}) (hsz : m'.size ≤ len) (h4 : 4096 * hwm ≤ m'.size) :
    mcellsAny (GF := GF) m'.maps m'.size len ∗ cellsR (GF := GF) base (4096 * hwm) (m'.size - 4096 * hwm) vf ⊢
      cellsAny (GF := GF) base (4096 * hwm) (len - 4096 * hwm) := by
  iintro ⟨Hc, Hlow⟩
  rw [hmaps]
  icases (mcellsAny_single (GF := GF) base len m'.size len hsz (Nat.le_refl _)).1 $$ Hc with Hc
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
theorem page_rejoin (p : GoString) (base : Loc) (hwm len : Nat) (ys rest : List (w8 × Bool))
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
    (mxc ys rest : List (w8 × Bool)) (fsz t n : Nat)
    (h : m3.maps = {[base := len]} ∧ m3.size ≤ len ∧ 0 < base.addr ∧ len ≤ 2 ^ 41 ∧ 2 ≤ hwm ∧
      4096 * hwm + 4096 ≤ m3.size ∧ mxc.length = 8192 ∧ ys.length = 4096 ∧
      rest.length = m3.size - 4096 * hwm - 4096) :
    dbOwner (GF := GF) γ t n ∗ ghostVar γ.cur (1 : Qp).half.half (mp, false, hwm) ∗
      ghostVar γ.map (1 : Qp).half (some (base, len, γm)) ∗ ghostVar γ.out (1 : Qp).half.half false ∗
      mapFields (GF := GF) db (DFrac.own (1 : Qp).half) (some (base, len, γm)) ∗
      ghostVar γ.cls (1 : Qp).half false ∗ ghostVar γm (1 : Qp).half () ∗
      mapInv (GF := GF) γ p base len γm ∗
      ((∃ vf, cellsR (GF := GF) base 0 16 vf) ∗ (∃ vf, cellsR (GF := GF) base 80 4016 vf) ∗
        (∃ vf, cellsR (GF := GF) base 4096 16 vf) ∗ (∃ vf, cellsR (GF := GF) base 4176 4016 vf)) ∗
      cellsAny (GF := GF) base (4096 * hwm) 4096 ∗
      cellsAny (GF := GF) base (4096 * hwm + 4096) (len - 4096 * hwm - 4096) ∗
      db.[DB, go!"filesz"] ↦ W64 fsz ∗ db.[DB, go!"datasz"] ↦ W64 len ∗
      os.ownFile (GF := GF) f fd p (DFrac.own (1 : Qp).half) ∗
      osFd (GF := GF) fd (DFrac.own (1 : Qp).half) ⟨p, true, true⟩ ∗
      osMeta (GF := GF) p (DFrac.own 1) (some m3) ∗ osBytes (GF := GF) p 0 (DFrac.own (1 : Qp).half) mxc ∗
      osBytes (GF := GF) p (4096 * hwm) (DFrac.own 1) ys ∗
      osBytes (GF := GF) p (4096 * hwm + 4096) (DFrac.own 1) rest ⊢
      commitErr (GF := GF) γ db f fd p t n := by
  iintro ⟨Hown, Hcur, Hmap, Hout, Hflds, Hcls, Htok, #Hinv, Hwc4, Hpc, Htop, Hfsz, Hdsz, Hf, Hfd, Hm,
    Hmx, Hpg, Hrest⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  icases page_rejoin p base hwm len ys rest h8 (by omega) $$ [Hpg Hrest Hpc Htop] with ⟨Htail, Htop⟩
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
theorem window_join (p : GoString) (dq : DFrac) (xs ys : List (w8 × Bool)) (a n : Nat)
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

theorem window_join_length (xs ys : List (w8 × Bool)) (a n : Nat) (h : a + n ≤ xs.length)
    (hy : ys.length = n) : (xs.take a ++ ys ++ (xs.drop a).drop n).length = xs.length := by
  simp only [List.length_append, List.length_take, List.length_drop, hy]; omega

/-- Bytes of a file, as two halves. -/
theorem osBytes_halves (p : GoString) :
    ∀ (xs : List (w8 × Bool)) (off : Nat),
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

theorem DB.commit.wp_proof (wp_mmap : DB.mmap.spec (GF := GF) (hG := hG))
    (wp_Truncate : os.File.Truncate.spec (GF := GF) (hG := hG))
    (wp_Sync : os.File.Sync.spec (GF := GF) (hG := hG))
    (wp_pageAt : pageAt.spec (GF := GF) (hG := hG))
    (wp_WriteAt : os.File.WriteAt.spec (GF := GF) (hG := hG))
    (wp_Fd : os.File.Fd.spec (GF := GF) (hG := hG))
    (wp_Fdatasync : syscall.Fdatasync.spec (GF := GF) (hG := hG))
    (wp_pmeta : Page.«meta».spec (GF := GF) (hG := hG))
    (wp_write : Meta.write.spec (GF := GF) (hG := hG)) :
    DB.commit.spec (GF := GF) (hG := hG) := by
  intro γ db f fd p mp st m v Hok Ht Hb Hmok Hst
  generalize hmv : curMeta mp = mv at Ht ⊢
  generalize hhwm : curPgid mp = hwm at Hb ⊢
  have hpg : mv.pgid'.toNat = hwm := by rw [← hmv, ← hhwm]; rfl
  wp_start as ⟨#Hpkg, #Hos, #Hfile, #Hmeta, #Hguard, Hws, Hown⟩
  unfold writerSt
  icases Hws with ⟨Hcur, Hmap, Hout, Hflds, Hw, Hcls, Hstr⟩
  rcases st with _ | ⟨base, len, γm⟩
  · exact absurd rfl Hst
  dsimp only
  icases Hstr with ⟨%Hstp, Htok, #Hinv, Hwc⟩
  iunfold writerFile at Hw
  icases Hw with ⟨%mxc, %tail, %fsz, Hfsz, Hdsz, Hf, Hfd, Hm, Hmx, Htail, %Hwf⟩
  obtain ⟨hmx, hclean, rfl, hfd⟩ := Hwf.2.2.2.2 rfl
  wp_alloc «$res0_ptr» as «$res0»
  wp_pures
  wp_alloc_auto
  wp_pures
  wp_alloc_auto
  wp_pures
  wp_apply (Meta.wp_alloc_pos mv) as %m_ptr ⟨m, %Hmpos⟩
  (try wp_auto)
  dsimp only
  have hhwm2 : hwm + 2 ≤ 2 ^ 18 := by omega
  have hmZ : sint.Z ((mv.pgid' + W64 1 + W64 1) * W64 4096) = ((hwm + 2) * 4096 : Nat) := by
    have h1 : (mv.pgid' + W64 1 + W64 1).toNat = hwm + 2 := by
      simp only [BitVec.toNat_add]; rw [hpg]; show ((hwm + 1) % 2 ^ 64 + 1) % 2 ^ 64 = _; omega
    have h2 : ((mv.pgid' + W64 1 + W64 1) * W64 4096).toNat = (hwm + 2) * 4096 := by
      rw [BitVec.toNat_mul, h1]; show (hwm + 2) * 4096 % 2 ^ 64 = _; omega
    show BitVec.toInt _ = _
    rw [BitVec.toInt_eq_toNat_cond, h2]; split <;> omega
  have hlenZ : sint.Z (W64 (len : Int)) = len := by
    have : len ≤ 2 ^ 41 := Hstp.2.2.2
    show BitVec.toInt _ = _
    rw [BitVec.toInt_eq_toNat_cond]; simp only [BitVec.toNat_ofInt]; split <;> omega
  simp only [mapLen, hlenZ, hmZ]
  generalize hminsz : (mv.pgid' + W64 1 + W64 1) * W64 4096 = minsz at hmZ ⊢
  -- remap if the next high water mark passes the mapping
  wp_join (Q := fun bv => iprop((⌜bv = executeVal⌝ ∗ ∃ (base' : Loc) (len' : Nat) (γm' : GName) (m' : OsMeta),
      writerSt (GF := GF) γ db f fd p mp false hwm (some (base', len', γm')) m' ∗
      ⌜m'.size = m.size ∧ m'.ok = true ∧ (hwm + 2) * 4096 ≤ len'⌝ ∗
      dbOwner (GF := GF) γ mv.txid'.toNat hwm ∗
      db_ptr ↦ db ∗ minsz_ptr ↦ minsz ∗ «$res0_ptr» ↦ GoInterface.nil ∗
      v_ptr ↦ v ∗ pg_ptr ↦ mv.pgid' ∗ m_ptr ↦ nextMeta mv) ∨
    (∃ e : GoInterface, ⌜bv = returnVal #() ∧ e ≠ interface.nil⌝ ∗ db_ptr ↦ db ∗
      «$res0_ptr» ↦ e ∗ commitErr (GF := GF) γ db f fd p mv.txid'.toNat hwm)))
    with [-HΦ]
  · -- remap
    have hsz40 : m.size ≤ 2 ^ 40 := by have := Hstp.2.1; have := Hstp.2.2.2; omega
    wp_apply wp_mmap γ db f fd p minsz mp false hwm (some (base, len, γm)) m rfl (by omega)
        (by omega) hsz40 $$ [Hcur Hmap Hout Hflds Hfsz Hdsz Hf Hfd Hm Hmx Htail Htok Hwc]
      as %err ⟨%st', %m', Hcur, Hmap, Hout, Hflds, Hw, %Hm', Hres⟩
    · iframe #
      unfold writerFile mmapPre
      dsimp only
      iframe
      ipureintro
      exact ⟨⟨Hwf.1, Hwf.2.1, Hwf.2.2.1, Hwf.2.2.2.1, fun _ => ⟨hmx, hclean, rfl, hfd⟩⟩, Hstp⟩
    icases Hres with (⟨%Herr, %base', %len', %γm', %Hst', Htok, #Hinv', Hwc⟩ | ⟨%Herr, Hx⟩)
    · subst Herr
      obtain ⟨rfl, Hmaps', Hsz', Hmin', Hb', Hl41⟩ := Hst'
      (try wp_auto)
      ileft
      isplitr
      · ipureintro; rfl
      iexists base', len', γm', m'
      iframe
      unfold writerSt
      dsimp only
      iframe; iframe #
      ipureintro
      refine ⟨⟨Hmaps', by omega, Hb', Hl41⟩, Hm'.1, by rw [Hm'.2]; exact Hmok, by omega⟩
    · obtain ⟨Herr, rfl⟩ := Herr
      cases err with
      | nil => exact absurd rfl Herr
      | ok ie =>
      (try wp_auto)
      iright
      iexists (GoInterface.ok ie)
      iframe
      isplitr
      · ipureintro; exact ⟨rfl, Herr⟩
      unfold commitErr writerStF
      iframe
      dsimp only
      iexists m'
      iunfold writerFile at Hw
      icases Hw with ⟨%mxc1, %tail1, %fsz1, Hfsz, Hdsz, Hf, Hfd, Hm, Hmx, Htail, %Hw1⟩
      isplitl [Hfsz Hdsz Hf Hfd Hm Hmx Htail Hx]
      · isplitl [Hfsz Hdsz Hf Hfd Hm Hmx Htail]
        · unfold writerFile; iexists mxc1, tail1, fsz1; iframe; ipureintro
          exact ⟨Hw1.1, Hw1.2.1, Hw1.2.2.1, Hw1.2.2.2.1, fun h => by cases h⟩
        · iexact Hx
      ileft; ipureintro; rfl
  · -- no remap
    ileft
    isplitr
    · ipureintro; trivial
    iexists base, len, γm, m
    unfold writerSt writerFile
    dsimp only
    iframe; iframe #
    isplitr
    · ipureintro; exact ⟨⟨Hwf.1, Hwf.2.1, Hwf.2.2.1, Hwf.2.2.2.1, fun _ => ⟨hmx, hclean, rfl, hfd⟩⟩, Hstp⟩
    · ipureintro; exact ⟨rfl, Hmok, by omega⟩
  iintro (⟨%Hbv, %base, %len, %γm, %m', Hws, %Hm', Hown, db, minsz, «$res0», v, pg, m⟩ |
    ⟨%e, %Hbv, db, «$res0», Herr⟩)
  rotate_left
  · obtain ⟨rfl, He⟩ := Hbv
    (try wp_auto)
    iapply HΦ
    iright
    isplitr
    · ipureintro; exact He
    iunfold commitErr at Herr
    iexact Herr
  subst Hbv
  iunfold writerSt at Hws
  icases Hws with ⟨Hcur, Hmap, Hout, Hflds, Hw, Hcls, %Hstp, Htok, #Hinv, Hwc⟩
  iunfold writerFile at Hw
  icases Hw with ⟨%mxc, %tail, %fsz, Hfsz, Hdsz, Hf, Hfd, Hm, Hmx, Htail, %Hwf⟩
  obtain ⟨hmx, hclean, rfl, hfd⟩ := Hwf.2.2.2.2 rfl
  obtain ⟨Hmaps, Hsz, Hbase, Hl41⟩ := Hstp
  obtain ⟨Hsize, Hok', Hlen⟩ := Hm'
  have hsZ : sint.Z (W64 (m'.size : Int)) = m'.size := by
    show BitVec.toInt _ = _
    rw [BitVec.toInt_eq_toNat_cond]; simp only [BitVec.toNat_ofInt]; split <;> omega
  have hlen64 : (W64 (len : Int)).toNat = len := by simp only [BitVec.toNat_ofInt]; omega
  have hlenI : 0 ≤ (W64 (len : Int)).toInt := by
    rw [BitVec.toInt_eq_toNat_cond, hlen64]; split <;> omega
  dsimp only [mapLen]
  (try wp_auto)
  simp only [hsZ, hmZ]
  -- grow: Truncate and Sync
  wp_join (Q := fun bv => iprop((⌜bv = executeVal⌝ ∗ ∃ (m2 : OsMeta) (tail2 : List (w8 × Bool)),
      ⌜m2.maps = {[base := len]} ∧ m2.size ≤ len ∧ (hwm + 2) * 4096 ≤ m2.size ∧ m2.ok = true ∧
        tail2.length = m2.size - 4096 * hwm⌝ ∗
      osMeta (GF := GF) p (DFrac.own 1) (some m2) ∗ db.[DB, go!"filesz"] ↦ W64 m2.size ∗
      osBytes (GF := GF) p (4096 * hwm) (DFrac.own 1) tail2 ∗ writerCells (GF := GF) base hwm len ∗
      os.ownFile (GF := GF) f fd p (DFrac.own (1 : Qp).half) ∗
      osFd (GF := GF) fd (DFrac.own (1 : Qp).half) ⟨p, true, true⟩ ∗
      db.[DB, go!"datasz"] ↦ W64 len ∗ db_ptr ↦ db ∗ «$res0_ptr» ↦ GoInterface.nil ∗
      v_ptr ↦ v ∗ pg_ptr ↦ mv.pgid' ∗ m_ptr ↦ nextMeta mv ∗
      dbOwner (GF := GF) γ mv.txid'.toNat hwm ∗ ghostVar γ.cur (1 : Qp).half.half (mp, false, hwm) ∗
      ghostVar γ.map (1 : Qp).half (some (base, len, γm)) ∗ ghostVar γ.out (1 : Qp).half.half false ∗
      mapFields (GF := GF) db (DFrac.own (1 : Qp).half) (some (base, len, γm)) ∗
      ghostVar γ.cls (1 : Qp).half false ∗ ghostVar γm (1 : Qp).half () ∗
      osBytes (GF := GF) p 0 (DFrac.own (1 : Qp).half) mxc) ∨
    (∃ e : GoInterface, ⌜bv = returnVal #() ∧ e ≠ interface.nil⌝ ∗ db_ptr ↦ db ∗
      «$res0_ptr» ↦ e ∗ commitErr (GF := GF) γ db f fd p mv.txid'.toNat hwm)))
    with [-HΦ]
  · (try wp_auto)
    have hsz' : m'.size < (hwm + 2) * 4096 := by exact_mod_cast Hif
    icases (writerCells_top base hwm len).1 $$ Hwc with ⟨Hwc4, Htop⟩
    iunfold cellsAny at Htop
    icases Htop with ⟨%vf, Htop⟩
    rw [show len - 4096 * hwm = (m'.size - 4096 * hwm) + (len - m'.size) by omega]
    icases (cellsR_append _ _ _ _ _).1 $$ Htop with ⟨Hlow, Hhigh⟩
    rw [show 4096 * hwm + (m'.size - 4096 * hwm) = m'.size by omega]
    ihave Hmc := (mcellsAny_single (GF := GF) base len m'.size len Hsz (Nat.le_refl _)).2 $$ [Hhigh]
    · unfold cellsAny; iexists vf; iexact Hhigh
    rw [← Hmaps]
    wp_apply wp_Truncate f fd p _ (W64 (len : Int)) _ ⟨p, true, true⟩ m' len hfd rfl hlenI
        (by rw [hlen64]; exact Hsz) (fun b l h => by rw [Hmaps] at h; simp at h; omega)
        $$ [Hf Hfd Hm Hmc] as %err ⟨Hf, Hfd, Hres⟩
    · iframe #
      iframe
    simp only [hlen64]
    have h4 := Hwf.2.1
    have htl := Hwf.2.2.2.1
    have hmx8 := Hwf.2.2.1
    have h2 := Hwf.1
    icases Hres with (⟨%Herr, Hg⟩ | ⟨%Herr, (Hg | ⟨Hm, Hmc⟩)⟩)
    · subst Herr
      ihave Hx := grown_writer p base m' len hwm tail vf Hmaps Hsz h4 htl $$ [Hg Htail Hlow]
      · iframe
      icases Hx with ⟨%tail2, %Htl2, Hm, Htail, Htop⟩
      ihave Hwc := (writerCells_top base hwm len).2 $$ [Hwc4 Htop]
      · iframe
      (try wp_auto)
      ihave Hnil := (osBytes_nil (GF := GF) p 0 (DFrac.own 1)).2 $$ []
      · iempintro
      wp_apply wp_Sync f fd p _ _ ⟨p, true, true⟩ (m'.grown len) 0 [] $$ [Hf Hfd Hm Hnil]
        as %err2 ⟨Hf, Hfd, Hres2⟩
      · iframe; iframe #
      icases Hres2 with (⟨%Herr2, Hm, -⟩ | ⟨%Herr2, Hm, -⟩)
      · subst Herr2
        (try wp_auto)
        ileft
        isplitr
        · ipureintro; trivial
        iexists (m'.grown len).synced, tail2
        iframe
        ipureintro
        exact ⟨rfl, Nat.le_refl _, Hlen, Hok', Htl2⟩
      · cases err2 with
        | nil => exact absurd rfl Herr2
        | ok ie =>
        (try wp_auto)
        iright
        iexists GoInterface.ok ie
        iframe
        isplitr
        · ipureintro; exact ⟨rfl, Herr2⟩
        iapply commitErr_of γ db f fd p mp hwm base len γm { m'.grown len with ok := false } mxc tail2
          m'.size _ _ ⟨Hmaps, Nat.le_refl _, Hbase, Hl41, h2, by simp [OsMeta.grown]; omega, hmx8,
            by simp [OsMeta.grown]; exact Htl2⟩
        iframe; iframe #
    · cases err with
      | nil => exact absurd rfl Herr
      | ok ie =>
      ihave Hx := grown_writer p base m' len hwm tail vf Hmaps Hsz h4 htl $$ [Hg Htail Hlow]
      · iframe
      icases Hx with ⟨%tail2, %Htl2, Hm, Htail, Htop⟩
      ihave Hwc := (writerCells_top base hwm len).2 $$ [Hwc4 Htop]
      · iframe
      (try wp_auto)
      iright
      iexists GoInterface.ok ie
      iframe
      isplitr
      · ipureintro; exact ⟨rfl, Herr⟩
      iapply commitErr_of γ db f fd p mp hwm base len γm (m'.grown len) mxc tail2
        m'.size _ _ ⟨Hmaps, Nat.le_refl _, Hbase, Hl41, h2, by simp [OsMeta.grown]; omega, hmx8,
          by simp [OsMeta.grown]; exact Htl2⟩
      iframe; iframe #
    · cases err with
      | nil => exact absurd rfl Herr
      | ok ie =>
      ihave Htop := cells_back base m' len hwm vf Hmaps Hsz h4 $$ [Hmc Hlow]
      · iframe
      ihave Hwc := (writerCells_top base hwm len).2 $$ [Hwc4 Htop]
      · iframe
      (try wp_auto)
      iright
      iexists GoInterface.ok ie
      iframe
      isplitr
      · ipureintro; exact ⟨rfl, Herr⟩
      iapply commitErr_of γ db f fd p mp hwm base len γm (ftMeta m' len) mxc tail
        m'.size _ _ ⟨Hmaps, Hsz, Hbase, Hl41, h2, h4, hmx8, htl⟩
      iframe; iframe #
  · ileft
    isplitr
    · ipureintro; trivial
    iexists m', tail
    iframe
    ipureintro; exact ⟨Hmaps, Hsz, by omega, Hok', Hwf.2.2.2.1⟩
  iintro (⟨%Hbv, %m2, %tail2, %Hm2, Hm, Hfsz, Htail, Hwc, Hf, Hfd, Hdsz, db, «$res0», v, pg, m, Hown, Hcur, Hmap,
    Hout, Hflds, Hcls, Htok, Hmx⟩ | ⟨%e, %Hbv, db, «$res0», Herr⟩)
  rotate_left
  · obtain ⟨rfl, He⟩ := Hbv
    (try wp_auto)
    iapply HΦ
    iright
    isplitr
    · ipureintro; exact He
    iunfold commitErr at Herr
    iexact Herr
  subst Hbv
  clear Hsize Hok' Hlen Hsz Hmaps hsZ
  obtain ⟨Hmaps, Hsz, Hgrow, Hok2, Htl2⟩ := Hm2
  (try wp_auto)
  -- the data page
  wp_apply (wp_slice_make2 (V := w8) (W64 4096)) as %buf ⟨Hbuf, -⟩
  · ipureintro; decide
  (try wp_auto)
  ihave %Hblen := ownSlice_len $$ Hbuf
  ihave %Hpos := ownSlice_ptr_pos buf _ _ (List.ne_nil_of_length_pos (by rw [List.length_replicate]; decide)) $$ Hbuf
  have hbl : sint.Z buf.len = 4096 := by
    have h1 := Hblen.1; have h2 := Hblen.2; simp only [List.length_replicate] at h1
    have : sint.nat buf.len = (sint.Z buf.len).toNat := rfl
    omega
  wp_apply wp_pageAt
  · ipureintro; rw [hbl]; exact ⟨Hpos, by decide, by decide⟩
  rw [show sint.Z (W64 0) = 0 from rfl, loc_add_0]
  icases ownSlice_bytes_acc go.uint8 (.scalar _ _ .isPlainScalar_uint8) buf _ _ Hpos $$ Hbuf
    with ⟨Hb, Hclose⟩
  simp only [flatMap_encode_w8, show zero_val w8 = (0 : w8) from rfl]
  rw [zeroPage_val]
  icases (valPage_view _ _ _ _ _ Hpos).1 $$ Hb with ⟨Hh, Hv, Hr⟩
  (try wp_auto)
  rw [ite_eq_left (by rw [hbl]; decide), show sliceIndexRef w8 (sint.Z (W64 16)) buf = buf.ptr +ₗ 16 from
    sliceIndexRef_byte_W64 buf 16 Hpos (by decide)]
  (try wp_auto)
  ihave Hh : buf.ptr ↦ dataHdr mv.pgid' $$ [Hh]
  · simp only [dataHdr, pageHdr]; iexact Hh
  ihave Hb := (valPage_view buf.ptr _ _ v _ Hpos).2 $$ [Hh Hv Hr]
  · iframe
  ihave Hbuf := Hclose $$ %(dataPage mv.pgid' v) [] [Hb]
  · ipureintro; rw [dataPage_length, ← zeroPage_val, List.length_replicate]
  · simp only [dataPage]; iexact Hb
  -- its write, at the high water mark (inside the file)
  have hoff : (mv.pgid' * W64 4096).toNat = 4096 * hwm := by
    rw [BitVec.toNat_mul, hpg]; show hwm * 4096 % 2 ^ 64 = _; omega
  have hoffI : 0 ≤ (mv.pgid' * W64 4096).toInt := by
    rw [BitVec.toInt_eq_toNat_cond, hoff]; split <;> omega
  have hdl := dataPage_length mv.pgid' v
  have hin : 4096 * hwm + 4096 ≤ m2.size := by omega
  icases (osBytes_app p _ _ (tail2.take 4096) (tail2.drop 4096)).1 $$ [Htail] with ⟨Hpg, Hrest⟩
  · rw [List.take_append_drop]; iexact Htail
  have htk : (tail2.take 4096).length = 4096 := by rw [List.length_take]; omega
  rw [htk]
  icases (writerCells_top base hwm len).1 $$ Hwc with ⟨Hwc4, Htop⟩
  rw [show len - 4096 * hwm = 4096 + (len - 4096 * hwm - 4096) by omega]
  icases cellsAny_split _ _ _ _ $$ Htop with ⟨Hpc, Htop⟩
  ihave Hpc := (mcellsAny_single (GF := GF) base len (4096 * hwm) (4096 * hwm + 4096) (by omega)
    (by omega)).2 $$ [Hpc]
  · rw [show 4096 * hwm + 4096 - 4096 * hwm = 4096 by omega]; iexact Hpc
  rw [← Hmaps]
  wp_apply wp_WriteAt f fd p (DFrac.own (1 : Qp).half) buf (dataPage mv.pgid' v) (DFrac.own 1)
      (mv.pgid' * W64 4096) (DFrac.own (1 : Qp).half)
      ⟨p, true, true⟩ 1 m2 (tail2.take 4096) rfl hoffI (by omega) (by omega)
      (by rw [hoff, htk, hdl]; omega) (fun _ => rfl) $$ [Hf Hbuf Hfd Hm Hpg Hpc]
    as %n %err ⟨Hf, Hbuf, Hfd, %j, %ys, %h, %Hres, Hm, Hpg, Hpc⟩
  · rw [hoff, hdl, Nat.min_eq_left (by omega : 4096 * hwm ≤ m2.size)]
    iframe Hf Hbuf Hfd Hm Hpg Hpc; iframe #
  rw [hoff, dataPage_length, Nat.min_eq_left (by omega : 4096 * hwm ≤ m2.size)] at *
  have hj : j ≤ 4096 := Hres.1
  have hys : ys.length = 4096 := by
    have h1 := congrArg List.length Hres.2.1
    simp only [List.length_map, pwBytes_length] at h1
    rw [pwSize_inside m2.size (4096 * hwm) j (by omega), dataPage_length] at h1; omega
  rw [pwSize_inside m2.size (4096 * hwm) j (by omega)]
  have hmp3 : ({ m2 with size := m2.size, hi := h } : OsMeta).maps = {[base := len]} := Hmaps
  icases (mcellsAny_single (GF := GF) base len (4096 * hwm) (4096 * hwm + 4096) (by omega)
    (by omega)).1 $$ [Hpc] with Hpc
  · rw [Hmaps]; iexact Hpc
  rw [show 4096 * hwm + 4096 - 4096 * hwm = 4096 by omega]
  obtain ⟨-, hys', hh, ⟨rfl, rfl, rfl⟩ | ⟨rfl, hne⟩⟩ := Hres
  rotate_left
  · cases err with
    | nil => exact absurd rfl hne
    | ok ie =>
    (try wp_auto)
    iapply HΦ
    iright
    isplitr
    · ipureintro; exact hne
    ihave Herr := dataErr γ db f fd p mp hwm base len γm { m2 with size := m2.size, hi := h } mxc ys
      (tail2.drop 4096) m2.size _ _ ⟨Hmaps, Hsz, Hbase, Hl41, Hwf.1, hin, Hwf.2.2.1, hys,
        by simp only [List.length_drop]; omega⟩
      $$ [Hown Hcur Hmap Hout Hflds Hcls Htok Hwc4 Hpc Htop Hfsz Hdsz Hf Hfd Hm Hmx Hpg Hrest]
    · iframe Hown Hcur Hmap Hout Hflds Hcls Htok Hwc4 Hpc Htop Hfsz Hdsz Hf Hfd Hm Hmx Hpg Hrest
      iframe #
    iunfold commitErr at Herr
    iexact Herr
  (try wp_auto)
  wp_apply wp_Fd f fd p _ $$ [Hf] as Hf
  · iexact Hf
  (try wp_auto)
  wp_apply wp_Fdatasync fd (DFrac.own (1 : Qp).half) ⟨p, true, true⟩ { m2 with size := m2.size, hi := h }
      (4096 * hwm) ys $$ [Hfd Hm Hpg] as %e ⟨Hfd, Hs⟩
  · iframe Hfd Hm Hpg; iframe #
  icases Hs with (⟨%He, Hm, Hpg⟩ | ⟨%He, Hm, Hpg⟩)
  rotate_left
  · unfold errnoErr; rw [if_neg He.1]
    (try wp_auto)
    iapply HΦ
    iright
    isplitr
    · ipureintro; simp
    ihave Herr := dataErr γ db f fd p mp hwm base len γm { m2 with size := m2.size, hi := h, ok := false }
      mxc ys (tail2.drop 4096) m2.size _ _ ⟨Hmaps, Hsz, Hbase, Hl41, Hwf.1, hin, Hwf.2.2.1, hys,
        by simp only [List.length_drop]; omega⟩
      $$ [Hown Hcur Hmap Hout Hflds Hcls Htok Hwc4 Hpc Htop Hfsz Hdsz Hf Hfd Hm Hmx Hpg Hrest]
    · iframe Hown Hcur Hmap Hout Hflds Hcls Htok Hwc4 Hpc Htop Hfsz Hdsz Hf Hfd Hm Hmx Hpg Hrest
      iframe #
    iunfold commitErr at Herr
    iexact Herr
  subst He
  unfold errnoErr; rw [if_pos rfl]
  (try wp_auto)
  -- the data page is clean, and its cells hold it
  have hysB : ys.map Prod.fst = dataPage mv.pgid' v := by
    rw [hys']
    have := pwBytes_inside m2.size (4096 * hwm) (dataPage mv.pgid' v) (List.take 4096 tail2)
      (by rw [dataPage_length]; omega) (by omega)
    rwa [dataPage_length] at this
  have hsyn : syncedBytes { m2 with size := m2.size, hi := h } ys =
      (dataPage mv.pgid' v).map (·, true) := by
    unfold syncedBytes
    rw [ite_eq_left (show ({ m2 with size := m2.size, hi := h } : OsMeta).ok = true from Hok2), ← hysB,
      List.map_map]
    rfl
  rw [hsyn]
  generalize hm4 : ({ m2 with size := m2.size, hi := h } : OsMeta).synced = m4
  have hm4m : m4.maps = {[base := len]} := by rw [← hm4]; exact Hmaps
  have hm4s : m4.size = m2.size := by rw [← hm4]; rfl
  have hm4o : m4.ok = true := by rw [← hm4]; exact Hok2
  have hb4 : m4.maps !! base = some len := by rw [hm4m]; exact GMap.lookup_insert _ _ _
  iunfold cellsAny at Hpc
  icases Hpc with ⟨%vf, Hpc⟩
  iapply cellsR_agree _ rfl p _ m4 base len hb4 (DFrac.own 1) (by simp) _
    ((dataPage mv.pgid' v).map (·, true)) (4096 * hwm) vf (by simp only [List.length_map, dataPage_length]; omega)
    $$ Hos Hm Hpg [Hpc]
  · rw [List.length_map, dataPage_length]; iexact Hpc
  iintro Hm Hpg Hpc
  rw [show ((dataPage mv.pgid' v).map (·, true)).map Prod.fst = dataPage mv.pgid' v by
    rw [List.map_map]; exact List.map_id _]
  -- the meta page
  wp_apply (wp_slice_make2 (V := w8) (W64 4096)) as %mbuf ⟨Hmb, -⟩
  · ipureintro; decide
  (try wp_auto)
  ihave %Hmblen := ownSlice_len $$ Hmb
  ihave %Hmbpos := ownSlice_ptr_pos mbuf _ _
    (List.ne_nil_of_length_pos (by rw [List.length_replicate]; decide)) $$ Hmb
  have hmbl : sint.Z mbuf.len = 4096 := by
    have h1 := Hmblen.1; have h2 := Hmblen.2; simp only [List.length_replicate] at h1
    have : sint.nat mbuf.len = (sint.Z mbuf.len).toNat := rfl
    omega
  wp_apply wp_pageAt
  · ipureintro; rw [hmbl]; exact ⟨Hmbpos, by decide, by decide⟩
  rw [show sint.Z (W64 0) = 0 from rfl, loc_add_0]
  icases ownSlice_bytes_acc go.uint8 (.scalar _ _ .isPlainScalar_uint8) mbuf _ _ Hmbpos $$ Hmb
    with ⟨Hb, Hmclose⟩
  simp only [flatMap_encode_w8, show zero_val w8 = (0 : w8) from rfl]
  icases (zeroPage_meta_view _ _ Hmbpos).1 $$ [Hb] with ⟨Hh, Hmm, Hr⟩
  · iexact Hb
  (try wp_auto)
  wp_apply wp_write m_ptr mbuf.ptr (nextMeta mv) _ _ $$ [m Hh Hmm] as ⟨m, Hh, Hmm⟩
  · iframe m Hh Hmm; ipureintro; exact ⟨Hmpos, Hmbpos⟩
  (try wp_auto)
  -- `metalock`: the handle is not failed (the writer's `cur`)
  ihave #Hpkg2 := Hpkg
  iunfold pkgFacts at Hpkg2
  icases Hpkg2 with ⟨#Hsync, -⟩
  wp_apply sync.Mutex.wp_Lock db.[DB, go!"metalock"] (metaR (GF := GF) γ db p) $$ [$Hmeta $Hsync]
    as ⟨Hlocked, HR⟩
  iunfold metaR at HR
  icases HR with ⟨%b, %mpx, %mx, %hwmx, %mxc', %T, Hfl, Hcm, Hmb, %Hmx', Hauth, Hout2, Hrest⟩
  icombine Hcur Hcm gives % ⟨_, Hceq⟩
  cases Hceq
  dsimp only
  icases Hrest with ⟨Hfail, %Hmeta', Hlast, Hown2, %B0, #HB0, #Htx0, %HT0⟩
  obtain ⟨rfl, -, -, HTn⟩ := Hmeta'
  icases Hmb with (⟨Hmx2, Hcls2⟩ | Hcls2)
  rotate_left
  · icombine Hcls Hcls2 gives % ⟨_, Hbad⟩; cases Hbad
  (try wp_auto)
  -- the meta buffer holds the meta page
  ihave Hh : mbuf.ptr ↦ metaHdrOf mv $$ [Hh]
  · simp only [metaHdrOf, pageHdr, nextMeta]; iexact Hh
  ihave Hmm : (mbuf.ptr +ₗ 16) ↦ commitOf mv $$ [Hmm]
  · simp only [commitOf, nextMeta]; iexact Hmm
  ihave Hb := (pageMeta_view mbuf.ptr _ _ _ _ Hmbpos).2 $$ [Hh Hmm Hr]
  · iframe Hh Hmm Hr
  ihave Hmb := Hmclose $$ %(metaPageOf mv) [] [Hb]
  · ipureintro; rw [metaPageOf_length, List.length_replicate]
  · simp only [metaPageOf]; iexact Hb
  -- the meta cells out of the invariant, the meta pages' bytes whole
  imod metas_out γ p base len γm mx hwm $$ [Hinv Htok Hcur Hout Hout2]
    with ⟨Htok, Hcur, Hout, Hout2, Hc0, Hc1⟩
  · iframe Htok Hcur Hout Hout2; iframe #
  have hmxl : mxc.length = 8192 := Hwf.2.2.1
  have hmxl' : mxc'.length = 8192 := Hmx'.1
  ihave Hmxw := osBytes_join p mxc mxc' 0 (by rw [hmxl, hmxl']) $$ [Hmx Hmx2]
  · iframe Hmx Hmx2
  have hml : mx.length = 8192 := by rw [← hmx, List.length_map, hmxl]
  generalize hi : ((mv.txid' + W64 1) % W64 2).toNat = i
  have hi2 : i < 2 := by rw [← hi, BitVec.toNat_umod]; exact Nat.mod_lt _ (by decide)
  have hoffm : ((mv.txid' + W64 1) % W64 2 * W64 4096).toNat = 4096 * i := by
    rw [BitVec.toNat_mul, hi]; show i * 4096 % 2 ^ 64 = _; omega
  have hoffmI : 0 ≤ ((mv.txid' + W64 1) % W64 2 * W64 4096).toInt := by
    rw [BitVec.toInt_eq_toNat_cond, hoffm]; split <;> omega
  -- meta page `i`'s cells
  ihave Hc0 := cellsB_any base 16 _ $$ Hc0
  ihave Hc1 := cellsB_any base 4112 _ $$ Hc1
  have hl64 : ∀ k, ((mx.drop k).take 64).length = 64 ∨ 8192 < k + 64 := by
    intro k; by_cases hk : k + 64 ≤ 8192
    · left; simp only [List.length_take, List.length_drop, hml]; omega
    · right; omega
  rw [show ((mx.drop 16).take 64).length = 64 by simp only [List.length_take, List.length_drop, hml]; rfl,
    show ((mx.drop 4112).take 64).length = 64 by simp only [List.length_take, List.length_drop, hml]; rfl]
  icases (hdrTails base).1 $$ Hwc4 with ⟨T0, T1⟩
  icases (pick_page (fun k => iprop(hdrTail (GF := GF) base k ∗ cellsAny (GF := GF) base (4096 * k + 16) 64))
    i hi2).1 $$ [T0 T1 Hc0 Hc1] with ⟨⟨Ti, Hci⟩, Hother⟩
  · iframe T0 T1 Hc0 Hc1
  ihave Hpi := metaPage_cells base i $$ [Ti Hci]
  · iframe Ti Hci
  -- its write
  have hm4ge : 16384 ≤ m4.size := by rw [hm4s]; omega
  icases (osBytes_window p _ mxc (4096 * i) 4096 (by omega)).1 $$ Hmxw with ⟨W0, Wi, W2⟩
  ihave Hpi := (mcellsAny_single (GF := GF) base len (4096 * i) (4096 * i + 4096) (by omega)
    (by omega)).2 $$ [Hpi]
  · rw [show 4096 * i + 4096 - 4096 * i = 4096 by omega]; iexact Hpi
  rw [← hm4m]
  have hwl : ((mxc.drop (4096 * i)).take 4096).length = 4096 := by
    simp only [List.length_take, List.length_drop, hmxl]; omega
  wp_apply wp_WriteAt f fd p (DFrac.own (1 : Qp).half) mbuf (metaPageOf mv) (DFrac.own 1)
      ((mv.txid' + W64 1) % W64 2 * W64 4096) (DFrac.own (1 : Qp).half)
      ⟨p, true, true⟩ 1 m4 ((mxc.drop (4096 * i)).take 4096) rfl hoffmI
      (by rw [metaPageOf_length]; omega) (by rw [metaPageOf_length]; omega)
      (by rw [hoffm, metaPageOf_length, hwl]; omega) (fun _ => rfl)
      $$ [Hf Hmb Hfd Hm Wi Hpi]
    as %n2 %err2 ⟨Hf, Hmb, Hfd, %j2, %ys2, %h2, %Hres2, Hm, Wi, Hpi⟩
  · rw [hoffm, metaPageOf_length, Nat.min_eq_left (by omega : 4096 * i ≤ m4.size)]
    iframe Hf Hmb Hfd Hm Wi Hpi; iframe #
  rw [hoffm, metaPageOf_length, Nat.min_eq_left (by omega : 4096 * i ≤ m4.size)] at *
  have hj2 : j2 ≤ 4096 := Hres2.1
  have hys2 : ys2.length = 4096 := by
    have h1 := congrArg List.length Hres2.2.1
    simp only [List.length_map, pwBytes_length] at h1
    rw [pwSize_inside m4.size (4096 * i) j2 (by omega), metaPageOf_length] at h1; omega
  rw [pwSize_inside m4.size (4096 * i) j2 (by omega)]
  -- the meta pages' bytes whole again, and both metas' cells holding them
  ihave Hmxw := window_join p _ mxc ys2 (4096 * i) 4096 (by omega) hys2 $$ [W0 Wi W2]
  · iframe W0 Wi W2
  generalize hX : mxc.take (4096 * i) ++ ys2 ++ (mxc.drop (4096 * i)).drop 4096 = X
  have hXl : X.length = 8192 := by rw [← hX, window_join_length _ _ _ _ (by omega) hys2, hmxl]
  sorry

end proof

end bboltfs
end EtcdGrove
end Perennial
