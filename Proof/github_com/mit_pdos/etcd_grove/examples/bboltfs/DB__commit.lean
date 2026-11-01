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
      db_ptr ↦ db ∗ minsz_ptr ↦ minsz ∗ «$res0_ptr» ↦ GoInterface.nil) ∨
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
  iintro (⟨%Hbv, %base, %len, %γm, %m', Hws, %Hm', Hown, db, minsz, «$res0»⟩ |
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
  iintro (⟨%Hbv, %m2, %tail2, %Hm2, Hm, Hfsz, Htail, Hwc, Hf, Hfd, Hdsz, db, «$res0», Hown, Hcur, Hmap,
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
  -- TODO: the rest of `commit`, after the grow. The file is `m2` (size at least the next high
  -- water mark's end, `m2.ok`), the bytes from `hwm` on `tail2`, the mapping `(base, len, γm)`.
  -- 1. the data page: `make` (`wp_slice_make2`), the header and `v` through `pageHdr_view` and a
  --    `w64` byte view at offset 16; `WriteAt` at `4096 * hwm` over `tail2.take 4096` and the cells
  --    `[4096 * hwm, 4096 * hwm + 4096)` of `writerCells`' top (`mcellsAny_single`); `Fdatasync`
  --    (`m2.ok`: the page's bytes clean); `cellsR_agree` around the next step for its cells;
  --    `osBytes` discarded into `pageIs p hwm B` (a lemma like `ghostMapElem_persist` for
  --    `bytesG`). On an error: `commitErr_of`.
  -- 2. the meta page: `make`, `pageAt`, `Meta.write` (the meta `commitOf mv`, page id
  --    `txid % 2`); `metalock` (`metaR`, not failed: `fail_handle`-like ghost reasoning), the
  --    meta cells out of the invariant (`metas_out`), `WriteAt` over page `i` of the meta pages
  --    (both halves of `mxc`, `osBytes_join`, `osBytes_window`), `Fdatasync` (clean), on an error
  --    `failed := true` under `metalock` (`fail_cur_inv`, `metaR`'s `own` into its failed branch)
  --    and `commitErr` with `dbFailed`.
  -- 3. publish: `setPage mp i PB` (`metaPagesOk_commit`), `cur` (three parts), page `hwm`'s cells
  --    into the invariant, `metas_in`, `own` to `(t + 1, hwm + 1)`, `last` to `t + 1`, the
  --    transaction map at `t + 1` (`HTn`: no entry yet), `dbTx (t + 1) (some v)`; `rwR`.
  sorry

end proof

end bboltfs
end EtcdGrove
end Perennial
