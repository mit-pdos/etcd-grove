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
      writerSt (GF := GF) γ db f fd p mp' fl hwm st' m' ∗
      (⌜fl = false⌝ ∨ (⌜fl = true⌝ ∗ dbFailed (GF := GF) γ)))

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
  obtain ⟨hmx, hclean, rfl⟩ := Hwf.2.2.2.2 rfl
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
      exact ⟨⟨Hwf.1, Hwf.2.1, Hwf.2.2.1, Hwf.2.2.2.1, fun _ => ⟨hmx, hclean, rfl⟩⟩, Hstp⟩
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
      unfold commitErr writerSt
      iframe
      dsimp only
      iframe
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
    · ipureintro; exact ⟨⟨Hwf.1, Hwf.2.1, Hwf.2.2.1, Hwf.2.2.2.1, fun _ => ⟨hmx, hclean, rfl⟩⟩, Hstp⟩
    · ipureintro; exact ⟨rfl, Hmok, by omega⟩
  sorry

end proof

end bboltfs
end EtcdGrove
end Perennial
