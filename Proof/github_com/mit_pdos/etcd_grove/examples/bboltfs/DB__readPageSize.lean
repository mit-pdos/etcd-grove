/- Lean-first (no Rocq counterpart). The proof of `db.readPageSize()`: each iteration reads page `i` (a window of the client's bytes) with `ReadAt`, views the buffer as a page header and a meta (`pageView`), and validates the meta. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__readPageSize
public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.pageAt
public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.Page__meta
public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.Meta__validate
public import Spec.os.File__ReadAt

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.bboltfs

theorem addr_le_of_len {a M : Int} {l k n : Nat} (h : a + l ≤ M) (hl : l = k) (hk : n ≤ k) :
    a + n ≤ M := by
  subst hl; omega

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.bboltfs.Assumptions]

theorem DB.readPageSize.wp_proof
    (wp_pageAt : pageAt.spec (GF := GF) (hG := hG))
    (wp_meta : Page.«meta».spec (GF := GF) (hG := hG))
    (wp_validate : Meta.validate.spec (GF := GF) (hG := hG))
    (wp_ReadAt : os.File.ReadAt.spec (GF := GF) (hG := hG)) :
    DB.readPageSize.spec (GF := GF) (hG := hG) := by
  intro db f dqd fd name dqf dq dqm dqb d m xs hrd hxs hsz
  wp_start as ⟨#Hinv, Hfile, Hf, Hfd, Hm, Hb⟩
  wp_auto
  wp_apply (wp_slice_make2 (V := w8) (W64 4096)) as %buf ⟨Hbuf, -⟩
  · ipureintro; decide
  (try wp_auto)
  ihave HI : (∃ (j : w64), "i" ∷ i_ptr ↦ j ∗
      "Hbuf" ∷ (∃ vs : List w8, buf ↦* vs ∗ ⌜vs.length = 4096⌝) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ 2 ∧
        ∀ i < sint.nat j, ¬ metaValid (fileMeta (xs.map Prod.fst) i)⌝ : IProp GF) $$ [i Hbuf]
  · iexists W64 0; iframe; isplitl
    · iexists _; iframe; ipureintro; rw [List.length_replicate]
    · ipureintro; refine ⟨by decide, by decide, ?_⟩; intro i hi; have h0 : sint.nat (W64 0) = 0 := rfl; omega
  wp_for HI
  wp_if_destruct
  · obtain ⟨Hj0, Hj2, Hjv⟩ := Hj
    rw [show sint.Z (W64 2) = 2 from rfl] at Hif
    icases Hbuf with ⟨%vs, Hbuf, %Hvs⟩
    ihave %Hbl := ownSlice_len $$ Hbuf
    have hw : 4096 * sint.nat j + 4096 ≤ xs.length := by
      show 4096 * (sint.Z j).toNat + 4096 ≤ xs.length; omega
    icases (osBytes_window d.path dqb xs (4096 * sint.nat j) 4096 hw).1 $$ Hb with ⟨Hb0, Hw, Hb2⟩
    (try wp_auto)
    have hoff : (j * W64 4096).toNat = 4096 * sint.nat j := by
      show (j * W64 4096).toNat = 4096 * (sint.Z j).toNat
      have : (j * W64 4096).toNat = 4096 * j.toNat := by word
      rw [this]; congr 1; word
    wp_apply wp_ReadAt f fd name dqf buf vs (j * W64 4096) dq dqm dqb d m
        ((xs.drop (4096 * sint.nat j)).take 4096) hrd (by word) (by omega)
        (by rw [hoff]; omega) (by simp; omega) $$ [Hinv Hf Hbuf Hfd Hm Hw]
      as %n %err ⟨Hf, Hfd, Hm, Hw, %vs', Hbuf, %Hres⟩
    · rw [hoff]; iframe; iframe #
    rw [hoff]
    ihave Hb := (osBytes_window d.path dqb xs (4096 * sint.nat j) 4096 hw).2 $$ [Hb0 Hw Hb2]
    · iframe
    have hlen : buf.len = W64 4096 := by
      have h1 : (sint.Z buf.len).toNat = 4096 := by rw [← Hvs]; exact Hbl.1.symm
      have h2 := Hbl.2
      have : sint.Z buf.len = 4096 := by omega
      word
    obtain ⟨hl', ⟨rfl, rfl, hvs'⟩ | ⟨rfl, hne⟩⟩ := Hres
    · have hl4 : vs'.length = 4096 := by omega
      ihave %Hpos := ownSlice_ptr_pos buf vs' _ (by intro h; rw [h] at hl4; simp at hl4) $$ Hbuf
      (try rw [Hvs])
      (try wp_auto)
      (try rw [hlen])
      (try wp_auto)
      wp_apply wp_pageAt
      · ipureintro; rw [hlen]; exact ⟨Hpos, by decide, by decide⟩
      rw [show sint.Z (W64 0) = 0 from rfl, loc_add_0]
      icases ownSlice_bytes_acc go.uint8 (.scalar _ _ .isPlainScalar_uint8) buf _ _ Hpos $$ Hbuf
        with ⟨Hbytes, Hclose⟩
      simp only [flatMap_encode_w8]
      ihave %Hbd := bytesPointsto_in_bounds _ _ _ (by intro h; rw [h] at hl4; simp at hl4) $$ Hbytes
      icases (pageView buf.ptr _ vs' (by omega) Hpos).1 $$ Hbytes with ⟨Hh, Hmt, Hrest⟩
      have hb16 : 0 < buf.ptr.addr ∧ buf.ptr.addr + 16 ≤ maxAddr := by
        exact ⟨Hpos, addr_le_of_len Hbd.2 hl4 (by decide)⟩
      wp_apply wp_meta
      · ipureintro; exact hb16
      have h16 : 0 < (buf.ptr +ₗ 16).addr := by simp only [Loc.add]; omega
      (try wp_auto)
      wp_apply wp_validate (buf.ptr +ₗ 16) (pageMeta vs') _ $$ [Hmt] as Hmt
      · iframe; ipureintro; exact h16
      have hfm : pageMeta vs' = fileMeta (xs.map Prod.fst) (sint.nat j) := by
        rw [hvs', List.map_take, List.map_drop]; exact fileMeta_window _ _ _ (by omega)
      wp_if_destruct
      · have hn : (buf.ptr +ₗ 16) ≠ null := by intro h; rw [h] at h16; simp [null] at h16
        icases typedPointsto_split _ _ _ $$ Hmt with Hmt
        simp only [TypedPointsto.typedPointstoDef]
        icases Hmt with ⟨Hmagic, Hversion, HpageSize, Hflags, Hroot, Hfreelist, Hpgid, Htxid, Hchecksum, -⟩
        (try wp_auto)
        wp_for_post
        iapply HΦ
        iframe
        ipureintro; intro _
        refine ⟨fun _ => ⟨sint.nat j, ?_, ?_, ?_⟩, fun h => by cases h⟩
        · show (sint.Z j).toNat < 2; omega
        · rw [← hfm]; exact Hif
        · rw [← hfm]; rfl
      · ihave Hbytes := (pageView buf.ptr _ vs' (by omega) Hpos).2 $$ [Hh Hmt Hrest]
        · iframe
        ihave Hbuf := Hclose $$ %vs' %rfl [Hbytes]
        · iexact Hbytes
        (try wp_auto)
        wp_for_post
        iframe
        iexists (j + W64 1)
        iframe
        isplitl
        · iexists vs'; iframe; ipureintro; exact hl4
        · ipureintro
          refine ⟨by word, by word, ?_⟩
          intro i hi
          have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by
            show (sint.Z (j + W64 1)).toNat = (sint.Z j).toNat + 1
            have : sint.Z (j + W64 1) = sint.Z j + 1 := by word
            omega
          rw [hj1] at hi
          rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
          · exact Hjv i hi
          · rw [← hfm]; exact Hif
    · cases err with
      | nil => exact absurd rfl hne
      | ok ie =>
      (try wp_auto)
      wp_for_post
      iapply HΦ
      iframe
      ipureintro; intro h; cases h
  · obtain ⟨Hj0, Hj2, Hjv⟩ := Hj
    rw [show sint.Z (W64 2) = 2 from rfl] at Hif
    (try wp_auto)
    iapply HΦ
    iframe
    ipureintro; intro _
    refine ⟨fun h => (nomatch h), fun _ i hi => Hjv i ?_⟩
    show i < (sint.Z j).toNat; omega
