/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/client/pkg/v3/fileutil/ZeroToEnd.lean`.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.ZeroToEnd
public import LinuxFs.Spec.os.File__Truncate

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions] [os.file.FieldAssumptions]

theorem OsMeta.announce_maps (m : OsMeta) (lo hi tg : Nat) : (m.announce lo hi tg).maps = m.maps := by
  simp [OsMeta.announce, OsMeta.touch]; split <;> (try split) <;> rfl

theorem OsMeta.announce_size (m : OsMeta) (lo hi tg : Nat) : (m.announce lo hi tg).size = m.size := by
  simp [OsMeta.announce, OsMeta.touch]; split <;> (try split) <;> rfl

/-- A truncate that shrank the file to `tg` landed: its `OsMeta`, of size `tg`, the same mappings,
the page cache known zero to the end of the page holding the old end. -/
theorem ftDone_shrunk (p : Ino) (m : OsMeta) (tg : Nat) :
    os.ftDone (GF := GF) p m tg ⊢ ∃ m1 : OsMeta,
      ⌜m1.size = tg ∧ m1.maps = m.maps ∧ pageEnd (max m.size tg) ≤ m1.cz⌝ ∗
      osMeta p (DFrac.own 1) m1 := by
  unfold os.ftDone
  iintro ⟨%zs, %hzs, Hm, -, -⟩
  iexists rsPost true m tg tg
  iframe Hm
  ipureintro
  refine ⟨rfl, ?_, os.rsPost_cz_true m tg tg⟩
  simp [rsPost, OsMeta.announce, OsMeta.touch]; split <;> (try split) <;> rfl

theorem go_etcd_io.etcd.client.pkg.v3.fileutil.ZeroToEnd.wp_proof
    (wp_Truncate : os.File.Truncate.spec (GF := GF) (hG := hG))
    (wp_Preallocate : go_etcd_io.etcd.client.pkg.v3.fileutil.Preallocate.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.client.pkg.v3.fileutil.ZeroToEnd.spec (GF := GF) (hG := hG) := by
  intro f fd name dqf dq d m o xs hfd hwr hmaps ho0 hole hsz hxs
  wp_start as ⟨#Hinv, #Herrs, Hf, Ho, Hfd, Hm, Hb⟩
  have hoN : (o.toNat : Int) = o.toInt := by
    have := BitVec.toInt_eq_toNat_cond o; split at this <;> omega
  have ho1 : o.toInt ≤ 0xffffffff000 := by omega
  wp_auto
  wp_apply os.File.Seek.wp_cur f fd name dqf o hfd ho0 ho1 $$ [Hf Ho] as ⟨Hf, Ho⟩
  · iframe
  wp_apply os.File.Seek.wp_end f fd name dqf o dq (DFrac.own 1) d m hfd hsz
    $$ [Hf Ho Hfd Hm] as %n %err ⟨Hf, Hfd, Hm, Hr⟩
  · iframe; iexact Hinv
  icases Hr with (⟨%hn, Ho⟩ | ⟨%herr, Ho⟩)
  rotate_left
  · cases err with
    | nil => exact absurd rfl herr
    | ok ie =>
    wp_auto
    iapply HΦ
    iframe Hf Hfd
    iright
    isplitr
    · ipureintro; intro h; cases h
    iexists o, m, xs
    iframe
    ipureintro; exact ⟨hole, rfl, hxs⟩
  obtain ⟨rfl, rfl⟩ := hn
  wp_auto
  wp_apply wp_Truncate f fd name dqf o dq d m xs hfd hwr ho0 hxs
    $$ [Hf Hfd Hm Hb] as %err ⟨Hf, Hfd, Hr, -⟩
  · rw [show min m.size o.toNat = o.toNat by omega]
    iframe; iframe Hinv; iapply mcellsAny_empty (GF := GF) _ hmaps
  icases Hr with (⟨%he, Hd⟩ | ⟨%he, Hd⟩)
  rotate_left
  · cases err with
    | nil => exact absurd rfl he
    | ok ie =>
    wp_auto
    iapply HΦ
    iframe Hf Hfd
    iright
    isplitr
    · ipureintro; intro h; cases h
    icases Hd with (Hd | Hd)
    · icases ftDone_shrunk _ m o.toNat $$ Hd with ⟨%m1, %hm1, Hm⟩
      iexists W64 m.size, m1, []
      iframe
      isplitr
      · ipureintro; simp [hm1]
      unfold osBytes; iapply (bytesG_nil _ _ _ _).2; iempintro
    · unfold os.ftUndone
      icases Hd with ⟨%xs', %hxs', Hm, Hb, -⟩
      iexists W64 m.size, _, xs'
      iframe
      rw [show min m.size o.toNat = o.toNat by omega]
      iframe
      ipureintro
      have hl := congrArg List.length hxs'
      simp only [List.length_map] at hl
      refine ⟨by rw [OsMeta.announce_size]; omega, OsMeta.announce_maps .., ?_⟩
      rw [OsMeta.announce_size]; omega
  subst he
  wp_auto
  icases ftDone_shrunk _ m o.toNat $$ Hd with ⟨%m1, %hm1, Hm⟩
  have hsI : (W64 (m.size : Int)).toInt = m.size := by
    rw [BitVec.toInt_eq_toNat_cond]; simp only [BitVec.toNat_ofInt]; split <;> omega
  have hsN : (W64 (m.size : Int)).toNat = m.size := by
    simp only [BitVec.toNat_ofInt]; omega
  wp_apply wp_Preallocate f fd name dqf dq d m1 (W64 m.size) (W64 m.size) true hfd hwr
    (by rw [hm1.2.1, hmaps]) (by omega) (by omega) (by omega) (by omega) (fun _ => by omega)
    $$ [Hf Ho Hfd Hm] as %err ⟨Hf, Ho, Hfd, Hr⟩
  · iframe; isplitl [] <;> iassumption
  simp only [preallocPost, ↓reduceIte]
  icases Hr with ⟨%w, %hw, Hg⟩
  unfold preGrown
  icases Hg with ⟨%m', %hm', Hm, Hz⟩
  rw [hm1.1] at hw ⊢
  by_cases he : err = interface.nil
  · subst he
    wp_auto
    wp_apply os.File.Seek.wp_start f fd name dqf _ o hfd ho0 ho1 $$ [Hf Ho] as ⟨Hf, Ho⟩
    · iframe
    iapply HΦ
    iframe Hf Hfd
    ileft
    isplitr
    · ipureintro; rfl
    iframe Ho
    iexists m'
    have hw' : w = m.size := by have := hw.2.2 rfl; omega
    subst hw'
    iframe
    have hcz1 := hm1.2.2
    rw [Nat.max_eq_left hole] at hcz1
    ipureintro; exact ⟨hm'.1, hm'.2.1.trans hm1.2.1, Nat.le_trans hcz1 hm'.2.2⟩
  · cases err with
    | nil => exact absurd rfl he
    | ok ie =>
    wp_auto
    iapply HΦ
    iframe Hf Hfd
    iright
    isplitr
    · ipureintro; intro h; cases h
    icases (osZerosA_unfold _ _ _ _).1 $$ Hz with ⟨%zs, %hzs, Hz⟩
    iexists W64 m.size, m', _
    iframe
    ipureintro
    simp only [List.length_map]
    refine ⟨by omega, hm'.2.1.trans hm1.2.1, by omega⟩

end proof

end EtcdGrove
end Perennial
