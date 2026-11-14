/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/client/pkg/v3/fileutil/ZeroToEndAu.lean`: `ZeroToEnd.lean`'s,
the truncate by `os.File.Truncate.specAu`, the growth by `Preallocate.specAu`.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.ZeroToEndAu
public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.PreallocateAu

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

/-- A truncate that shrank the file to `tg` landed, the caller's half (`os.ftDoneH`, nothing grown):
its `OsMeta`'s half, of size `tg`, the same mappings, the page cache known zero to the end of the
page holding the old end, knowing the candidates past the old size `m` knew (`PcKeep`), and the zeros
from the page cache known zero on if `m` knew zeros from at least its size. -/
theorem ftDoneH_shrunk (p : Ino) (m : OsMeta) (tg : Nat) (zs : List Cands) (htg : tg ≤ m.size) :
    os.ftDoneH (GF := GF) p m tg zs ⊢ ∃ m1 : OsMeta,
      ⌜m1.size = tg ∧ m1.maps = m.maps ∧ pageEnd m.size ≤ m1.cz ∧ PcKeep m m1 ∧ (m.ZfGe → m1.ZeroPg) ∧
        m1.lo = min m.lo tg⌝ ∗
      osMeta p (DFrac.own (1 : Qp).half) m1 := by
  unfold os.ftDoneH
  iintro ⟨%hzs, ⟨%tc, %rz, %htc, Hm⟩, -⟩
  iexists (rsPost true m tg tg).withTc tc rz
  iframe Hm
  ipureintro
  have h := os.rsPost_cz_true m tg tg
  rw [Nat.max_eq_left htg] at h
  exact ⟨rfl, rsPost_maps true m tg tg, h, PcKeep.of_tc (tr := true) rfl rfl htc.1,
    fun hz => OsMeta.zeroPg_rsPost_true hz tg, by simp only [OsMeta.withTc_lo, rsPost, OsMeta.announce]⟩

theorem go_etcd_io.etcd.client.pkg.v3.fileutil.ZeroToEnd.wp_proofAu
    (wp_Truncate : os.File.Truncate.specAu (GF := GF) (hG := hG))
    (wp_Preallocate : go_etcd_io.etcd.client.pkg.v3.fileutil.Preallocate.specAu (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.client.pkg.v3.fileutil.ZeroToEnd.specAu (GF := GF) (hG := hG) := by
  intro f fd name dqf dq d m o xs K P Q hfd hwr hmaps ho0 hole hsz hxs hP hPQ
  wp_start as ⟨#Hinv, #Herrs, Hf, Ho, Hfd, Hm, Hb, HK, #Hto, #Hts, #Hfs⟩
  have hoN : (o.toNat : Int) = o.toInt := by
    have := BitVec.toInt_eq_toNat_cond o; split at this <;> omega
  have ho1 : o.toInt ≤ 0xffffffff000 := by omega
  wp_auto
  wp_apply os.File.Seek.wp_cur f fd name dqf o hfd ho0 ho1 $$ [Hf Ho] as ⟨Hf, Ho⟩
  · iframe
  wp_apply os.File.Seek.wp_end f fd name dqf o dq (DFrac.own (1 : Qp).half) d m hfd hsz
    $$ [Hf Ho Hfd Hm] as %n %err ⟨Hf, Hfd, Hm, Hr⟩
  · iframe; iexact Hinv
  icases Hr with (⟨%hn, Ho⟩ | ⟨%herr, Ho⟩)
  rotate_left
  · cases err with
    | nil => exact absurd rfl herr
    | ok ie =>
    wp_auto
    iapply HΦ
    iframe Hf Hfd HK
    iright
    isplitr
    · ipureintro; intro h; cases h
    iexists o, m, xs
    iframe
    ipureintro; exact ⟨hole, rfl, hxs⟩
  obtain ⟨rfl, rfl⟩ := hn
  wp_auto
  have hmin : min m.size o.toNat = o.toNat := by omega
  wp_apply wp_Truncate f fd name dqf o dq d m xs K P hfd hwr ho0 hmaps (by omega) hP
    (fun m' h h' => (hPQ m' h (by omega)).1)
    $$ [Hf Hfd Hm Hb HK] as %err ⟨Hf, Hfd, HK, Hr, -⟩
  · rw [hmin]; iframe; iframe Hinv; iexact Hto
  icases Hr with (⟨%he, %zs, Hd⟩ | ⟨%he, Hd⟩)
  rotate_left
  · cases err with
    | nil => exact absurd rfl he
    | ok ie =>
    wp_auto
    iapply HΦ
    iframe Hf Hfd HK
    iright
    isplitr
    · ipureintro; intro h; cases h
    icases Hd with (⟨%zs, Hd⟩ | ⟨%xs', %hxs', Hd⟩)
    · icases ftDoneH_shrunk _ m o.toNat zs hole $$ Hd with ⟨%m1, %hm1, Hm⟩
      iexists W64 m.size, m1, []
      iframe
      isplitr
      · ipureintro; simp [hm1]
      unfold osBytes; iapply (bytesG_nil _ _ _ _).2; iempintro
    · unfold os.ftUndoneH
      icases Hd with ⟨⟨%tc, %rz, -, Hm⟩, Hb⟩
      iexists W64 m.size, _, xs'
      iframe
      rw [show min m.size o.toNat = o.toNat by omega]
      iframe
      ipureintro
      have hl := congrArg List.length hxs'
      simp only [List.length_map] at hl
      refine ⟨by rw [OsMeta.withTc_size, announce_size']; omega,
        announce_maps' m o.toNat (rsHi true m.size o.toNat) o.toNat, ?_⟩
      rw [OsMeta.withTc_size, announce_size']; omega
  subst he
  wp_auto
  icases ftDoneH_shrunk _ m o.toNat zs hole $$ Hd with ⟨%m1, %hm1, Hm⟩
  have hsI : (W64 (m.size : Int)).toInt = m.size := by
    rw [BitVec.toInt_eq_toNat_cond]; simp only [BitVec.toNat_ofInt]; split <;> omega
  have hsN : (W64 (m.size : Int)).toNat = m.size := by
    simp only [BitVec.toNat_ofInt]; omega
  wp_apply wp_Preallocate f fd name dqf dq d m1 (W64 m.size) (W64 m.size) true K Q hfd hwr
    (by rw [hm1.2.1, hmaps]) (by omega) (by omega) (by omega) (by omega) (fun _ => by omega)
    (fun m' h h' => (hPQ m' (by rw [← hm1.2.2.2.2.2]; exact h) (by rw [hsN] at h'; exact h')).2)
    $$ [Hf Ho Hfd Hm HK] as %err ⟨Hf, Ho, Hfd, HK, Hr⟩
  · iframe
    rw [hsN]
    isplitl []
    · iexact Hinv
    isplitl []
    · iexact Herrs
    isplitl []
    · iexact Hfs
    iexact Hts
  simp only [preallocPostH, ↓reduceIte]
  icases Hr with ⟨%w, %hw, Hg⟩
  iunfold preGrownH at Hg
  icases Hg with ⟨%m', %hm', Hm, Hz⟩
  rw [hm1.1] at hw ⊢
  rw [hsN] at hw
  by_cases he : err = interface.nil
  · subst he
    wp_auto
    wp_apply os.File.Seek.wp_start f fd name dqf _ o hfd ho0 ho1 $$ [Hf Ho] as ⟨Hf, Ho⟩
    · iframe
    iapply HΦ
    iframe Hf Hfd HK
    ileft
    isplitr
    · ipureintro; rfl
    iframe Ho
    iexists m'
    have hw' : w = m.size := hw.2.2 rfl
    subst hw'
    iframe
    ipureintro
    exact ⟨hm'.1, hm'.2.1.trans hm1.2.1, Nat.le_trans hm1.2.2.1 hm'.2.2.1,
      hm1.2.2.2.1.trans hm'.2.2.2.2.1 (by omega), fun hz => hm'.2.2.2.2.2.2 ⟨rfl, hm1.2.2.2.2.1 hz⟩⟩
  · cases err with
    | nil => exact absurd rfl he
    | ok ie =>
    wp_auto
    iapply HΦ
    iframe Hf Hfd HK
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
