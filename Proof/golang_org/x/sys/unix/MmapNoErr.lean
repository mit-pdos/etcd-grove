/-
The proof of `Spec/golang_org/x/sys/unix/MmapNoErr.lean`: `wp_osMmapNE`, then `unsafe.Slice` of the
base, as `Proof/golang_org/x/sys/unix/Mmap.lean`'s success.
-/
module

public import Spec.golang_org.x.sys.unix.MmapNoErr
public import Proof.golang_org.x.sys.unix.Mmap
public import GooseLang.Ext.Fs.NoMapLockErrSpecs

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
variable [golang_org.x.sys.unix.Assumptions]

theorem golang_org.x.sys.unix.Mmap.wp_proofNoErr :
    golang_org.x.sys.unix.Mmap.specNoErr (GF := GF) (hG := hG) := by
  intro Sio _ hS fd off len prot fl dq d m hrd hoff hlen hprot hfl
  wp_start as ⟨#Hinv, Hfd, Hm⟩
  have hl : ¬ (sint.Z len ≤ sint.Z (W64 0)) := by
    rw [show sint.Z (W64 0) = 0 from rfl]; simp only [sint.Z]; omega
  rw [decide_eq_false hl]
  wp_auto
  wp_apply wp_osMmapNE hS fd off len prot fl dq d m CoPset.subseteq_top hrd hoff hlen hprot hfl
    $$ Hinv Hfd Hm as %base %he Hm Hc Hfd
  obtain ⟨hpos, hmax⟩ := he
  wp_func_call
  wp_call
  have hnn : base ≠ null := by intro h; subst h; simp [null] at hpos
  have hlz : sint.Z len = (len.toNat : Int) := by
    simp only [sint.Z]; have := BitVec.toInt_eq_toNat_cond len; split at this <;> omega
  rw [ite_eq_right (by omega), ite_eq_right hnn,
    ite_eq_right (by simp only [maxAddr] at hmax; push_cast; omega)]
  wp_auto
  rw [← show errnoErr 0 = interface.nil by unfold errnoErr; rfl]
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
