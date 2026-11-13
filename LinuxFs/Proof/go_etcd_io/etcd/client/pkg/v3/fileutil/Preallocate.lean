/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/client/pkg/v3/fileutil/Preallocate.lean`.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.Preallocate
public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.preallocExtend
public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.preallocFixed

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
variable [go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]

theorem go_etcd_io.etcd.client.pkg.v3.fileutil.Preallocate.wp_proof
    (wp_ext : go_etcd_io.etcd.client.pkg.v3.fileutil.preallocExtend.spec (GF := GF) (hG := hG))
    (wp_fixed : go_etcd_io.etcd.client.pkg.v3.fileutil.preallocFixed.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.client.pkg.v3.fileutil.Preallocate.spec (GF := GF) (hG := hG) := by
  intro f fd name dqf dq d m o sz ext hfd hwr hmaps ho0 ho1 hsz0 hsz1 hle
  wp_start as ⟨#Hinv, #Herrs, Hf, Ho, Hfd, Hm⟩
  wp_auto
  by_cases hz : sz = W64 0
  · subst hz
    wp_auto
    iapply HΦ
    iframe Hf Ho Hfd
    cases ext
    · simp only [preallocPost, Bool.false_eq_true, ↓reduceIte]
      iexact Hm
    · have h0 : m.size = 0 := by have := hle rfl; simp at this; omega
      simp only [preallocPost, ↓reduceIte]
      iexists m.size
      isplitr
      · ipureintro; simp [h0]
      iapply preGrown_same $$ Hm
  have hpos : 0 < sz.toInt := by
    rcases Int.lt_or_eq_of_le hsz0 with h | h
    · exact h
    · exfalso; apply hz; apply BitVec.eq_of_toInt_eq; rw [← h]; rfl
  rw [decide_eq_false hz]
  wp_auto
  cases ext
  · wp_auto
    wp_apply wp_fixed f fd name dqf dq d sz hwr hpos $$ [Hf Hfd] as %err ⟨Hf, Hfd⟩
    · iframe; isplitl [] <;> iassumption
    iapply HΦ
    iframe
    simp only [preallocPost, Bool.false_eq_true, ↓reduceIte]
    iexact Hm
  · wp_auto
    wp_apply wp_ext f fd name dqf dq d m o sz hfd hwr hmaps ho0 ho1 hpos hsz1 (hle rfl)
      $$ [Hf Ho Hfd Hm] as %err ⟨Hf, Ho, Hfd, Hr⟩
    · iframe; isplitl [] <;> iassumption
    iapply HΦ
    iframe Hf Ho Hfd
    simp only [preallocPost, ↓reduceIte]
    iexact Hr

end proof

end EtcdGrove
end Perennial
