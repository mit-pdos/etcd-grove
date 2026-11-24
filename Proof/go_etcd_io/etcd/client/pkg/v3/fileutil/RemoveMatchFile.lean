/-
The proof of `Spec/go_etcd_io/etcd/client/pkg/v3/fileutil/RemoveMatchFile.lean`, over `Exist`,
`os.Stat.wp_dirS`, `ReadDir` and `fmt.ErrorfStrs.spec`. Lean-first (claim #34, stage 4).
-/
module

public import Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.RemoveMatchFile
public import Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.Exist
public import Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.ReadDir
public import Spec.fmt.ErrorfStrs
public import Proof.os.StatS

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]
variable [os_sem : os.Assumptions]

/-- `os.Stat` of a directory, its result dropped (the form `fileutil.Exist.spec` takes). -/
theorem wp_statDir_errRM (p : GoString) (R : Roots) (J : Ino) (dq : DFrac) (qc : Qp) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R p dq J ∗ osCallPerm (callKey R p) qc }}
      (App (Val (@! os.Stat)) (Val #p))
    {{ (fi : GoInterface) (err : GoInterface), RET (PairV #fi #err); osPathS R p dq J ∗
        osCallPerm (callKey R p) qc }} := by
  iintro %Φ Hpre HΦ
  wp_apply os.Stat.wp_dirS p R J dq qc $$ Hpre as %fi %err ⟨Hp, Hperm, -⟩
  iapply HΦ
  iframe

theorem go_etcd_io.etcd.client.pkg.v3.fileutil.RemoveMatchFile.wp_proof
    (wp_Exist : go_etcd_io.etcd.client.pkg.v3.fileutil.Exist.spec (GF := GF) (hG := hG))
    (wp_ReadDir : go_etcd_io.etcd.client.pkg.v3.fileutil.ReadDir.spec (GF := GF) (hG := hG))
    (wp_Errorf : fmt.ErrorfStrs.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.client.pkg.v3.fileutil.RemoveMatchFile.spec (GF := GF) (hG := hG) := by
  intro lg d mf R j dq qc dqn h hnone
  wp_start as ⟨#Hlg, #Hinv, #Hsi, Hp, Hperm, Hn⟩
  wp_auto
  ihave %hlgnn := zapLoggerOk_ne_null lg $$ Hlg
  simp only [hlgnn, decide_false]
  wp_auto
  wp_apply wp_Exist d _ _ (wp_statDir_errRM d R j dq qc) $$ [Hp Hperm] as %b ⟨%err, %hb, Hp, Hperm⟩
  · iframe; isplitl [] <;> iassumption
  subst hb
  by_cases he : err = GoInterface.nil
  rotate_left
  · rw [decide_eq_false he]
    wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply wp_Errorf _ _ [interface.ok (interface.mk go.string #d)] _ $$ [Hsl] as %e ⟨-, -, -⟩
    · iframe
      iapply (BigSepL.bigSepL_singleton (Φ := fun _ a => fmt.strArgOk (GF := GF) a)).2
      unfold fmt.strArgOk
      ileft; ipureintro; exact Or.inl (argWf_string _)
    try wp_auto
    iapply HΦ
    iframe
  rw [decide_eq_true he]
  wp_auto
  wp_apply wp_ReadDir d slice.nil [] [] (DFrac.own 1) R j dq qc (.except []) dqn h rfl
      $$ [Hp Hperm Hn]
  · iframe
    isplitl []; iassumption
    isplitl []; iassumption
    isplitl []; iassumption
    isplitl []
    · iapply ownSlice_nil
    iapply BigSepL.bigSepL_nil.2
    iempintro
  iintro %r %e ⟨Hp, Hperm, Hn, -, Hres⟩
  icases Hres with (⟨%names, %rs, %hrd, Hr⟩ | ⟨%he', -⟩)
  · obtain ⟨rfl, -, hnm, -, hout⟩ := hrd
    have hnames : names = [] := by
      apply List.eq_nil_iff_forall_not_mem.2
      intro b hb
      have := (hnm b (by simp [NameSet.Mem])).2 hb
      rw [hnone b] at this; simp at this
    subst hnames
    obtain ⟨srt, hperm, -, hrs⟩ := hout
    have hsrt : srt = [] := (List.Perm.nil_eq hperm).symm
    subst hsrt
    simp only [fileutil.optsExt, List.foldl_nil, ↓reduceIte] at hrs
    subst hrs
    ihave %hl := ownSlice_len _ _ _ $$ Hr
    have hr0 : r.len = W64 0 := by simp at hl; word
    wp_auto
    ihave IH : iprop(i_ptr ↦ W64 0) $$ [i]
    · iexact i
    wp_for IH
    rw [hr0]
    rw [decide_eq_false (by simp)]
    simp only [Bool.false_eq_true, ↓reduceIte]
    wp_auto
    iapply HΦ
    iframe
  · cases e with
    | nil => exact absurd rfl he'
    | ok e =>
      wp_auto
      iapply HΦ
      iframe

end proof

end EtcdGrove
end Perennial
