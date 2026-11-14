/-
The proof of `fileutil.CreateDirAll.specTmp` (`LinuxFs/Spec/.../wal/CreateCallees.lean`, a hypothesis
of `wal.Create.wp_proof`): `name` absent, `CreateDirAll.spec` (proved) with its commit bound dropped;
`name` holding a directory of files, `TouchDirAll.specDir` then `ReadDir`, an error naming the files
found if there are any (`fmt.ErrorfStrs.spec`: `%q` of the `[]string`). Lean-first (`wal-leaf5`).
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.CreateCallees
public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.TouchDirAllDir
public import LinuxFs.Spec.fmt.ErrorfStrs
public import LinuxFs.Proof.go_etcd_io.etcd.client.pkg.v3.fileutil.TouchDirAllDir

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Fs WalFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]
variable [os_sem : os.Assumptions] [os.file.FieldAssumptions] [os.fileStat.FieldAssumptions]

theorem fileutil.CreateDirAll.wp_proofTmp (hC : fileutil.CreateDirAll.spec (GF := GF))
    (hT : fileutil.TouchDirAll.specDir (GF := GF))
    (wp_ReadDir : go_etcd_io.etcd.client.pkg.v3.fileutil.ReadDir.spec (GF := GF) (hG := hG))
    (wp_Errorf : fmt.ErrorfStrs.spec (GF := GF) (hG := hG)) :
    fileutil.CreateDirAll.specTmp (GF := GF) (hG := hG) := by
  intro lg R jp d parent name qp h hd hname hlen
  rcases hc : h.cur !! name with _ | ⟨i | J⟩
  · -- absent: `CreateDirAll.spec`
    iintro %Φ ⟨#Hpkg, #Hlg, #Hinv, #Hsi, Hp, Hperm, Ht⟩ HΦ
    iunfold tmpDirH at Ht
    icases Ht with ⟨Hn, -⟩
    wp_apply hC lg R jp d parent name qp h hd hname hlen hc $$ [Hp Hperm Hn] as %err ⟨Hp, Hperm, Hr⟩
    · iframe; iframe #
    iapply HΦ
    iframe Hp Hperm
    icases Hr with (⟨%herr, Ht⟩ | ⟨%herr, %h', %hJ, %J, %n, %hf, Hn, HJ, -⟩)
    · ileft; iframe; ipureintro; exact herr
    · iright
      isplitr
      · ipureintro; exact herr
      iexists h', hJ, J
      iframe
      ipureintro; exact ⟨hf.1, hf.2.2⟩
  · iintro %Φ ⟨#Hpkg, #Hlg, #Hinv, #Hsi, Hp, Hperm, Ht⟩ HΦ
    iunfold tmpDirH at Ht
    icases Ht with ⟨-, Hs⟩
    rw [hc]
    iunfold tmpSub at Hs
    icases Hs with %hf
    exact hf.elim
  · -- a directory of files: `TouchDirAll.specDir`, `ReadDir`
    wp_start as ⟨#Hlg, #Hinv, #Hsi, Hp, Hperm, Ht⟩
    wp_auto
    wp_apply hT lg R jp d parent name qp h J hd hname hlen hc $$ [Hp Hperm Ht] as %err ⟨Hp, Hperm, Hr⟩
    · iframe; iframe #
    icases Hr with (⟨%herr, %h', Hsub⟩ | ⟨%herr, %hJ, %hJf, Hn, HJ⟩)
    · cases err with
      | nil => exact absurd rfl herr
      | ok e =>
        wp_auto
        iapply HΦ
        iframe
        ileft
        isplitr
        · ipureintro; intro hc; cases hc
        iexists h'
        iexact Hsub
    subst herr hd
    wp_auto
    obtain ⟨hfo, hJt⟩ := hJf
    -- the error arm's `tmpDirH`: `.touch` holds nothing
    have hTe :
        osNames (GF := GF) jp (.only [name]) (DFrac.own 1) h ∗ osNames J (.except []) (DFrac.own 1) hJ ⊢
          tmpDirH jp name h := by
      iintro ⟨Hn, HJ⟩
      iapply tmpDirH_of jp name h J hJ hc hfo
      iframe
      rw [hJt]; unfold tmpEnt; iempintro
    icases osPathS_child_borrow R parent name jp J qp 1 h hname hc $$ [Hp Hn] with ⟨%ε, Hpc, Hback⟩
    · iframe
    wp_apply wp_ReadDir (child parent name) slice.nil [] [] (DFrac.own 1) R J (DFrac.own ε) 1 (.except [])
        (DFrac.own 1) hJ rfl $$ [Hpc Hperm HJ]
    · iframe
      isplitl []; iassumption
      isplitl []; iassumption
      isplitl []; iassumption
      isplitl []
      · iapply ownSlice_nil
      iapply BigSepL.bigSepL_nil.2
      iempintro
    iintro %r %e ⟨Hpc, Hperm, HJ, -, Hres⟩
    icases Hback $$ Hpc with ⟨Hp, Hn⟩
    icases Hres with (⟨%names, %rs, %hrd, Hr⟩ | ⟨%he, -⟩)
    rotate_left
    · cases e with
      | nil => exact absurd rfl he
      | ok e =>
        wp_auto
        iapply HΦ
        iframe Hp Hperm
        ileft
        isplitr
        · ipureintro; intro hc; cases hc
        iexists h
        iapply hTe $$ [Hn HJ]
        iframe
    obtain ⟨rfl, -, hnm, -, hout⟩ := hrd
    obtain ⟨srt, hperm, -, hrs⟩ := hout
    simp only [fileutil.optsExt, List.foldl_nil, ↓reduceIte] at hrs
    subst rs
    ihave %hl := ownSlice_len _ _ _ $$ Hr
    wp_auto
    by_cases hr0 : r.len = W64 0
    · -- no name: `J` is empty
      have hsrt : srt = [] := by
        apply List.eq_nil_of_length_eq_zero
        rw [hl.1, hr0]; rfl
      subst hsrt
      have hnames : names = [] := List.Perm.nil_eq hperm.symm |>.symm
      subst hnames
      have hJe : hJ.cur = ∅ := by
        apply GMap.ext; intro b
        cases hcb : hJ.cur !! b with
        | none => simp
        | some n =>
          exfalso
          have := (hnm b (by simp [NameSet.Mem])).1 (by simp [hcb])
          simp at this
      rw [hr0]
      wp_auto
      iapply HΦ
      iframe Hp Hperm
      iright
      isplitr
      · ipureintro; rfl
      iexists h, hJ, J
      iframe Hn HJ
      ipureintro; exact ⟨hc, hJe⟩
    · -- names found: an error naming them
      rw [decide_eq_false (by intro he; exact hr0 he)]
      wp_auto
      wp_apply wp_slice_literal (V := GoInterface) [interface.mkOk go.string #(child parent name),
        interface.mkOk (go.GoType.SliceType go.string) #r]
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, -⟩
      wp_apply wp_Errorf _ _ [interface.mkOk go.string #(child parent name),
          interface.mkOk (go.GoType.SliceType go.string) #r] _ $$ [Hsl Hr]
        as %e ⟨-, -, -⟩
      · iframe Hsl
        iapply BigSepL.bigSepL_cons.2
        isplitl []
        · simp only [fmt.strArgOk]
          ileft; ipureintro; exact Or.inl (argWf_string _)
        iapply (BigSepL.bigSepL_singleton (Φ := fun _ a => fmt.strArgOk (GF := GF) a)).2
        simp only [fmt.strArgOk]
        iright
        iexists r
        iexists DFrac.own 1
        iexists srt
        iframe Hr
        ipureintro; simp
      try wp_auto
      iapply HΦ
      iframe Hp Hperm
      ileft
      isplitr
      · ipureintro; intro hc; cases hc
      iexists h
      iapply hTe $$ [Hn HJ]
      iframe

end proof

end EtcdGrove
end Perennial
