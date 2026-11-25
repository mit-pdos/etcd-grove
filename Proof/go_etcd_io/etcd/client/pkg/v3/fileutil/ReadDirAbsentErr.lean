/-
The proof of `Spec/go_etcd_io/etcd/client/pkg/v3/fileutil/ReadDirAbsentErr.lean`, from
`fileutil.ReadDir.wp_core` (`ReadDirCore.lean`) over `os.Open.wp_absentErrSW`
(`Proof/os/OpenAbsentNE.lean`). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.ReadDirAbsentErr
public import Proof.go_etcd_io.etcd.client.pkg.v3.fileutil.ReadDirCore

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
variable [os.Assumptions] [go.BasicIntoValInj]

theorem fileutil.ReadDir.wp_proofAbsentErr
    (wp_Strings : sort.Strings.spec (GF := GF) (hG := hG))
    (wp_Ext : filepath.Ext.spec (GF := GF) (hG := hG)) :
    fileutil.ReadDir.specAbsentErr (GF := GF) (hG := hG) := by
  intro d b sl gs es dqs R j dq qc N dqn h hlen hb hN hi
  iintro %Φ ⟨#Hinv, #Hsi, #Hpkg, Hp, Hperm, Hn, Hsl, #Hgs⟩ HΦ
  let Er : GoInterface → IProp GF := fun err =>
    iprop(∃ e : w64, ⌜e ≠ 0 ∧ (FsNoErrAt (child d b) → e = ENOENT)⌝ ∗ os.errnoPathErr err e)
  have wpOpen : ∀ Φ : val → IProp GF,
      ⊢ iprop(osInv ∗ osSharedInv R ∗ osPathS R d dq j ∗ osCallPerm (callKey R d) qc ∗
          osNames j N dqn h) -∗
        (∀ (f : Loc) (err : GoInterface),
          ((∃ fd : w64, ⌜err = interface.nil⌝ ∗ os.ownFile f fd (child d b) (DFrac.own 1) ∗
              iprop(⌜False⌝) ∗ iprop(emp)) ∨
           (⌜err ≠ interface.nil⌝ ∗ Er err ∗
              iprop(osPathS R d dq j ∗ osCallPerm (callKey R d) qc ∗ osNames j N dqn h))) -∗
          Φ (PairV #f #err)) -∗
        WP (App (Val (@! os.Open)) (Val #(child d b))) {{ Φ }} := by
    intro Φ
    iintro ⟨#Hinv, #Hsi, Hp, Hperm, Hn⟩ HΦ
    wp_apply os.Open.wp_absentErrSW d b R j N dq dqn h qc hb hN hi $$ [Hp Hn Hperm]
      as %f %err ⟨Hp, Hn, Hperm, %e, %he, #Herr⟩
    · iframe; isplitl [] <;> iassumption
    ihave %hne := os.errnoPathErr_ne err e $$ Herr
    iapply HΦ; iright; iframe
    isplitr
    · ipureintro; exact hne
    iexists e
    iframe Herr
    ipureintro; exact ⟨he.1, he.2.2⟩
  have wpRead : ∀ (f : Loc) (fd n : w64) (Φ : val → IProp GF), ⊢ ⌜sint.Z n ≤ 0⌝ -∗
      os.ownFile f fd (child d b) (DFrac.own 1) -∗ iprop(⌜False⌝) -∗ iprop(emp) -∗
      (∀ (r : GoSlice) (err : GoInterface), os.ownFile f fd (child d b) (DFrac.own 1) -∗
        iprop(⌜False⌝) -∗ iprop(osPathS R d dq j ∗ osCallPerm (callKey R d) qc ∗ osNames j N dqn h) -∗
        ((∃ names : List GoString, ⌜err = interface.nil ∧ False⌝ ∗ r ↦* names) ∨
         (⌜err ≠ interface.nil⌝ ∗ Er err)) -∗ Φ (PairV #r #err)) -∗
      WP (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Readdirnames")) (Val #n))
        {{ Φ }} := by
    intro f fd n Φ
    iintro %hn Hf %hF
    exact hF.elim
  have wpClose : ∀ (f : Loc) (fd : w64) (Φ : val → IProp GF),
      ⊢ os.ownFile f fd (child d b) (DFrac.own 1) -∗ iprop(⌜False⌝) -∗
        (∀ err : GoInterface, Φ #err) -∗
        WP (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Close")) (Val #())) {{ Φ }} := by
    intro f fd Φ
    iintro Hf %hF
    exact hF.elim
  wp_apply (fileutil.ReadDir.wp_core wp_Strings wp_Ext (child d b) sl gs es dqs _ _ _
    (fun _ => iprop(⌜False⌝)) (fun _ => iprop(⌜False⌝)) (fun _ => False) Er Er
    hlen (fun _ h => h.elim) wpOpen wpRead wpClose) $$ [Hp Hperm Hn Hsl]
    as %r %err ⟨Hsl, ⟨Hp, Hperm, Hn⟩, Hr⟩
  · iframe
    isplitl []
    · isplitl [] <;> iassumption
    isplitl [] <;> iassumption
  iapply HΦ
  iframe
  icases Hr with (⟨%names, %rs, %hr, -⟩ | ⟨%herr1, Herr⟩)
  · exact hr.elim
  · isplitr
    · ipureintro; exact herr1
    icases Herr with (H | H) <;> iexact H

end proof

end EtcdGrove
end Perennial

end
