/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/client/pkg/v3/fileutil/ReadDir.lean`: `ReadDir.wp_core`
(`ReadDirCore.lean`: the options loop, `sort.Strings`, the extension filter) over the shared-mode
directory specs `os.Open.wp_dirErrS`, `File.Readdirnames.wp_dirS`, `File.Close.wp_dirS` (`NsS.lean`).
`sort.Strings`' bound (at most `2^62` names) is `Readdirnames`' (at most `2^44`: its trusted model
assumes Go's `growslice` limit, `TrustedCode/os.lean`, pending the user's review).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.client.pkg.v3.fileutil.ReadDirCore

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
variable [os.Assumptions] [os.file.FieldAssumptions] [go.BasicIntoValInj]

theorem go_etcd_io.etcd.client.pkg.v3.fileutil.ReadDir.wp_proof
    (wp_Strings : sort.Strings.spec (GF := GF) (hG := hG))
    (wp_Ext : filepath.Ext.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.client.pkg.v3.fileutil.ReadDir.spec (GF := GF) (hG := hG) := by
  intro d sl gs es dqs R j dq qc N dqn h hlen
  iintro %Φ ⟨#Hinv, #Hsi, #Hpkg, Hp, Hperm, Hn, Hsl, #Hgs⟩ HΦ
  let OkN : List GoString → Prop := fun names => (∀ b ∈ names, NameOk b) ∧
    (∀ b, N.Mem b → ((h.cur !! b).isSome ↔ b ∈ names)) ∧ (∀ b, N.Mem b → names.count b ≤ 1) ∧
    names.length ≤ 2 ^ 44
  let Er : GoInterface → IProp GF := fun err => iprop(∃ e : w64, ⌜e ≠ 0⌝ ∗ os.errnoPathErr err e)
  have hOk : ∀ names, OkN names → names.length ≤ 2 ^ 62 := fun names h => by
    have := h.2.2.2; omega
  have wpOpen : ∀ Φ : val → IProp GF,
      ⊢ iprop(osInv ∗ osSharedInv R ∗ osPathS R d dq j ∗ osCallPerm qc ∗ osNames j N dqn h) -∗
        (∀ (f : Loc) (err : GoInterface),
          ((∃ fd : w64, ⌜err = interface.nil⌝ ∗ os.ownFile f fd d (DFrac.own 1) ∗
              iprop(osDirFdS fd j .idle ∗ osInv) ∗
              iprop(osSharedInv R ∗ osNames j N dqn h ∗ osPathS R d dq j ∗ osCallPerm qc)) ∨
           (⌜err ≠ interface.nil⌝ ∗ Er err ∗
              iprop(osPathS R d dq j ∗ osCallPerm qc ∗ osNames j N dqn h))) -∗ Φ (PairV #f #err)) -∗
        WP (App (Val (@! os.Open)) (Val #d)) {{ Φ }} := by
    intro Φ
    iintro ⟨#Hinv, #Hsi, Hp, Hperm, Hn⟩ HΦ
    wp_apply os.Open.wp_dirErrS d R j dq qc $$ [Hp Hperm] as %f %err ⟨Hp, Hperm, Hr⟩
    · iframe; isplitl [] <;> iassumption
    icases Hr with (⟨%fd, %herr, Hf, Hfd⟩ | ⟨%e, %he, #Herr⟩)
    · iapply HΦ; ileft; iexists fd; iframe
      isplitr
      · ipureintro; exact herr
      isplitl [] <;> iassumption
    · ihave %hne := os.errnoPathErr_ne err e $$ Herr
      iapply HΦ; iright; iframe
      isplitr
      · ipureintro; exact hne
      iexists e; iframe Herr; ipureintro; exact he.1
  have wpRead : ∀ (f : Loc) (fd n : w64) (Φ : val → IProp GF), ⊢ ⌜sint.Z n ≤ 0⌝ -∗
      os.ownFile f fd d (DFrac.own 1) -∗ iprop(osDirFdS fd j .idle ∗ osInv) -∗
      iprop(osSharedInv R ∗ osNames j N dqn h ∗ osPathS R d dq j ∗ osCallPerm qc) -∗
      (∀ (r : GoSlice) (err : GoInterface), os.ownFile f fd d (DFrac.own 1) -∗
        iprop(osInv ∗ ∃ ph, osDirFdS fd j ph) -∗
        iprop(osPathS R d dq j ∗ osCallPerm qc ∗ osNames j N dqn h) -∗
        ((∃ names : List GoString, ⌜err = interface.nil ∧ OkN names⌝ ∗ r ↦* names) ∨
         (⌜err ≠ interface.nil⌝ ∗ Er err)) -∗ Φ (PairV #r #err)) -∗
      WP (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Readdirnames")) (Val #n))
        {{ Φ }} := by
    intro f fd n Φ
    iintro %hn Hf ⟨Hfd, #Hinv⟩ ⟨#Hsi, Hn, Hp, Hperm⟩ HΦ
    wp_apply os.File.Readdirnames.wp_dirS f fd d (DFrac.own 1) R j N dqn h n hn
      $$ [Hf Hfd Hn] as %r %err ⟨Hf, Hn, Hr⟩
    · iframe; isplitl [] <;> iassumption
    icases Hr with (⟨%names, %hr, Hr, Hfd⟩ | ⟨⟨%e, %he, #Herr⟩, %r0, %rs, Hfd⟩)
    · obtain ⟨herr, h1, h2, h3, h4⟩ := hr
      iapply HΦ $$ Hf [Hfd] [Hp Hperm Hn]
      · isplitl []
        · iassumption
        iexists _; iexact Hfd
      · iframe
      ileft; iexists names; iframe; ipureintro; exact ⟨herr, h1, h2, h3, h4⟩
    · ihave %hne := os.errnoPathErr_ne err e $$ Herr
      iapply HΦ $$ Hf [Hfd] [Hp Hperm Hn]
      · isplitl []
        · iassumption
        iexists _; iexact Hfd
      · iframe
      iright
      isplitr
      · ipureintro; exact hne
      iexists e; iframe Herr; ipureintro; exact he
  have wpClose : ∀ (f : Loc) (fd : w64) (Φ : val → IProp GF),
      ⊢ os.ownFile f fd d (DFrac.own 1) -∗ iprop(osInv ∗ ∃ ph, osDirFdS fd j ph) -∗
        (∀ err : GoInterface, Φ #err) -∗
        WP (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Close")) (Val #())) {{ Φ }} := by
    intro f fd Φ
    iintro Hf ⟨#Hinv, %ph, Hfd⟩ HΦ
    wp_apply os.File.Close.wp_dirS f fd d j ph $$ [Hf Hfd] as %err -
    · iframe; iassumption
    iapply HΦ
  wp_apply (fileutil.ReadDir.wp_core wp_Strings wp_Ext d sl gs es dqs _ _ _ _ _ OkN Er Er hlen hOk
    wpOpen wpRead wpClose) $$ [Hp Hperm Hn Hsl] as %r %err ⟨Hsl, ⟨Hp, Hperm, Hn⟩, Hr⟩
  · iframe
    isplitl []
    · isplitl [] <;> iassumption
    isplitl [] <;> iassumption
  iapply HΦ
  iframe
  icases Hr with (⟨%names, %rs, %hr, Hr⟩ | ⟨%herr, Herr⟩)
  · obtain ⟨herr, ⟨h1, h2, h3, -⟩, hout⟩ := hr
    ileft; iexists names, rs; iframe; ipureintro; exact ⟨herr, h1, h2, h3, hout⟩
  · iright
    isplitr
    · ipureintro; exact herr
    icases Herr with (⟨%e, %he, #Herr⟩ | ⟨%e, %he, #Herr⟩) <;>
      iapply (os.errnoPathErr_fmtErrorOkOrNil err e he) $$ Herr

end proof

end EtcdGrove
end Perennial
