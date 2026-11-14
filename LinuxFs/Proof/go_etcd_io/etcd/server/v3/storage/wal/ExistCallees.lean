/-
The proofs of `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/ExistCallees.lean`'s `ReadDir` specs,
from `fileutil.ReadDir.wp_core` (`ReadDirCore.lean`) over the `os` layer's explicit-error specs
(`NsChildS.lean`: `os.Open.wp_dirChildS`, `File.Readdirnames.wp_dirChildS`, `os.Open.wp_absentErrS`;
`NsS.lean`: `File.Close.wp_dirS`), given `errors.IsPathErrnoNotExist.spec` (not proved: the error tree
of the part's `os` errors). Lean-first.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.ExistCallees
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

theorem fileutil.ReadDir.wp_specChildIs
    (wp_Strings : sort.Strings.spec (GF := GF) (hG := hG))
    (wp_Ext : filepath.Ext.spec (GF := GF) (hG := hG))
    (wp_IsNE : errors.IsPathErrnoNotExist.spec (GF := GF) (hG := hG)) :
    fileutil.ReadDir.specChildIs (GF := GF) (hG := hG) := by
  intro d b sl gs es dqs R jp dq Np dqp hp J qc N dqn h hlen hb hNp hJ
  iintro %Φ ⟨#Hinv, #Hsi, #Hpkg, Hp, Hnp, Hperm, Hn, Hsl, #Hgs⟩ HΦ
  ihave #Hos : isPkgInit (PROP := IProp GF) pkg_id.os $$ []
  · iPkgInit
  let OkN : List GoString → Prop := fun names => (∀ b ∈ names, NameOk b) ∧
    (∀ b, N.Mem b → ((h.cur !! b).isSome ↔ b ∈ names)) ∧ (∀ b, N.Mem b → names.count b ≤ 1) ∧
    names.length ≤ 2 ^ 44
  let Er : GoInterface → IProp GF := fun err => errIsNotExist err false
  have hOk : ∀ names, OkN names → names.length ≤ 2 ^ 62 := fun names h => by
    have := h.2.2.2; omega
  have herr : ∀ (err : GoInterface) (e : w64), e ≠ 0 → e ≠ ENOENT →
      ⊢ isPkgInit (PROP := IProp GF) pkg_id.os -∗ os.errnoPathErr err e -∗ Er err := by
    intro err e he0 hne
    iintro #Hos #Herr
    ihave H := wp_IsNE err e he0 $$ Hos Herr
    rw [decide_eq_false hne]
    iexact H
  have wpOpen : ∀ Φ : val → IProp GF,
      ⊢ iprop(osInv ∗ osSharedInv R ∗ isPkgInit (PROP := IProp GF) pkg_id.os ∗ osPathS R d dq jp ∗
          osNames jp Np dqp hp ∗ osCallPerm qc ∗ osNames J N dqn h) -∗
        (∀ (f : Loc) (err : GoInterface),
          ((∃ fd : w64, ⌜err = interface.nil⌝ ∗ os.ownFile f fd (child d b) (DFrac.own 1) ∗
              iprop(osDirFdS fd J .idle ∗ osInv) ∗
              iprop(osSharedInv R ∗ isPkgInit (PROP := IProp GF) pkg_id.os ∗ osNames J N dqn h ∗
                osPathS R d dq jp ∗ osNames jp Np dqp hp ∗ osCallPerm qc)) ∨
           (⌜err ≠ interface.nil⌝ ∗ Er err ∗
              iprop(osPathS R d dq jp ∗ osNames jp Np dqp hp ∗ osCallPerm qc ∗ osNames J N dqn h))) -∗
          Φ (PairV #f #err)) -∗
        WP (App (Val (@! os.Open)) (Val #(child d b))) {{ Φ }} := by
    intro Φ
    iintro ⟨#Hinv, #Hsi, #Hos, Hp, Hnp, Hperm, Hn⟩ HΦ
    wp_apply os.Open.wp_dirChildS d b R jp J Np dq dqp hp qc hb hNp hJ $$ [Hp Hnp Hperm]
      as %f %err ⟨Hp, Hnp, Hperm, Hr⟩
    · iframe; isplitl [] <;> iassumption
    icases Hr with (⟨%fd, %herr0, Hf, Hfd⟩ | ⟨%e, %he, #Herr⟩)
    · iapply HΦ; ileft; iexists fd; iframe
      isplitr
      · ipureintro; exact herr0
      isplitl [] <;> try iassumption
      isplitl [] <;> iassumption
    · ihave %hne := os.errnoPathErr_ne err e $$ Herr
      iapply HΦ; iright; iframe
      isplitr
      · ipureintro; exact hne
      iapply (herr err e he.1 he.2.1) $$ Hos Herr
  have wpRead : ∀ (f : Loc) (fd n : w64) (Φ : val → IProp GF), ⊢ ⌜sint.Z n ≤ 0⌝ -∗
      os.ownFile f fd (child d b) (DFrac.own 1) -∗ iprop(osDirFdS fd J .idle ∗ osInv) -∗
      iprop(osSharedInv R ∗ isPkgInit (PROP := IProp GF) pkg_id.os ∗ osNames J N dqn h ∗
        osPathS R d dq jp ∗ osNames jp Np dqp hp ∗ osCallPerm qc) -∗
      (∀ (r : GoSlice) (err : GoInterface), os.ownFile f fd (child d b) (DFrac.own 1) -∗
        iprop(osInv ∗ ∃ ph, osDirFdS fd J ph) -∗
        iprop(osPathS R d dq jp ∗ osNames jp Np dqp hp ∗ osCallPerm qc ∗ osNames J N dqn h) -∗
        ((∃ names : List GoString, ⌜err = interface.nil ∧ OkN names⌝ ∗ r ↦* names) ∨
         (⌜err ≠ interface.nil⌝ ∗ Er err)) -∗ Φ (PairV #r #err)) -∗
      WP (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Readdirnames")) (Val #n))
        {{ Φ }} := by
    intro f fd n Φ
    iintro %hn Hf ⟨Hfd, #Hinv⟩ ⟨#Hsi, #Hos, Hn, Hp, Hnp, Hperm⟩ HΦ
    wp_apply os.File.Readdirnames.wp_dirChildS f fd (child d b) (DFrac.own 1) R J N dqn h n hn
      d b jp Np dq dqp hp hb hNp hJ $$ [Hf Hfd Hn Hp Hnp] as %r %err ⟨Hf, Hn, Hp, Hnp, Hr⟩
    · iframe; isplitl [] <;> iassumption
    icases Hr with (⟨%names, %hr, Hr, Hfd⟩ | ⟨⟨%e, %he, #Herr⟩, %r0, %rs, Hfd⟩)
    · iapply HΦ $$ Hf [Hfd] [Hp Hnp Hperm Hn]
      · isplitl []
        · iassumption
        iexists _; iexact Hfd
      · iframe
      ileft; iexists names; iframe; ipureintro; exact hr
    · ihave %hne := os.errnoPathErr_ne err e $$ Herr
      iapply HΦ $$ Hf [Hfd] [Hp Hnp Hperm Hn]
      · isplitl []
        · iassumption
        iexists _; iexact Hfd
      · iframe
      iright
      isplitr
      · ipureintro; exact hne
      iapply (herr err e he.1 he.2) $$ Hos Herr
  have wpClose : ∀ (f : Loc) (fd : w64) (Φ : val → IProp GF),
      ⊢ os.ownFile f fd (child d b) (DFrac.own 1) -∗ iprop(osInv ∗ ∃ ph, osDirFdS fd J ph) -∗
        (∀ err : GoInterface, Φ #err) -∗
        WP (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Close")) (Val #())) {{ Φ }} := by
    intro f fd Φ
    iintro Hf ⟨#Hinv, %ph, Hfd⟩ HΦ
    wp_apply os.File.Close.wp_dirS f fd (child d b) J ph $$ [Hf Hfd] as %err -
    · iframe; iassumption
    iapply HΦ
  wp_apply (fileutil.ReadDir.wp_core wp_Strings wp_Ext (child d b) sl gs es dqs _ _ _ _ _ OkN Er Er
    hlen hOk wpOpen wpRead wpClose) $$ [Hp Hnp Hperm Hn Hsl]
    as %r %err ⟨Hsl, ⟨Hp, Hnp, Hperm, Hn⟩, Hr⟩
  · iframe
    isplitl []
    · isplitl [] <;> try iassumption
      isplitl [] <;> iassumption
    isplitl [] <;> iassumption
  iapply HΦ
  iframe
  icases Hr with (⟨%names, %rs, %hr, Hr⟩ | ⟨%herr1, Herr⟩)
  · obtain ⟨herr1, ⟨h1, h2, h3, -⟩, hout⟩ := hr
    ileft; iexists names, rs; iframe; ipureintro; exact ⟨herr1, h1, h2, h3, hout⟩
  · iright
    isplitr
    · ipureintro; exact herr1
    icases Herr with (H | H) <;> iexact H

theorem fileutil.ReadDir.wp_specAbsentIs
    (wp_Strings : sort.Strings.spec (GF := GF) (hG := hG))
    (wp_Ext : filepath.Ext.spec (GF := GF) (hG := hG))
    (wp_IsNE : errors.IsPathErrnoNotExist.spec (GF := GF) (hG := hG)) :
    fileutil.ReadDir.specAbsentIs (GF := GF) (hG := hG) := by
  intro d b sl gs es dqs R j dq qc N dqn h hlen hb hN hi
  iintro %Φ ⟨#Hinv, #Hsi, #Hpkg, Hp, Hperm, Hn, Hsl, #Hgs⟩ HΦ
  ihave #Hos : isPkgInit (PROP := IProp GF) pkg_id.os $$ []
  · iPkgInit
  let Er : GoInterface → IProp GF := fun err => iprop(∃ bn : Bool, errIsNotExist err bn)
  have wpOpen : ∀ Φ : val → IProp GF,
      ⊢ iprop(osInv ∗ osSharedInv R ∗ isPkgInit (PROP := IProp GF) pkg_id.os ∗ osPathS R d dq j ∗
          osCallPerm qc ∗ osNames j N dqn h) -∗
        (∀ (f : Loc) (err : GoInterface),
          ((∃ fd : w64, ⌜err = interface.nil⌝ ∗ os.ownFile f fd (child d b) (DFrac.own 1) ∗
              iprop(⌜False⌝) ∗ iprop(emp)) ∨
           (⌜err ≠ interface.nil⌝ ∗ Er err ∗
              iprop(osPathS R d dq j ∗ osCallPerm qc ∗ osNames j N dqn h))) -∗
          Φ (PairV #f #err)) -∗
        WP (App (Val (@! os.Open)) (Val #(child d b))) {{ Φ }} := by
    intro Φ
    iintro ⟨#Hinv, #Hsi, #Hos, Hp, Hperm, Hn⟩ HΦ
    wp_apply os.Open.wp_absentErrS d b R j N dq dqn h qc hb hN hi $$ [Hp Hn Hperm]
      as %f %err ⟨Hp, Hn, Hperm, %e, %he, #Herr⟩
    · iframe; isplitl [] <;> iassumption
    ihave %hne := os.errnoPathErr_ne err e $$ Herr
    iapply HΦ; iright; iframe
    isplitr
    · ipureintro; exact hne
    iexists _
    iapply (wp_IsNE err e he.1) $$ Hos Herr
  have wpRead : ∀ (f : Loc) (fd n : w64) (Φ : val → IProp GF), ⊢ ⌜sint.Z n ≤ 0⌝ -∗
      os.ownFile f fd (child d b) (DFrac.own 1) -∗ iprop(⌜False⌝) -∗ iprop(emp) -∗
      (∀ (r : GoSlice) (err : GoInterface), os.ownFile f fd (child d b) (DFrac.own 1) -∗
        iprop(⌜False⌝) -∗ iprop(osPathS R d dq j ∗ osCallPerm qc ∗ osNames j N dqn h) -∗
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
    · isplitl [] <;> try iassumption
      isplitl [] <;> iassumption
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
