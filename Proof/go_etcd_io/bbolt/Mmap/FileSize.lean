/-
`DB.fileSize` (U4, `notes/bbolt-proof-plan.md`): the file's size by `Stat`, an error when it is
under two pages. Its errors are `fmt.Errorf`'s, `fmtErrorOk`.
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Locks
public import Proof.go_etcd_io.bbolt.PkgInit
public import Spec.os.File__Stat
public import Spec.os.fileStat__Size
public import Spec.fmt.Errorf
public import Spec.fmt.ErrorOk

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section fsz
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

omit hos package_sem in
/-- An error `fmt` formats by its `Error()` is a good `Errorf` argument. -/
theorem fmtErrorOk_argOk (err : GoInterface) :
    fmtErrorOk (GF := GF) err ⊢ fmt.argOk err := by
  cases err with
  | nil => unfold fmtErrorOk; iintro %H; exact H.elim
  | ok ii =>
    unfold fmtErrorOk fmt.argOk
    iintro ⟨-, #H⟩
    iright; ileft; iexact H

omit hos package_sem in
/-- `fmt.Errorf`'s post gives `fmtErrorOk`. -/
theorem errorf_fmtErrorOk (ii : GoInterfaceOk) :
    fmt.stringMethodSpec (GF := GF) ii go!"Error" ∗
      ⌜methodSet ii.ty !! go!"Format" = none ∧
        methodSet ii.ty !! go!"Error" = some (go.signature.Signature [] false [go.string])⌝ ⊢
      fmtErrorOk (.ok ii) := by
  iintro ⟨#H, %h⟩
  iapply fmtErrorOk_of_errorf ii h $$ H

/-- **`db.fileSize()`**: the file's size (`OsMeta`'s), or an error. -/
abbrev DB.fileSize.spec : Prop :=
  ∀ (db f : Loc) (fd : w64) (p : GoString) (dqf dqo dqd dqm : DFrac) (d : OsFd) (m : OsMeta),
  d.path = p → m.size < 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ osInv (GF := GF) ∗
      db.[DB, go!"file"] ↦{dqf} f ∗ fileOwn f fd p dqo ∗ osFd fd dqd d ∗
      osMeta p dqm (some m) ∗ db.[DB, go!"pageSize"] ↦□ W64 4096 }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"fileSize")) (Val #()))
  {{ (r : w64) (err : GoInterface), RET (PairV #r #err);
      db.[DB, go!"file"] ↦{dqf} f ∗ fileOwn f fd p dqo ∗ osFd fd dqd d ∗ osMeta p dqm (some m) ∗
      ((⌜err = interface.nil ∧ r = W64 (m.size : Int) ∧ 8192 ≤ m.size⌝) ∨
       (⌜err ≠ interface.nil⌝ ∗ fmtErrorOk err)) }}

theorem DB.fileSize.wp_proof (hStat : os.File.Stat.spec (GF := GF) (hG := hG))
    (hSize : os.fileStat.Size.spec (GF := GF) (hG := hG))
    (hErrorf : fmt.Errorf.spec (GF := GF) (hG := hG)) :
    DB.fileSize.spec (GF := GF) (hG := hG) := by
  intro db f fd p dqf dqo dqd dqm d m hp hsz
  subst hp
  wp_start as ⟨#Hos, Hf, Hfo, Hfd, Hm, #Hps⟩
  wp_auto
  wp_apply hStat f fd d.path dqo dqd dqm d m $$ [Hfo Hfd Hm] as %fi %err ⟨Hfo, Hfd, Hm, Hr, #Hek⟩
  · rw [← fileOwn_eq]; iframe; iframe #
  ihave Hfo : fileOwn f fd d.path dqo $$ [Hfo]
  · rw [fileOwn_eq]; iexact Hfo
  try wp_auto
  icases Hr with (⟨%fs, %Hfs, Hst⟩ | %Hfs)
  · obtain ⟨rfl, rfl⟩ := Hfs
    wp_auto
    wp_apply hSize fs (W64 (m.size : Int)) $$ [Hst] as Hst
    · iframe
    try wp_auto
    have e1 : sint.Z (W64 (m.size : Int)) = (m.size : Int) := by word
    have e2 : sint.Z (W64 4096 * W64 2) = 8192 := by word
    rw [e1, e2]
    by_cases hs : (m.size : Int) < 8192
    · rw [decide_eq_true hs]
      wp_auto
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, -⟩
      wp_apply hErrorf _ _ _ _ $$ [$Hsl] as %e ⟨-, #HeS0, %Hty0, %Hptr0⟩
      · iframe
        fmt_args_ok
      try wp_auto
      iapply HΦ
      iframe
      iright
      isplitr
      · ipureintro; exact fun h => nomatch h
      · iapply errorf_fmtErrorOk
        isplitl
        · iexact HeS0
        · ipureintro; exact Hty0
    · rw [decide_eq_false hs]
      wp_auto
      iapply HΦ
      iframe
      ileft
      ipureintro
      exact ⟨rfl, rfl, by omega⟩
  · obtain ⟨hne, rfl⟩ := Hfs
    cases err with
    | nil => exact absurd rfl hne
    | ok ii =>
      ihave #Hek : fmtErrorOk (GF := GF) (GoInterface.ok ii) $$ []
      · iapply fmtErrorOkOrNil_ne _ hne $$ Hek
      wp_auto
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, -⟩
      wp_apply hErrorf _ _ _ _ $$ [$Hsl] as %e ⟨-, #HeS0, %Hty0, %Hptr0⟩
      · iframe
        simp only [fmt.argsOk]
        isplitl
        · iapply fmtErrorOk_argOk $$ Hek
        · itrivial
      try wp_auto
      iapply HΦ
      iframe
      iright
      isplitr
      · ipureintro; exact fun h => nomatch h
      · iapply errorf_fmtErrorOk
        isplitl
        · iexact HeS0
        · ipureintro; exact Hty0

end fsz

end bbolt
end EtcdGrove
end Perennial
