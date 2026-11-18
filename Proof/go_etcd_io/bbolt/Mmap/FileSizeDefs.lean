/-
`fmtErrorOk_argOk`, `errorf_fmtErrorOk` and `DB.fileSize.spec`, out of `FileSize.lean`'s proof so that
`MunmapSpec.lean` and the modules over it import them without the proof (import tiers, 2026-11-18).
-/
module

public import Proof.go_etcd_io.bbolt.Mmap.ErrPtr
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

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section fsz
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
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
    iintro ⟨%h, #H⟩
    iright; ileft; isplitr
    · iexact H
    · ipureintro; exact h.1

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
  ∀ (db f : Loc) (fd : w64) (p : BFile) (dqf dqo dqd dqm : DFrac) (d : OsFd) (m : OsMeta),
  d.ino = p.ino → m.size < 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ osInv (GF := GF) ∗
      db.[DB, go!"file"] ↦{dqf} f ∗ fileOwn f fd p.path dqo ∗ osFd fd dqd d ∗
      osMeta p.ino dqm m ∗ db.[DB, go!"pageSize"] ↦□ W64 4096 }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"fileSize")) (Val #()))
  {{ (r : w64) (err : GoInterface), RET (PairV #r #err);
      db.[DB, go!"file"] ↦{dqf} f ∗ fileOwn f fd p.path dqo ∗ osFd fd dqd d ∗ osMeta p.ino dqm m ∗
      ((⌜err = interface.nil ∧ r = W64 (m.size : Int) ∧ 8192 ≤ m.size⌝) ∨
       (⌜err ≠ interface.nil ∧ errPtrTyped err⌝ ∗ fmtErrorOk err)) }}

end fsz

end bbolt
end EtcdGrove
end Perennial
