module
public import Spec.go_etcd_io.bbolt.DB__getPageSizeFromSecondMeta
public import Spec.go_etcd_io.bbolt.DB__pageInBuffer
public import Spec.go_etcd_io.bbolt.internal.common.Page__Meta
public import Spec.go_etcd_io.bbolt.internal.common.Meta__PageSize
public import Spec.os.File__ReadAt
public import Spec.os.File__Stat
public import Spec.io.fs.FileInfo__Size
public import Proof.go_etcd_io.bbolt.ErrShape

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]
variable [os_fi : OsFileInfoAssumptions (GF := GF)]

theorem DB.getPageSizeFromSecondMeta.wp_proof (hStat : os.File.Stat.spec (GF := GF) (hG := hG))
    (hSize : fs.FileInfo.Size.spec (GF := GF) (hG := hG))
    (hReadAt : os.File.ReadAt.spec (GF := GF) (hG := hG))
    (hpib : DB.pageInBuffer.spec (GF := GF) (hG := hG))
    (hMeta : Page.Meta.spec (GF := GF) (hG := hG))
    (hValidate : Meta.Validate.spec (GF := GF) (hG := hG))
    (hPageSize : Meta.PageSize.spec (GF := GF) (hG := hG)) :
    DB.getPageSizeFromSecondMeta.spec (GF := GF) (hG := hG) := by
  intro dbl f fd bs ps dq Hbl
  wp_start as ⟨Hf, Hps, #Hof, Hfb⟩
  ihave #Hei : (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.errors) $$ []
  · iPkgInit
  icases bboltError_access errors.ErrInvalid (by simp [bboltErrorNames]) $$ Hei
    with ⟨%e, #He, %Hne⟩
  wp_auto
  wp_apply hStat f fd bs $$ [Hfb] as %fi %err ⟨Hfb, Hfi⟩
  · iframe; iframe #
  try wp_auto
  icases Hfi with (%Herr | ⟨%Herr, #Hfi⟩)
  · cases err with
    | nil => exact absurd rfl Herr.1
    | ok ei =>
      -- `Stat` failed: its error
      try wp_auto
      iapply HΦ
      iframe
      ipureintro
      right
      exact Herr
  subst Herr
  try wp_auto
  wp_apply hSize fi bs.length $$ [Hfi]
  · iexact Hfi
  try wp_auto
  obtain ⟨t', p', rfl⟩ := Hne
  ihave IH : iprop(∃ (j : w64) (cr : Bool), "i" ∷ i_ptr ↦ j ∗
      "metaCanRead" ∷ metaCanRead_ptr ↦ cr ∗ "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ 15⌝ ∗
      "Hf" ∷ structFieldRef DB go!"file" dbl ↦{dq} f ∗
      "Hps" ∷ structFieldRef DB go!"pageSize" dbl ↦{dq} ps ∗ "Hfb" ∷ fileBytes fd bs ∗
      "db" ∷ db_ptr ↦ dbl ∗ "fileSize" ∷ fileSize_ptr ↦ W64 (bs.length : Int))
    $$ [i metaCanRead Hf Hps Hfb db fileSize]
  · iexists (W64 0), (zero_val Bool); iframe; ipureintro; decide
  wp_for IH
  by_cases hj : sint.Z j ≤ 14
  · rw [decide_eq_true hj]
    try wp_auto
    done
  · rw [decide_eq_false hj]
    try wp_auto
    done

end proof

end bbolt
end EtcdGrove
end Perennial
