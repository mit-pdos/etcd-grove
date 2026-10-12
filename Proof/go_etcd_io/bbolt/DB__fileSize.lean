module
public import Spec.go_etcd_io.bbolt.DB__fileSize
public import Spec.os.File__Stat
public import Spec.io.fs.FileInfo__Size

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

variable [os_fi : OsFileInfoAssumptions (GF := GF)]

theorem DB.fileSize.wp_proof (hStat : os.File.Stat.spec (GF := GF) (hG := hG))
    (hSize : fs.FileInfo.Size.spec (GF := GF) (hG := hG)) :
    DB.fileSize.spec (GF := GF) (hG := hG) := by
  intro dbl f fd bs ps dq Hbl Hps
  wp_start as ⟨Hf, Hp, #Hfile, Hbytes⟩
  wp_auto
  wp_apply hStat f fd bs $$ [Hbytes] as %fi %err ⟨Hbytes, Hfi⟩
  · iframe; iframe #
  try wp_auto
  icases Hfi with (%Herr | ⟨%Herr, #Hfi⟩)
  · cases err with
    | nil => exact absurd rfl Herr
    | ok i =>
      try wp_auto
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, -⟩
      wp_apply fmt.wp_Errorf $$ [$Hsl] as %e2 _
      try wp_auto
      ispecialize HΦ $$ %(W64 0) %(GoInterface.ok e2)
      iapply HΦ; iframe
      ipureintro; intro h; cases h
  · subst Herr
    try wp_auto
    wp_apply hSize fi bs.length $$ [Hfi]
    · iexact Hfi
    try wp_auto
    wp_if_destruct
    · try wp_auto
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, -⟩
      wp_apply fmt.wp_Errorf $$ [$Hsl] as %e2 _
      try wp_auto
      ispecialize HΦ $$ %(W64 0) %(GoInterface.ok e2)
      iapply HΦ; iframe
      ipureintro; intro h; cases h
    · try wp_auto
      ispecialize HΦ $$ %(W64 bs.length) %GoInterface.nil
      iapply HΦ; iframe
      ipureintro; intro _
      refine ⟨rfl, ?_⟩
      word

end proof

end bbolt
end EtcdGrove
end Perennial
