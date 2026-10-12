module
public import Spec.go_etcd_io.bbolt.DefaultLogger__Info
public import Spec.fmt.Sprint
public import Spec.go_etcd_io.bbolt.header
public import Spec.log.Logger__Output

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

theorem DefaultLogger.Info.wp_proof
    (hSprint : fmt.Sprint.spec (GF := GF) (hG := hG))
    (hheader : header.spec (GF := GF) (hG := hG))
    (hOutput : log.Logger.Output.spec (GF := GF) (hG := hG)) :
    DefaultLogger.Info.spec (GF := GF) (hG := hG) := by
  intro dl v
  wp_start as #Hdl
  simp only [defaultLoggerOK]
  icases Hdl with ⟨%ll, #Hll, #Hlog⟩
  wp_auto
  wp_apply hSprint as %s _
  wp_apply hheader as %h _
  try wp_auto
  wp_method_call
  try wp_auto
  wp_apply hOutput ll _ h $$ [Hlog] as %e _
  · iexact Hlog
  try wp_auto
  iapply HΦ; itrivial

end proof

end bbolt
end EtcdGrove
end Perennial
