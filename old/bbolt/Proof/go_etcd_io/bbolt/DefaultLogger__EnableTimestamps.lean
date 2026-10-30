module
public import Spec.go_etcd_io.bbolt.DefaultLogger__EnableTimestamps
public import Spec.log.Logger__Flags
public import Spec.log.Logger__SetFlags

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

theorem DefaultLogger.EnableTimestamps.wp_proof
    (hFlags : log.Logger.Flags.spec (GF := GF) (hG := hG))
    (hSetFlags : log.Logger.SetFlags.spec (GF := GF) (hG := hG)) :
    DefaultLogger.EnableTimestamps.spec (GF := GF) (hG := hG) := by
  intro dl ll d dq
  wp_start as ⟨Hdl, #Hlog⟩
  wp_auto
  wp_method_call
  try wp_auto
  wp_apply hFlags ll $$ [Hlog] as %fl _
  · iexact Hlog
  try wp_auto
  wp_method_call
  try wp_auto
  wp_apply hSetFlags ll _ $$ [Hlog]
  · iexact Hlog
  try wp_auto
  iapply HΦ; iframe

end proof

end bbolt
end EtcdGrove
end Perennial
