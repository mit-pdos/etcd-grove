/-
Proof of the spec of the same name (the request path's unit 4d).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.schedule.job__Do

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.pkg.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.schedule.Assumptions]

theorem schedule.job.Do.wp_proof : schedule.job.Do.spec (GF := GF) (hG := hG) := by
  intro γ jv ctx cd Pre Prev Post
  wp_start as ⟨#Hf, Hrun, HPre, HPrev, Hctx⟩
  wp_auto
  iunfold jobFnSpec at Hf
  wp_bind (App (Val #jv.do') (Val #(GoInterface.ok ctx)))
  iapply Hf $$ %ctx %cd [Hrun HPre HPrev Hctx]
  · iframe
  inext
  iintro Hpost
  wp_auto
  iapply HΦ
  iexact Hpost


end proof

end EtcdGrove
end Perennial
