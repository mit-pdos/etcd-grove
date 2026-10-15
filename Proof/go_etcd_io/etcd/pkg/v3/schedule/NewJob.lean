/-
Proof of the spec of the same name (the request path's unit 4d): the `job{name, do}` struct as a
`Job` interface value, whose `Do` is `job.Do`'s (its spec, the callee).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.schedule.NewJob
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

theorem schedule.NewJob.wp_proof (hDo : schedule.job.Do.spec (GF := GF) (hG := hG)) :
    schedule.NewJob.spec (GF := GF) (hG := hG) := by
  intro γ name f Pre Prev Post
  wp_start as #Hf
  wp_auto
  iapply HΦ
  iunfold jobIs
  iexists interface.mk schedule.job.ty #({ name' := name, do' := f } : schedule.job)
  isplitr
  · ipureintro; rfl
  iunfold jobDoSpec
  imodintro
  iintro %ctx %cd %Φ'
  imodintro
  iintro ⟨Hrun, HPre, HPrev, Hctx⟩ HΦ'
  iapply (hDo γ { name' := name, do' := f } ctx cd Pre Prev Post) $$ [Hrun HPre HPrev Hctx] HΦ'
  iframe
  iframe #


end proof

end EtcdGrove
end Perennial
