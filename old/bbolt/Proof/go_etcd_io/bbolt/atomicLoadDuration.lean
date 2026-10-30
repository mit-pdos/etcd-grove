module
public import Spec.go_etcd_io.bbolt.atomicLoadDuration
public import Proof.go_etcd_io.bbolt.Atomics

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

theorem atomicLoadDuration.wp_proof : atomicLoadDuration.spec (GF := GF) (hG := hG) := by
  intro ptr dq v
  wp_start as Hp
  ihave #Hatomic : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_LoadInt64_own $$ [$Hp] as Hp
  iapply HΦ $$ Hp

end proof

end bbolt
end EtcdGrove
end Perennial
