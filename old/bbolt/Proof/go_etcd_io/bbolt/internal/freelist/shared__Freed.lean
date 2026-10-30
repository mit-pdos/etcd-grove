module
public import Spec.go_etcd_io.bbolt.internal.freelist.shared__Freed

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.freelist

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

theorem shared.Freed.wp_proof : shared.Freed.spec (GF := GF) (hG := hG) := by
  intro s iface σ id
  wp_start as Hs
  unfold ownShared ownSharedC
  icases Hs with ⟨%sv, %c, Hs, %Hok⟩
  iNamed Hs
  wp_auto
  wp_apply wp_map_lookup2 $$ [Hcache] as Hcache
  · iexact Hcache
  try wp_auto
  rw [show decide ((c !! id).isSome = true) = decide (σ.cached id) from
    decide_eq_decide.2 (Hok.1 id)]
  iapply HΦ
  iexists sv, c
  iframe
  ipureintro; exact ⟨Hiface, Hok⟩

end proof

end bbolt
end EtcdGrove
end Perennial
