/-
Proof of `Spec/Cache__RequestProgress.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.Cache__RequestProgress
public import Spec.go_etcd_io.etcd.cache.v3.demux__BroadcastProgress

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

set_option linter.unusedSectionVars false

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem Cache.RequestProgress.wp_proof
    (wp_BroadcastProgress : demux.BroadcastProgress.spec (GF := GF) (hG := hG)) :
    Cache.RequestProgress.spec (GF := GF) (hG := hG) := by
  intro c cf γr γd cap ctx
  wp_start as ⟨Hc, Hh⟩
  iNamed Hc
  wp_auto
  wp_apply wp_BroadcastProgress $$ [$HisDemux $Hh] as Hh
  wp_end

end proof

end EtcdGrove
end Perennial
