/-
Proof of `Spec/go_etcd_io/etcd/client/v3/ensureWatchHeader.lean` (the watch slice's unit W-C). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.ensureWatchHeader

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3 client

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem ensureWatchHeader.wp_proof : ensureWatchHeader.spec (GF := GF) (hG := hG) := by
  intro hdr
  wp_start
  wp_auto
  wp_if_destruct
  · irename «$r0» => Hh
    generalize «$r0_ptr» = h at *
    ihave %Hhn := typedPointsto_not_null _ _ _ $$ Hh
    iapply HΦ
    isplitl []
    · ipureintro; exact Hhn
    iright; iframe
  · iapply HΦ; isplitl []
    · ipureintro; assumption
    ileft; ipureintro; exact ⟨by assumption, rfl⟩

end proof

end EtcdGrove
end Perennial
