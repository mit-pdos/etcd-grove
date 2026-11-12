/-
Proof of `Spec/go_etcd_io/etcd/server/v3/config/ServerConfig__MaxRequestBytesWithOverhead.lean`. Lean-first (no Rocq
counterpart); the watch slice's unit W-S (2026-10-14).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.config.ServerConfig__MaxRequestBytesWithOverhead

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem config.ServerConfig.MaxRequestBytesWithOverhead.wp_proof :
    config.ServerConfig.MaxRequestBytesWithOverhead.spec (GF := GF) (hG := hG) := by
  intro c m
  wp_start as #Hm
  wp_auto
  rw [show (W64 (512 * 1024) : w64) = W64 524288 from rfl]
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
