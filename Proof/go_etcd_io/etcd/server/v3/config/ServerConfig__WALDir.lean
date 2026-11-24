/-
Proof of `Spec/go_etcd_io/etcd/server/v3/config/ServerConfig__WALDir.lean` (claim #34, stage 3,
2026-11-23): with `DedicatedWALDir` non-empty the method returns it before `datadir.ToWALDir`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.config.ServerConfig__WALDir

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.config.Assumptions]

theorem config.ServerConfig.WALDir.wp_proof :
    config.ServerConfig.WALDir.spec (GF := GF) (hG := hG) := by
  intro c dq w hw
  wp_start as Hf
  wp_auto
  rw [decide_eq_false hw]
  wp_auto
  iapply HΦ
  iexact Hf

end proof

end EtcdGrove
end Perennial
