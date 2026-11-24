/-
The proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/bootstrapStorage.lean` (claim #34, stage 4,
2026-11-25): `wal == nil`, so `bootstrapNewWAL` (`bootstrapNewWAL.spec`), then the record. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.bootstrapStorage
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.bootstrapNewWAL

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem bootstrapStorage.wp_proof (hNew : bootstrapNewWAL.spec (GF := GF) (hG := hG)) :
    bootstrapStorage.spec (GF := GF) (hG := hG) := by
  intro cfg bkl c bc dq dqc cid Hnf
  wp_start as ⟨#Hzlg, Hwp, Hc, Hcid⟩
  wp_auto
  wp_apply (hNew cfg c bc dq dqc cid Hnf) $$ [Hwp Hc Hcid]
    as %w ⟨%bw, Hw, %Hbw, Hboot, Hc, Hcid⟩
  · iframe Hwp Hc Hcid; iframe #
  try wp_auto
  iapply HΦ
  iexists (bootstrappedStorage.mk bkl w), bw
  iframe
  ipureintro
  exact ⟨rfl, Hbw⟩

end proof

end EtcdGrove
end Perennial
