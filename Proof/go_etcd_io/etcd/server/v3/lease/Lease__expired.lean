/-
Proof of `Spec/go_etcd_io/etcd/server/v3/lease/Lease__expired.lean` (prove-ps2-renew, 2026-11-21):
`Remaining()`'s comparison with `0`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.Lease__expired
public import Spec.go_etcd_io.etcd.server.v3.lease.Lease__Remaining

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.lease lease

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

theorem lease.Lease.expired.wp_proof
    (hRem : lease.Lease.Remaining.spec (GF := GF) (hG := hG)) :
    lease.Lease.expired.spec (GF := GF) (hG := hG) := by
  intro γl l
  wp_start as ⟨#Hlo, Htt, %Hb⟩
  wp_auto
  wp_apply (hRem γl l) $$ [$Hpkg $Hlo $Htt] as %d Htt
  · ipureintro; exact Hb
  (try wp_auto)
  iapply HΦ
  iexact Htt

end proof

end EtcdGrove
end Perennial
