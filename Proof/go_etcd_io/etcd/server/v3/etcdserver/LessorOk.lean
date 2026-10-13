/-
The server's lessor contract (`lessorOk`: `Promote`, `Demote`, `ExpiredLeasesC`) of the real
lessor (2026-10-13, unit 9 of the backend). Lean-first (no Rocq counterpart); see
`Proof/go_etcd_io/etcd/server/v3/lease/InvLessor.lean`.

`lessorOk_of_lessorInv`: the lessor at `lp` (`lease.lessorInv`, its configuration and its
`expiredC`, `lease.lessorExpiredC`) meets `lessorOk`, from the specs of `Promote` and `Demote`
(trust-boundary axioms: float arithmetic, a float-to-integer conversion and `sort.Sort`; the
close of `demotec`) and the proof of `ExpiredLeasesC`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Promote
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Demote
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__ExpiredLeasesC

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The server's lessor contract, of the real lessor** at `lp`. -/
theorem lessorOk_of_lessorInv
    (hPromote : lease.lessor.Promote.spec (GF := GF) (hG := hG))
    (hDemote : lease.lessor.Demote.spec (GF := GF) (hG := hG))
    (hExp : lease.lessor.ExpiredLeasesC.spec (GF := GF) (hG := hG))
    (lp : Loc) (γl : GName) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗
      lease.lessorInv lp γl ∗ lease.lessorCfg lp ∗ lease.lessorExpiredC lp ⊢
      lessorOk (lease.lessorIface lp) := by
  iintro ⟨#Hpkg, #Hinv, #Hcfg, #Hexp⟩
  iunfold lessorOk
  iexists (interface.mk (go.GoType.PointerType lease.lessor.ty) #lp)
  isplitr
  · ipureintro; rfl
  isplitr
  · iintro !> %d %Φ !> - HΦ
    iapply (hPromote lp γl d) $$ [] HΦ
    iframe #
  isplitr
  · iintro !> %Φ !> - HΦ
    iapply (hDemote lp γl) $$ [] HΦ
    iframe #
  · iintro !> %Φ !> - HΦ
    iapply (hExp lp) $$ [] HΦ
    iframe #

end proof

end EtcdGrove
end Perennial
