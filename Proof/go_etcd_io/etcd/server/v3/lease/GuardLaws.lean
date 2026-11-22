/-
**The grant guard's law** (mvccfull's Probe, 2026-11-09, the unfold list): a lease meeting the
lessor's grant guard may be granted, for a client that chose the guard (`NewLessor`'s `GA`) and
lists the leases it admits. In a module of its own, so that adding it leaves `InvLessor` (and its
importers) as they were.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.InvLessor

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lease

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.lease

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

/-- **A lease meeting the grant guard `GA` may be granted.** -/
theorem leaseGranted_of_guard (γl : GName) (GA : w64 → IProp GF) (id : w64) :
    lessorGuard γl GA ∗ □ GA id ⊢ leaseGranted γl id := by
  iintro ⟨#Hg, #Hid⟩
  iunfold leaseGranted
  iexists GA
  iframe #


/-- **A granted lease meets the grant guard**, after a step (the saved predicates agree under a
later): what the expiry loop's send on `expiredC` gives of each lease it sends. -/
theorem guard_of_granted (γl : GName) (GA : w64 → IProp GF) (id : w64) :
    lessorGuard (GF := GF) γl GA ∗ leaseGranted γl id ⊢ ▷ GA id := by
  iintro ⟨#Hg, #Hgr⟩
  iunfold leaseGranted at Hgr
  icases Hgr with ⟨%GA', #Hg', #HA⟩
  iunfold lessorGuard at Hg Hg'
  icases Hg with ⟨%lp, %a, %b, #Hp, #Hs⟩
  icases Hg' with ⟨%lp', %a', %b', #Hp', #Hs'⟩
  ihave %E := lessorPinG_agree γl lp lp' a a' b b' $$ [$Hp $Hp']
  obtain ⟨-, rfl, -⟩ := E
  ihave #Heq := saved_pred_agree a DFrac.discard DFrac.discard GA' GA id $$ Hs' Hs
  inext
  ihave Hiff := internalEq_iff _ _ $$ Heq
  icases Hiff with ⟨Hiff, -⟩
  iapply Hiff $$ HA

end laws

end lease
end EtcdGrove
end Perennial
