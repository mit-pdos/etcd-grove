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

/-- **A lease meeting the grant guard `GA` may be granted.** -/
theorem leaseGranted_of_guard (γl : GName) (GA : w64 → IProp GF) (id : w64) :
    lessorGuard γl GA ∗ □ GA id ⊢ leaseGranted γl id := by
  iintro ⟨#Hg, #Hid⟩
  iunfold leaseGranted
  iexists GA
  iframe #

end laws

end lease
end EtcdGrove
end Perennial
