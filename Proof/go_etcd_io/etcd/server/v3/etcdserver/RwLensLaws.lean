/-
**The write right's lens law** (mvccfull's Probe, 2026-11-09, the unfold list): a resource lends
itself, for a client whose write right is exactly what a contract's writes take. In a module of its
own, so that adding it leaves `InvRest` (and its importers) as they were.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRest

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`X` lends itself.** -/
theorem rwLens_refl (X : IProp GF) : ⊢ rwLens X X := by
  iunfold rwLens
  iintro !> H
  iframe H
  iintro H
  iexact H

end laws

end EtcdGrove
end Perennial
