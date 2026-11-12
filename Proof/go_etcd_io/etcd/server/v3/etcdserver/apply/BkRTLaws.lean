/-
**The backend reader token's law** (mvccfull's Probe, 2026-11-09, the unfold list): `bkRT`'s parts,
for a client that builds or splits one (a census giving the open share back, a new backend's reader
token). In a module of its own, so that adding it leaves `Contracts` (and its importers) as they
were.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Contracts

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apply

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **A reader token of the backend `B`** is a reader slot of its backend and a reader's open
share. -/
theorem bkRT_eq (B : mvcc.KBReal) :
    bkRT (GF := GF) B ⊣⊢ backend.rdTok B.γB B.P B.be ∗ backend.bOpen B.γB backend.rdOpen := by
  unfold bkRT; exact .rfl

end laws

end apply
end EtcdGrove
end Perennial
