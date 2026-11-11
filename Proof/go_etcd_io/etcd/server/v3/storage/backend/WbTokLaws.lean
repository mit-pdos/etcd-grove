/-
**The write-back token's law** (mvccfull's Probe, 2026-11-09, the unfold list): `wbTok γ` is one of
the backend's write-back tokens `γ.wb`, for a client that keeps a stock of them or adds them up. In
a module of its own, so that adding it leaves `InvBackend` (and its importers) as they were.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBackend

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace backend

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- **A write-back token** is one of the tokens `γ.wb` (whose stock the constructor gives,
`wbInit` of them). -/
theorem wbTok_toks (γ : BNames) : wbTok (GF := GF) γ ⊣⊢ ownToks γ.wb 1 := by
  unfold wbTok; exact .rfl

end laws

end backend
end EtcdGrove
end Perennial
