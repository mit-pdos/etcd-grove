/-
The coordinator package's sealed slots (stage 1 interface: their names; their bodies are the coordinator package's).
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Coord.Defs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

namespace github_com.despreston.go_craq

attribute [local instance] GooseGlobalGS.gooseInvGS

section slots
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [examples.craqnet.Assumptions] [store.Assumptions] [store.kv.Assumptions] [transport.Assumptions] [transport.netrpc.Assumptions] [node.Assumptions] [coordinator.Assumptions]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]
variable [ra : RpcHttpAddr GF]

/-- The coordinator `c` (persistent; coordinator package). Intended: the fields read without the
lock are persistent (`tport`, `Updates`, the `mu`; per replica node struct, `rpc` (a client of its
address) and `address`); the lock invariant holds `replicas` (a slice of node pointers whose
addresses are distinct chain addresses), `version` with `nextHalf`, `head`, `tail`, each replica's
`connected` flag and, while connected, the coordinator's half of its role: the last replica is
the active tail, the others are not, each records its successor's address (the next replica's,
or none for the last); per chain address not joined, its role half `(false, "")` (or the join
ticket already received, for an address whose AddNode failed: tickets are exclusive); no replica
ever ⇒ `tailTok γ []` (the first AddNode's source is none: `srcOk ""`). -/
def isCoord (cfg : Cfg GF) (c : Loc) : IProp GF :=
  iprop(craqCtx cfg ∗ isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.coordinator ∗
    coordDef cfg c)

instance isCoord_persistent (cfg : Cfg GF) (c : Loc) :
    Persistent (isCoord (hG := hG) cfg c) := by
  unfold isCoord; infer_instance


end slots

end github_com.despreston.go_craq

end Perennial
