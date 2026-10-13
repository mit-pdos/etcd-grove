/- Lean-first (no Rocq counterpart, 2026-10-13). -/
module

public import Spec.go_etcd_io.raft.v3.raft__hardState
public import Spec.go_etcd_io.raft.v3.raft__softState

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section defs
variable [FfiSyntax]

/-- The `BasicStatus` of a node `id` in physical state `s`: its id, `r.hardState()`,
`r.softState()`, `r.raftLog.applied` and `r.leadTransferee` (`NState.lt`). -/
def basicStatusOf (id : w64) (s : NState) : BasicStatus :=
  BasicStatus.mk id (hardstateVal (nodeHardstate s)) (softstateVal (nodeSoftstate s))
    s.logst.applied s.lt

end defs

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `getBasicStatus(r)` (status.go:56): reads only; returns `basicStatusOf id s`. -/
abbrev getBasicStatus.spec : Prop :=
  ∀ (cfg : GSet w64) (r : Loc) (id : w64) (s : NState),
  {{ ownRaftPhys (GF := GF) cfg r id s }}
    (App (Val #(functions getBasicStatus [])) (Val #r))
  {{ RET #(basicStatusOf id s); ownRaftPhys cfg r id s }}

end spec

end EtcdGrove
end Perennial
