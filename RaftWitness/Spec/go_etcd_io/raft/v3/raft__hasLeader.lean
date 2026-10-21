/- Lean-first (no Rocq counterpart).

## `raft.hasLeader()` (raft.go:497)

`r.lead != None`, on the field alone: `node.go`'s `run` reads it with the raft struct open
in any of its states (`ownRawNode`, `ownRawNodeIdle`, `ownRawNodeReady`); the result is
not tracked (it only arms `run`'s proposal channel).
-/
module

public import Proof.go_etcd_io.raft.v3.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. -/
abbrev raft.hasLeader.spec : Prop :=
  ∀ (r : Loc) (ld : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ r.[raft, go!"lead"] ↦ ld }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"hasLeader")) (Val #()))
  {{ (b : Bool), RET #b; r.[raft, go!"lead"] ↦ ld }}

end spec

end EtcdGrove
end Perennial
