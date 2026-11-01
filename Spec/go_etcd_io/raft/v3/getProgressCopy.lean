/- Lean-first (no Rocq counterpart, 2026-10-29, stage U7). -/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys
public import Proof.go_etcd_io.raft.v3.InvStatus

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `getProgressCopy(r)` (status.go:43): a fresh map of copies of the tracker's progresses, each
with a clone of its `Inflights` (`progCopyOwn`); the raft struct unchanged. -/
abbrev getProgressCopy.spec : Prop :=
  ∀ (c : CfgM) (V : GSet w64) (r : Loc) (id : w64) (s : NState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhysCV c V r id s }}
    (App (Val #(functions getProgressCopy [])) (Val #r))
  {{ (m : GoMap), RET #m; progCopyOwn m ∗ ownRaftPhysCV c V r id s }}

end spec

end EtcdGrove
end Perennial
