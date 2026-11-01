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

/-- `getStatus(r)` (status.go:68): a `Status` whose memory is the caller's (`statusOwnRaw`: the
fresh hard state, a clone of the configuration, at a leader a copy of the progresses); the raft
struct unchanged. -/
abbrev getStatus.spec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhysCV c c.voters r id s }}
    (App (Val #(functions getStatus [])) (Val #r))
  {{ (st : Status), RET #st; statusOwnRaw st ∗ ownRaftPhysCV c c.voters r id s }}

end spec

end EtcdGrove
end Perennial
