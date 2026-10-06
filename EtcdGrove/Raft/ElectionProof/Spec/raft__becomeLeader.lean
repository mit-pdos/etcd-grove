/-
Port of `election_proof/spec_raft__becomeLeader.v`.

Lean notes:
* Rocq's `become_leader id s <| nstate.prvals := pvs |>` is
  `{ becomeLeader id s with prvals := pvs }`, and the type of the untyped binder `pvs`
  is written out.
-/
import EtcdGrove.Raft.ElectionProof.InvRaftPhys

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `becomeLeader` is `reset`, the role transition, marking its own `Progress`
replicating, and the empty entry. `id ∈ cfg` is needed because only voters are in the
`Progress` map. -/
abbrev raft.becomeLeader.spec : Prop :=
  ∀ (cfg : GSet w64) (r : Loc) (id : w64) (s : NState),
  s.role ≠ .follower →
  id ∈ cfg →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhys cfg r id s }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"becomeLeader")) (Val #()))
  {{ (pvs : GMap w64 (tracker.Progress × tracker.Inflights)), RET #();
      ownRaftPhys cfg r id { becomeLeader id s with prvals := pvs } }}

end spec

end EtcdGrove
end Perennial
