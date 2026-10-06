/-
Port of `election_proof/spec_raft__reset.v`.
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

/-- `reset term` clears the vote iff the term changes, clears `lead` and the vote
tally, and re-initializes the non-election state; `resetTo` (`Defs.lean`) is exactly
that. `r.step` is untouched, so `becomeFollower` -- which assigns it *before* calling
`reset` -- gets it back as it left it. -/
abbrev raft.reset.spec : Prop :=
  ∀ (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (term : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhys cfg r id s }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"reset")) (Val #term))
  {{ (pvs : GMap w64 (tracker.Progress × tracker.Inflights)), RET #();
      ownRaftPhys cfg r id { resetTo s term with prvals := pvs } }}

end spec

end EtcdGrove
end Perennial
