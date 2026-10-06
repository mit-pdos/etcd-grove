/- Port of election_proof/spec_raft__becomeFollower.v. -/
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

/-- `becomeFollower` is `r.step := stepFollower`, `reset`, and assignments to `lead`
and `state`; `becomeFollower` (`Defs.lean`) is exactly that, `r.step` included. The
precondition says nothing about `r.step`: the function overwrites it first, which is
why `newRaft` can call this on a struct whose `step` is still nil. -/
abbrev raft.becomeFollower.spec : Prop :=
  ∀ (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (term lead : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhys cfg r id s }}
    (App (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"becomeFollower"))
      (Val #term)) (Val #lead))
  {{ (pvs : GMap w64 (tracker.Progress × tracker.Inflights)), RET #();
      ownRaftPhys cfg r id { becomeFollower s term lead with prvals := pvs } }}

end spec

end EtcdGrove
end Perennial
