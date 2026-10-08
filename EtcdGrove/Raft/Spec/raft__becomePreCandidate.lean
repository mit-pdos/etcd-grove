/-
Port of election_proof/spec_raft__becomePreCandidate.v (feb5c73d4).

Lean notes:
* `become_precandidate` is `becomePrecandidate` (`Defs.lean`); `prole.Leader` is
  `PRole.leader`.
-/
import EtcdGrove.Raft.InvRaftPhys

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `becomePreCandidate` (raft.go:912, 2026-10-04): `r.step := stepCandidate`,
`r.trk.ResetVotes()`, `r.tick`, `r.lead := None`, `r.state := StatePreCandidate`, and a
log line. Term and vote are untouched and there is no `reset`, so the `Progress` values
stay (`becomePrecandidate`, `Defs.lean`). The panic branch (`state = StateLeader`) is
discharged from the role premise. -/
abbrev raft.becomePreCandidate.spec : Prop :=
  ∀ (cfg : GSet w64) (r : Loc) (id : w64) (s : NState),
  s.role ≠ .leader →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhys cfg r id s }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"becomePreCandidate"))
      (Val #()))
  {{ RET #(); ownRaftPhys cfg r id (becomePrecandidate s) }}

end spec

end EtcdGrove
end Perennial
