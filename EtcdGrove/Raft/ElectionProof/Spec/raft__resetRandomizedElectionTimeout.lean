/- Port of election_proof/spec_raft__resetRandomizedElectionTimeout.v (feb5c73d4). -/
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

/-- `resetRandomizedElectionTimeout` draws from the global RNG and writes
`r.randomizedElectionTimeout`. The *RNG* is outside core raft and is assumed
(`Spec/rand_Int.lean`); this wrapper is raft code, so it is a theorem. The field it
writes appears in no other conjunct of `ownRaftPhys`, and the model has no clock, so
the new value is existential.

`0 < electionTimeout` is not optional. The body is
`r.electionTimeout + globalRand.Intn(r.electionTimeout)`, and `lockedRand.Intn` reaches
`crypto/rand.Int`, which **panics** on a non-positive bound -- so without the premise
the triple is false at `electionTimeout ≤ 0`. Raft establishes it in `Config.validate`
(`ElectionTick > HeartbeatTick > 0`) and `ownRaftPhys` carries it as
`HelectionTimeout`; `reset` passes it through. Added 2026-09-20. -/
abbrev raft.resetRandomizedElectionTimeout.spec : Prop :=
  ∀ (cfg : GSet w64) (r : Loc) (id : w64) (s : NState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhys cfg r id s }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"resetRandomizedElectionTimeout"))
      (Val #()))
  {{ RET #(); ownRaftPhys cfg r id s }}

end spec

end EtcdGrove
end Perennial
