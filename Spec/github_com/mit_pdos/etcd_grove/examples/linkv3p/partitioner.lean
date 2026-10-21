/-
`partitioner(srvs, brs, sched)` (`examples/linkv3p/linkv3p.go`; the partition plan's S3a,
2026-10-20; the client steps since 2026-10-21, `notes/client-cut-plan.md`): for each step of the
schedule `sched`, after its delay (`time.Sleep`), a peer step (`peerStep`: cut or mend the link
between members `A` and `B` of `srvs`) or a client step (`clientStep`: blackhole, unblackhole or
drop the connections of member `A`'s bridge in `brs`, a second blackhole skipped), by its kind;
any other kind does nothing. Lean-first (no Rocq counterpart).

**The triple:** over the read-only slices of servers `ss`, each a member of the network `γn`
(`srvNetMember`), of bridges `bs`, each owned and not blackholed (`ownBridge`), and of steps: it
returns. Nothing is assumed of the schedule: the theorem that runs it (`Main`) quantifies over
every one.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkv3p.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv3p

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkv3p.Assumptions]

/-- See the file header. -/
abbrev partitioner.spec : Prop :=
  ∀ (γn : NetNames GF) (srvs brs sched : GoSlice) (ss : List Loc) (bs : List GoInterface)
    (steps : List github_com.mit_pdos.etcd_grove.examples.linkv3p.Step),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.linkv3p ∗
      srvs ↦*□ ss ∗ brs ↦*□ bs ∗ sched ↦*□ steps ∗
      ([∗list] s ∈ ss, ∃ id : w64, srvNetMember γn s id) ∗
      ([∗list] br ∈ bs, ∃ addr : GoString, bridgeP.ownBridge br addr false) }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.linkv3p.partitioner))
      (Val #srvs)) (Val #brs)) (Val #sched))
  {{ RET #(); True }}

end spec

end linkv3p
end EtcdGrove
end Perennial
