/-
`partitioner(srvs, sched)` (`examples/linkv3p/linkv3p.go`; the partition plan's S3a,
2026-10-20): for each step of the schedule `sched`, after its delay (`time.Sleep`), the link
between members `A` and `B` of `srvs` cut (`EtcdServer.CutPeer`, both directions) or mended
(`MendPeer`); a step whose indices are out of range or equal does nothing. Lean-first (no Rocq
counterpart).

**The triple:** over the read-only slices of servers `ss` and steps, each server a member of the
network `γn` (`srvNetMember`, which `startMember` returns in `memberServed` and `CutPeer`/
`MendPeer`'s specs take; `MemberID` reads the member id it carries): it returns. Nothing is
assumed of the schedule: the theorem that runs it (`Main`) quantifies over every one.
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
  ∀ (γn : NetNames GF) (srvs sched : GoSlice) (ss : List Loc)
    (steps : List github_com.mit_pdos.etcd_grove.examples.linkv3p.Step),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.linkv3p ∗
      srvs ↦*□ ss ∗ sched ↦*□ steps ∗ ([∗list] s ∈ ss, ∃ id : w64, srvNetMember γn s id) }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.linkv3p.partitioner))
      (Val #srvs)) (Val #sched))
  {{ RET #(); True }}

end spec

end linkv3p
end EtcdGrove
end Perennial
