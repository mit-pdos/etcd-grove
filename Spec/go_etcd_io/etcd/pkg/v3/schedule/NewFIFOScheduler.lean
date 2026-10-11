/-
`schedule.NewFIFOScheduler`: the trust boundary (`pkg/v3/schedule` is names-only). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Base
public import GeneratedProof.go_etcd_io.etcd.pkg.v3.schedule

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.pkg.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `schedule.NewFIFOScheduler(lg)` returns a scheduler (a `Scheduler` interface value; the
store keeps it for the compaction, out of scope). -/
abbrev schedule.NewFIFOScheduler.spec : Prop :=
  ∀ (lg : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.schedule }}
    (App (Val (@! schedule.NewFIFOScheduler)) (Val #lg))
  {{ (sc : GoInterface), RET #sc; True }}

end spec

end EtcdGrove
end Perennial
