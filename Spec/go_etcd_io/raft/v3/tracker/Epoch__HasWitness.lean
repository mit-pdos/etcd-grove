/-
`(*Epoch).HasWitness` (raft#168, `tracker/tracker.go`; 2026-10-19, witness support).
-/
module

public import Proof.go_etcd_io.raft.v3.InvTracker

@[expose] public section

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

/-- `e.HasWitness()` of a witness-free epoch is `false`. -/
abbrev tracker.Epoch.HasWitness.spec : Prop :=
  ∀ (e : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ ownEpochNW e }}
    (App (Val (e @!! go.GoType.PointerType tracker.Epoch.ty @!! go!"HasWitness")) (Val #()))
  {{ RET #false; True }}

end spec

end EtcdGrove
end Perennial
