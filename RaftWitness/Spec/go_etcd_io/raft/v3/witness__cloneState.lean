/-
`(*witness).cloneState` (raft#168, `witness.go`; 2026-10-20, witness support).
-/
module

public import Proof.go_etcd_io.raft.v3.InvWitness

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

/-- `w.cloneState()`: a fresh witness state holding `w.state`'s (nil read as the zero state),
owned (with a hard state), its replication sets fresh copies. (Until fork `9ed005d46` a nil
`w.state` panicked: `notes/raft-witness-vs-pr168/getstate-nil.md`.) -/
abbrev witness.cloneState.spec : Prop :=
  ∀ (w : Loc) (dq : DFrac) (p : Loc) (σ : WHS),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      w.[witness, go!"state"] ↦{dq} p ∗ whsOpt p σ }}
    (App (Val (w @!! go.GoType.PointerType witness.ty @!! go!"cloneState")) (Val #()))
  {{ (q : Loc), RET #q; w.[witness, go!"state"] ↦{dq} p ∗ whsOwn q σ }}

end spec

end EtcdGrove
end Perennial
