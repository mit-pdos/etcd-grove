/-
`(*witness).Close` (raft#168, `witness.go`; 2026-10-20, witness support, W3b).
-/
module

public import Proof.go_etcd_io.raft.v3.InvWitnessStorage

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

/-- `w.Close()`: the storage's `Close`; the witness unchanged. -/
abbrev witness.Close.spec : Prop :=
  ∀ (w : Loc) (id : w64) (s : GoInterface) (cq pv : Bool) (c : WHS) (h : Bool)
    (N : Namespace) (P : WHS → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      ownWitness w id s cq pv c h ∗ isWitnessStorage s N P }}
    (App (Val (w @!! go.GoType.PointerType witness.ty @!! go!"Close")) (Val #()))
  {{ RET #(); ownWitness w id s cq pv c h }}

end spec

end EtcdGrove
end Perennial
