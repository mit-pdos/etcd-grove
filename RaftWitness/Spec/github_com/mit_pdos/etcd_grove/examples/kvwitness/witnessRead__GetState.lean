/- Lean-first (no Rocq counterpart). (2026-10-20, witness support)

`r.GetState()` (witness.go): the state the read saw.
-/
module

public import RaftWitness.Proof.github_com.mit_pdos.etcd_grove.examples.kvwitness.DefsWitness

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvwitness

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvwitness.Assumptions]

abbrev witnessRead.GetState.spec : Prop :=
  ∀ (r s : Loc) (P : WHS → IProp GF) (p : Loc) (σ : WHS),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvwitness ∗ isWRead r s P p σ }}
    (App (Val (r @!! go.GoType.PointerType rWReadTy @!! go!"GetState")) (Val #()))
  {{ RET #p; True }}

end spec

end kvwitness
end EtcdGrove
end Perennial
