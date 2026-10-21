/- Lean-first (no Rocq counterpart). (2026-10-20, witness support)

`NewWitnessStore()` (witness.go): a store holding the zero state (`&WitnessHardState{State:
&HardState{}}`, read-only, `WHS.zero`), for any ghost counterpart `P` of its state, given at
the zero state; and the value of raft's `ErrWitnessStateModified` (`wErrOk`, see
`DefsWitness.lean`).
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

abbrev NewWitnessStore.spec : Prop :=
  ∀ (P : WHS → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvwitness ∗ wErrOk ∗ P WHS.zero }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.kvwitness.NewWitnessStore)) (Val #()))
  {{ (s : Loc), RET #s; isWStore s P }}

end spec

end kvwitness
end EtcdGrove
end Perennial
