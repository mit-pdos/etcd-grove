/- Lean-first (no Rocq counterpart). (2026-10-20, witness support)

`s.Close()` (witness.go): nothing.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.DefsWitness

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kv

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]

abbrev WitnessStore.Close.spec : Prop :=
  ∀ (s : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kv }}
    (App (Val (s @!! go.GoType.PointerType rWStoreTy @!! go!"Close")) (Val #()))
  {{ RET #(); True }}

end spec

end kv
end EtcdGrove
end Perennial
