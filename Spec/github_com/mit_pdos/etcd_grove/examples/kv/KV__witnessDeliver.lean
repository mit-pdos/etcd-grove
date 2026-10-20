/- Lean-first (no Rocq counterpart). (2026-10-20, witness support)

`r.witnessDeliver(ms)` (kv.go): the node's witness messages, passed to the witness through the
replica's access to it. Specified for a replica without one (`r.witness` nil, a cluster without a
witness): it returns at once. The witness case is not specified yet (W4).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.Defs

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

abbrev KV.witnessDeliver.spec : Prop :=
  ∀ (r : Loc) (ms : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kv ∗
      r.[RKV, go!"witness"] ↦□ (interface.nil : GoInterface) }}
    (App (Val (r @!! go.GoType.PointerType rKVTy @!! go!"witnessDeliver")) (Val #ms))
  {{ RET #(); True }}

end spec

end kv
end EtcdGrove
end Perennial
