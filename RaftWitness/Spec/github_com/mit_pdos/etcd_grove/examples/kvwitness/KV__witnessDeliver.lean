/- Lean-first (no Rocq counterpart). (2026-10-20, witness support)

`r.witnessDeliver(ms)` (kv.go): the node's witness messages, passed to the witness through the
replica's access to it, each deliverable answer stepped into the node. Without one (`r.witness`
nil, a cluster without a witness) it returns at once. (2026-10-20, W4) With one (`kvWitRes`: a
`Witness` of the cluster's witness, its storage's terms within the term budget), `ms` the
requests a `Ready` handed out (`readyWit`: each legitimately sent, from the node, to the cluster's
witness, within the budget): each answer (`Witness.Process`, `witness.Process.ghostSpecT`) is
legitimate, to the node, from the witness and within the budget, so `Node.Step` takes it
(`stepP`); the access is given back.
-/
module

public import RaftWitness.Proof.github_com.mit_pdos.etcd_grove.examples.kvwitness.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvwitness

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvwitness.Assumptions]
variable [StorageModel GF]

abbrev KV.witnessDeliver.spec : Prop :=
  ∀ (r : Loc) (rd : Ready) (wi : GoInterface) (γn : NodeNames) (id : w64) (n : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvwitness ∗
      r.[RKV, go!"witness"] ↦□ wi ∗ kvWitRes γn id wi ∗
      r.[RKV, go!"node"] ↦□ interface.mkOk (go.GoType.PointerType node.ty) #n ∗
      isNode γn id n ∗ readyWit γn id rd }}
    (App (Val (r @!! go.GoType.PointerType rKVTy @!! go!"witnessDeliver"))
      (Val #rd.WitnessMessages'))
  {{ RET #(); kvWitRes γn id wi }}

end spec

end kvwitness
end EtcdGrove
end Perennial
