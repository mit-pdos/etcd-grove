/- Lean-first (no Rocq counterpart).

`newKV(id, node, storage, send, w)` (kv.go:119, 2026-10-20, witness support): `New` with the
replica's access to the cluster's witness, specified for none (`w = nil`, a cluster without a
witness: what `New` passes); the witness case is not specified yet (W4). Otherwise `New`'s
spec: replica `id` on its running node (the
driver's token at the empty committed log) and its storage; it starts `run`. Since
2026-10-15 (stage N) the node is in raft's dynamic mode (`KVCC`: the cluster's conf changes are
`op`), with the driver's view of its configuration (`nodeCfg`), which `run` keeps. The replica's
seq token (`id ↪[γr.seq] 0`, from the cluster's allocation) starts its sequence numbers.
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvwitness.Assumptions]
variable [KVStor GF]

/-- See the file header. -/
abbrev newKV.spec : Prop :=
  ∀ (γr : RKVNames) (γn : NodeNames) (id : w64) (n st : Loc) (send : GoFunc) (op : CCOp)
    (c0 c1 : CCState) (wi : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvwitness ∗ rkvInv γr ∗ nodeDriver γn id n [] ∗ ⌜γn.raft = γr.raft⌝ ∗
      -- (2026-10-15, stage N) the node in the dynamic mode of a cluster whose conf changes are
      -- `op` (`KVCC`), and the driver's view of its configuration, the initial one; (2026-10-20,
      -- W4) or in the static mode of a cluster that admits no conf change (`KVCCS`)
      ⌜KVCC γn op c0 c1 ∨ KVCCS γn⌝ ∗ nodeCfg γn 0 c0 ∗
      ⌜γn.stor = kvStorIface st⌝ ∗ (∃ (ms : Loc) (γs : MemStorNames), kvStorRec st ms γs) ∗ isCommitted γr.raft [] ∗ id ↪[γr.seq] (W64 0) ∗
      sendSpec send γn ∗
      -- (2026-10-20, W4) the replica's access to the witness, if any (`nil`: none)
      kvWitRes γn id wi }}
    (App (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.kvwitness.newKV))
      (Val #id)) (Val #(interface.mkOk (go.GoType.PointerType node.ty) #n))) (Val #st))
      (Val #send)) (Val #wi))
  {{ (r : Loc), RET #r; ∃ γp : RepNames, ⌜γp.node = γn⌝ ∗ isKV γr γp r }}

end spec

end kvwitness
end EtcdGrove
end Perennial
