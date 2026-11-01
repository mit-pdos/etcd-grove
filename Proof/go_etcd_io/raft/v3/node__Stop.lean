/- Lean-first (no Rocq counterpart), 2026-10-29 (stage U9a). -/
module

public import Spec.go_etcd_io.raft.v3.node__Stop
public import Proof.go_etcd_io.raft.v3.InvNodeChan
import all Proof.go_etcd_io.raft.v3.InvNodeChan
import all Proof.go_etcd_io.raft.v3.InvNode
import Proof.go_etcd_io.raft.v3.LemmasP5NodeErr
import Proof.go_etcd_io.raft.v3.InvApi

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-! ## The raw triple (internal: private to this file)

`select { case n.stop <- struct{}{}: case <-n.done: return }; <-n.done`: the client's half of
`live` goes to `run` on `stop` (`isNodeChan`'s `Hstop`), which closes `done` once stopped
(`node_done_recv_au`); if `done` fired first, the node had stopped already. -/

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the header above. -/
private abbrev node.Stop.specRaw : Prop :=
  ∀ (γ : NodeNames) (id : w64) (n : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNodeChan γ id n ∗
      nodeLiveRaw γ 1 }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"Stop")) (Val #()))
  {{ RET #(); nodeStoppedRaw γ }}

end spec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

private theorem node.Stop.wp_raw : node.Stop.specRaw (GF := GF) (hG := hG) := by
  -- PORT(durability stage II): a definition or statement it uses changed (durability stage I-2..I-8)
  sorry

end proof

/-! ## The spec, from the raw triple -/

namespace ApiImpl

section wrap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `node.Stop.spec` from the raw triple: the names are `nodeRunning`'s (`isNode`'s are not
needed). -/
private theorem node.wp_Stop_impl
    (hS : EtcdGrove.node.Stop.specRaw (GF := GF) (hG := hG)) :
    EtcdGrove.node.Stop.spec (GF := GF) (hG := hG) := by
  -- PORT(durability stage II): a definition or statement it uses changed (durability stage I-2..I-8)
  sorry

end wrap

end ApiImpl

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem node.Stop.wp_proof : node.Stop.spec (GF := GF) (hG := hG) :=
  ApiImpl.node.wp_Stop_impl node.Stop.wp_raw

end proof

end EtcdGrove
end Perennial
