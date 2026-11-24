/- Lean-first (no Rocq counterpart).

#33 S4: **`cloneMsg.law` from `proto.Clone`'s trust boundary** (`proto.ClonePb.spec`, at the
registered `*raftpb.Message` type `pbMessageC`, `pbMessageC_reg`), as rafthttp's
`streamWriter.run` clones its heartbeat: a frozen message without responses is read-only at its
content (`msgPtsCC_msgRoC`), and its clone is exactly that content, since a message without
responses marshals (`MsgMarshals`). The Antithesis Link passes `cloneMsg_law_of proto.wp_ClonePb`
to `drainSend`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainSendWp
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.PerTypeMessage
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Net
public import Spec.google_golang_org.protobuf.proto.ClonePb

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section law
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`cloneMsg.law`**, from `proto.Clone`'s spec at the registered message type. -/
theorem cloneMsg_law_of (wp_Clone : proto.ClonePb.spec (GF := GF) (hG := hG)) :
    cloneMsg.law (GF := GF) (hG := hG) := by
  intro l c hr
  iintro %Φ ⟨#Hpkg, #Hl⟩ HΦ
  have wpC := wp_Clone pbMessageC pbMessageC_reg l c
  simp only [pbMessageC_ty, pbMessageC_roC, pbMessageC_decC, pbMessageC_eqv, pbMessageC_modelOf,
    pbMessageC_C, pbMessageC_marshals] at wpC
  ihave #Hro := msgPtsCC_msgRoC l c hr $$ Hl
  wp_apply wpC $$ [] as %l' ⟨%c', Hl', %Heqv⟩
  · first | iexact Hro | (isplitl []; iexact Hpkg; iexact Hro)
  have hm : MsgMarshals c.model := by
    simp only [MsgMarshals, MsgC.model, hr, List.map_nil]
  rw [Heqv.2.2 hm]
  iapply HΦ $$ Hl'

end law

end AntHarness
end EtcdGrove
end Perennial
