/-
Proof of `Spec/google_golang_org/grpc/internal/grpcsync/NewEvent.lean` over the model's body (W1,
2026-11-26): `&Event{c: make(chan struct{})}`.
-/
module

public import Spec.google_golang_org.grpc.internal.grpcsync.NewEvent

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : google_golang_org.grpc.internal.grpcsync.Assumptions]

theorem grpcsync.NewEvent.wp_proof : grpcsync.NewEvent.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_apply (chan.wp_make1 (V := Unit)
    (ct := go.ChannelType go.sendrecv (go.StructType []))) as %ch %γ ⟨#Hch, %Hcap, Hoc⟩
  iapply HΦ
  unfold srvEventIs
  iexists ch, γ
  isplitl [«$r0»]
  · iexact «$r0»
  iframe
  ipureintro
  exact Hcap

end proof

end EtcdGrove
end Perennial
