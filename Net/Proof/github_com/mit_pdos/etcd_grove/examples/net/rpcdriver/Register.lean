/- Lean-first (no Rocq counterpart).

The proof of `Register.spec`: the `Codec` literal's functions meet `drvCodec` (`Codec.lean`'s
`drvCodec_encOk`, ...), and `SetCodec` registers it (as swiftnet's `RegisterCodec.lean`).
-/
module

public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.Register
public import Net.Spec.net.rpc.SetCodec

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.mit_pdos.etcd_grove.examples.net.rpcdriver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]
variable [rpcdriver.Assumptions]

set_option goose.wp.extras true

theorem Register.wp_proof (wp_SetCodec : net.rpc.SetCodec.spec (GF := GF) (hG := hG)) :
    Register.spec (GF := GF) (hG := hG) := by
  wp_start as ⟨#Hmu, Hun⟩
  wp_auto
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ «$a0»
  ipersist «$a0»
  wp_apply wp_SetCodec drvCodec _ $$ [Hun]
  · isplitr
    · iexact Hmu
    isplitl [Hun]
    · iexact Hun
    isplitr
    · unfold net.rpc.codecIs
      iexists _
      iframe «$a0»
      isplitr
      · iapply drvCodec_encOk
      isplitr
      · iapply drvCodec_decOk
      · iapply drvCodec_rcvOk
    · ipureintro; exact Hnn
  iintro #Hcs
  wp_auto
  iapply HΦ
  iexact Hcs

end proof

end github_com.mit_pdos.etcd_grove.examples.net.rpcdriver
end Perennial
