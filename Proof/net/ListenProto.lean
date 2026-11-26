/-
`net.Listen` at an address whose net protocols are set (see `Spec/net/ListenProto.lean`): from the part `Net/`'s
`Listen` spec (`Net/Spec/net/Listen.lean`), the callee its `Link` passes, at the address's validity and its listening
token, which the address's net protocols hold in an invariant (`addrProto_tok`, `listen_au`); the listener's Go value
tied to the extension's listener by Net's `isListener` (`lisAt`, kept in `netListenerOpen`). As
`Proof/net/ListenHttp.lean`, without the claim.
-/
module

public import Spec.net.ListenProto
public import Net.Spec.net.Listen
public import Net.Proof.net.AtAddr

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : _root_.Perennial.net.Assumptions]
variable [_root_.Perennial.net.FieldAssumptions]

theorem net.Listen.wp_proofProto
    (wp_Listen : ∀ [HasExt netExt], _root_.Perennial.net.Listen.spec (GF := GF) (hG := hG)) :
    net.Listen.specProto (GF := GF) (hG := hG) := by
  intro hX π network addr P Q
  iintro %Φ ⟨%Hnw, #Hp⟩ HΦ
  subst Hnw
  ihave %Hok := addrTok_ok (GF := GF) addr $$ [Hp]
  · iapply addrProto_tok $$ Hp
  have hA := _root_.Perennial.net.Listen.spec_addrOk (GF := GF) (hG := hG) wp_Listen
  iapply (hA go!"tcp" _root_.Perennial.net.tcpNet_tcp addr) $$ []
  · isplitr
    · ipureintro; exact Hok
    · iapply listen_au $$ Hp
  iintro !> %li %err Hpost
  iapply HΦ
  icases Hpost with (⟨%Herr, %l, Hli, Hlis, Hat⟩ | ⟨%x, -, Hres⟩)
  · ileft
    isplitr; · ipureintro; exact Herr
    iunfold _root_.Perennial.net.isListener at Hli
    icases Hli with ⟨%t, %x, %Hli, #Hla⟩
    iunfold netListenerOpen
    iexists hX, t, l, x
    iframe Hla Hlis Hat
    ipureintro; exact Hli
  · iright
    iunfold _root_.Perennial.net.resErr at Hres
    icases Hres with ⟨%e, Hop, -⟩
    iunfold _root_.Perennial.net.opErr at Hop
    icases Hop with ⟨%pe, %nw, ⟨%Herr, -⟩, -⟩
    ipureintro
    subst Herr
    intro h; cases h

end proof

end EtcdGrove
end Perennial
