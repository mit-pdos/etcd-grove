/-
The proof of `NewClientWithCodec` (`Net/Spec/net/rpc/NewClientWithCodec.lean`): the `Client`
allocated with an empty `pending` map, its ghost state (the numbers issued, `0`, and no receipt;
not shut down), its two mutexes made (`sendInv`, `muInv`), and `input` forked with the reader's
resources (`readerOwn`, nothing read).
-/
module

public import Net.Spec.net.rpc.NewClientWithCodec
public import Net.Spec.net.rpc.Client__input

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net.rpc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions]
variable [π : NetProtoGS] [sync.Assumptions]

theorem NewClientWithCodec.wp_proof (wp_input : Client.input.spec (GF := GF) (hG := hG)) :
    NewClientWithCodec.spec (GF := GF) (hG := hG) := by
  intro W a cn γ cc t la ra
  wp_start as ⟨%Hbound, #Henv, #Hrwc, Hwerr, #Hconn, Hdial⟩
  wp_auto
  wp_apply (wp_map_make1 (K := w64) (V := Loc)) as %mp Hmp
  iStructNamed «$r0»
  ipersist codec
  imod ghostVar_alloc (GF := GF) (0 : Nat) with ⟨%γsq, Hsq⟩
  icases (ghostVar_split_half γsq 1 (0 : Nat)).1 $$ Hsq with ⟨Hsq1, Hsq2⟩
  imod ghostVar_alloc (GF := GF) false with ⟨%γd, Hd⟩
  icases (ghostVar_split_half γd 1 false).1 $$ Hd with ⟨Hd1, Hd2⟩
  icases (ghostVar_split_half γd (1 : Qp).half false).1 $$ Hd2 with ⟨Hd2, Hd3⟩
  imod receipt_zero (GF := GF) with Hr0
  iunfold rpcDialed at Hdial
  icases Hdial with ⟨#Hrpc, Hreqs, Hnm, Hsend, Hrecv⟩
  ihave #Hci := sendTok_connIs $$ Hsend
  icases recvTok_keep_sentLb (Gg := hG.goose_globalGS) cn false true rfl _ _ $$ Hrecv with ⟨Hrecv, #Hsl⟩
  let γc : ClientNames := ⟨γ, γsq, γd⟩
  imod sync.init_Mutex (sendInv γc «$r0_ptr» cc cn W a) ⊤
      (structFieldRef net.rpc.Client go!"reqMutex" «$r0_ptr») $$ reqMutex
      [request Hwerr Hsend Hreqs Hsq1 Hd3] with #Hsmu
  · inext
    iunfold sendInv
    iexists zero_val net.rpc.Request, interface.nil, [], W.hs a, 0
    iframe request Hwerr Hsend Hreqs Hsq1
    isplitl [Hd3]
    · iexists false; iexact Hd3
    isplitr
    · ileft; ipureintro; rfl
    ipureintro
    simp [reqsWire]
  imod sync.init_Mutex (muInv γc «$r0_ptr») ⊤
      (structFieldRef net.rpc.Client go!"mutex" «$r0_ptr») $$ mutex
      [seq pending Hmp shutdown closing Hsq2 Hr0 Hd1 Hnm] with #Hmu
  · inext
    iunfold muInv
    iexists 0, 0, mp, ∅, false, false, ∅
    iframe seq pending Hmp shutdown closing Hsq2 Hr0 Hd1 Hnm
    isplitr
    · ipureintro; exact ⟨rfl, Hbound⟩
    isplitr
    · ipureintro; intro i h; simp at h
    simp only [Bool.false_eq_true, ite_false]
    iapply BigSepM.bigSepM_empty.2
    iempintro
  ihave #Hat : clientAt «$r0_ptr» W a γc cc t cn la ra $$ []
  · iunfold clientAt
    iframe codec Hrwc Hconn Hci Hrpc Hsl Henv Hsmu Hmu
  wp_apply wp_fork $$ [Hrecv Hd2]
  · wp_apply wp_input «$r0_ptr» W a γc cc t cn la ra $$ [Hrecv Hd2]
    · iframe Hat
      iunfold readerOwn
      iexists []
      iframe Hd2
      isplitl [Hrecv]
      · simp only [List.flatMap_nil, framesOf_nil, List.append_nil]; iexact Hrecv
      ipureintro; simp
    itrivial
  iapply HΦ
  unfold isClient isClientN
  iexists γc, cc, t, cn, la, ra
  iexact Hat

end proof

end net.rpc
end Perennial
