/-
`net.Listen` (see `Spec/net/Listen.lean`): from the part `Net/`'s `Listen` spec (`Net/Spec/net/Listen.lean`,
proved over the net extension, `Net/Proof/net/Listen.lean`), the callee its `Link` passes. Until the net
swap (etcd-dist D2, 2026-11-22) a trust-boundary axiom over the names-only `net`.
-/
module

public import Spec.net.Listen
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

theorem net.Listen.wp_proof
    (wp_Listen : ∀ [HasExt netExt], _root_.Perennial.net.Listen.spec (GF := GF) (hG := hG)) :
    net.Listen.spec (GF := GF) (hG := hG) := by
  intro network addr
  iintro %Φ ⟨%Hnw, Hfree⟩ HΦ
  subst Hnw
  iunfold netAddrFree at Hfree
  icases Hfree with ⟨Hclaim, %hX, Hu⟩
  haveI : HasExt netExt := hX
  iunfold addrUnset at Hu
  icases Hu with ⟨Hpend, #Hvalid, Htok⟩
  ihave %Hok := addrTok_ok (GF := GF) addr $$ Hvalid
  -- the listening token goes to an invariant, which the step opens and `netAddrLeft` keeps
  imod inv_alloc (lisTokN addr) ⊤ (netLisTok (NG (Gg := hG.goose_globalGS)) addr) $$ [Htok]
    with #Hinv
  · inext; iexact Htok
  have hA := _root_.Perennial.net.Listen.spec_addrOk (GF := GF) (hG := hG) wp_Listen
  iapply (hA go!"tcp" _root_.Perennial.net.tcpNet_tcp addr) $$ []
  · isplitr
    · ipureintro; exact Hok
    · iinv Hinv with >Ht Hclose
      iapply fupd_mask_intro Std.LawfulSet.empty_subset
      iintro Hmask
      iframe Ht
      iintro Ht
      imod Hmask
      imod Hclose $$ [Ht] with -
      · inext; iexact Ht
      imodintro
      itrivial
  iintro !> %li %err Hpost
  iapply HΦ
  icases Hpost with (⟨%Herr, %l, Hli, Hlis, Hat⟩ | ⟨%x, %e, -, Hop, -⟩)
  · ileft
    isplitr; · ipureintro; exact Herr
    iunfold netListenerAt
    iframe Hclaim
    iunfold _root_.Perennial.net.isListener at Hli
    icases Hli with ⟨%t, %x, %Hli, -⟩
    isplitr [Hpend]
    · iunfold netListenerOpen
      iexists hX, t, l
      iframe Hlis Hat
      ipureintro; exact Hli
    · iunfold netAddrLeft
      iexists hX
      iframe Hpend Hvalid
      unfold lisTokInv
      ileft
      iexact Hinv
  · iright
    iunfold _root_.Perennial.net.opErr at Hop
    icases Hop with ⟨%pe, %nw, ⟨%Herr, -⟩, -⟩
    ipureintro
    subst Herr
    intro h; cases h

end proof

end EtcdGrove
end Perennial
