/- Lean-first (no Rocq counterpart).

# `lib/grpcdriver`: listening at an address whose protocols are set

The deployment sets the server's address's table before the server runs (from `addrUnset`, keeping
its listening token in its invariant, `lisTokN`, as `net.Listen`'s proof does, and its validity). The
server then listens through that invariant: `drv_listen`, `net.Listen.wp_proof`'s argument
(`Proof/net/Listen.lean`) without the pending set and the claim, from Net's `Listen.spec` (a
hypothesis).
-/
module

public import Proof.net.InvNet
public import Net.Spec.net.Listen
public import Net.Proof.net.AtAddr

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net EtcdGrove

namespace github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver

section listen
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : _root_.Perennial.net.Assumptions]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **`net.Listen("tcp", a)` at a valid address whose listening token is in its invariant**: an open
listener at `a`, or an error. -/
theorem drv_listen
    (wp_Listen : ∀ [HasExt netExt], _root_.Perennial.net.Listen.spec (GF := GF) (hG := hG))
    [hX : HasExt netExt] (addr : GoString) (hok : addrOk addr = true) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.net ∗
        inv (lisTokN addr) (netLisTok (NG (Gg := hG.goose_globalGS)) addr) }}
      (App (App (Val (@! _root_.Perennial.net.Listen)) (Val #(go!"tcp"))) (Val #addr))
    {{ (l err : GoInterface), RET (PairV #l #err);
        (⌜err = GoInterface.nil⌝ ∗ netListenerOpen l addr) ∨ ⌜err ≠ GoInterface.nil⌝ }} := by
  iintro %Φ ⟨#Hnet, #Hinv⟩ HΦ
  have hA := _root_.Perennial.net.Listen.spec_addrOk (GF := GF) (hG := hG) wp_Listen
  iapply (hA go!"tcp" _root_.Perennial.net.tcpNet_tcp addr) $$ []
  · iframe Hnet
    isplitr
    · ipureintro; exact hok
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

end listen

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver
end Perennial
