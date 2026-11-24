-- The copy for the part `KvNet/` of `Net/Proof/net/AtAddr.lean` (etc/copy-part.py; rerun it, do not edit).
/-
The specs of `net.Listen` and `Listener.Accept` at a valid address (`addrOk`, D20), as instances of
their canonical specs (`Net/Spec/net/Listen.lean`, `Net/Spec/net/Listener__Accept.lean`, which cover
the wildcards of D21 too), in the shapes their callers at a valid address are written in:
`Listen.spec_addrOk`, with the address's listening token (`lisToks_addrOk`), giving `netLisAt`;
`Listener.Accept.spec_addrOk`, with one update over both outcomes and the address's pending set (a
listener at a valid address takes only the connections dialed to it, `lisAccepts_addrOk`), which
`accept_au` and `accept_shared_au` (`GooseLang/Ext/Net/Proto.lean`) build. Not specs of their own:
each follows from the canonical spec it is given.
-/
module

public import KvNet.Spec.net.Listen
public import KvNet.Spec.net.Listener__Accept

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net

section instances
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.Assumptions] [field_sem : net.FieldAssumptions]

/-- `net.Listen("tcp", a)` at a valid address `a`, by the holder of `a`'s listening token: a new
open listener at `a` (`netLisAt`), or the `*OpError`. -/
abbrev Listen.specAddrOk : Prop :=
  ∀ (nw : GoString), tcpNet nw → ∀ (a : GoString),
  {{ ⌜addrOk a = true⌝ ∗
      (|={⊤,∅}=> netLisTok (extGlobalGS netExt (G := hG.goose_globalGS)) a ∗
        (netLisTok (extGlobalGS netExt (G := hG.goose_globalGS)) a ={∅,⊤}=∗ True)) }}
    (App (App (Val (@! net.Listen)) (Val #nw)) (Val #a))
  {{ (li : GoInterface) (err : GoInterface), RET (PairV #li #err);
      (⌜err = interface.nil⌝ ∗ ∃ l, isListener li l ∗ netLis (extLocalGS netExt (L := hG.goose_localGS)) l a true ∗
        netLisAt (extLocalGS netExt (L := hG.goose_localGS)) l a) ∨
      (∃ x e, netAddr x ∗ opErr go!"listen" interface.nil x e err ∗
        (sysErr (fun _ => True) e ∨ ⌜epollErr e⌝)) }}

/-- `Listener.Accept.spec` at a valid address `a`: one update over the listener's state and `a`'s
pending set, for both outcomes. -/
abbrev Listener.Accept.specAddrOk : Prop :=
  ∀ (t : Loc) (l : w64) (x : GoInterface) (a : GoString) (Qfail : NetErr → IProp GF)
    (Qok : Nat → IProp GF),
  {{ lisAt (GF := GF) t l x ∗ netLisAt (extLocalGS netExt (L := hG.goose_localGS)) l a ∗
      (|={⊤,∅}=> ∃ o S, netLis (extLocalGS netExt (L := hG.goose_localGS)) l a o ∗ netPend (extGlobalGS netExt (G := hG.goose_globalGS)) a S ∗
        ((netLis (extLocalGS netExt (L := hG.goose_localGS)) l a o -∗ netPend (extGlobalGS netExt (G := hG.goose_globalGS)) a S ={∅,⊤}=∗
            Qfail (if o then .sys else .closed)) ∧
          (⌜o = true⌝ -∗ ∀ cn, ⌜cn ∈ S⌝ -∗ netLis (extLocalGS netExt (L := hG.goose_localGS)) l a o -∗
            netPend (extGlobalGS netExt (G := hG.goose_globalGS)) a (S \ {[cn]}) -∗ netConnAt (extGlobalGS netExt (G := hG.goose_globalGS)) cn a ={∅,⊤}=∗ Qok cn))) }}
    (App (Val #(methods (go.GoType.PointerType TCPListener.ty) go!"Accept" #t)) (Val #()))
  {{ (c : GoInterface) (err : GoInterface), RET (PairV #c #err);
      (⌜err = interface.nil⌝ ∗ ∃ cn, isConn c cn true a ∗ Qok cn) ∨
      (∃ k, Qfail k ∗ resErr (some k) go!"accept" interface.nil x none (· = go!"accept4") err) }}

theorem Listen.spec_addrOk (h : Listen.spec (GF := GF) (hG := hG)) :
    Listen.specAddrOk (GF := GF) (hG := hG) := by
  intro nw hnw a
  iintro %Φ ⟨%Hok, Htok⟩ HΦ
  iapply h nw hnw a $$ [Htok]
  · isplitr
    · ipureintro; simp [listenOk, Hok]
    imod Htok with ⟨Ht, Hk⟩
    imodintro
    isplitl [Ht]
    · iapply (lisToks_addrOk _ Hok).2 $$ Ht
    · iintro Ht
      iapply Hk
      iapply (lisToks_addrOk _ Hok).1 $$ Ht
  inext
  iintro %li %err H
  icases H with (⟨%Herr, %l, #Hli, Hlis, #Hla⟩ | ⟨%x, %e, #Hx, #Herr, #He⟩)
  · iapply HΦ
    ileft
    isplitr
    · ipureintro; exact Herr
    iexists l
    iframe Hli Hlis
    iapply netLisOn_at _ l Hok $$ Hla
  · iapply HΦ
    iright
    iexists x, e
    iframe Hx Herr He

theorem Listener.Accept.spec_addrOk (h : Listener.Accept.spec (GF := GF) (hG := hG)) :
    Listener.Accept.specAddrOk (GF := GF) (hG := hG) := by
  intro t l x a Qfail Qok
  iintro %Φ ⟨#Ht, #Hla, HAU⟩ HΦ
  ihave %Hok : ⌜addrOk a = true⌝ $$ []
  · unfold netLisAt; icases Hla with ⟨-, %h⟩; ipureintro; exact h
  ihave #Hon := netLisAt_on _ l a $$ Hla
  iapply h t l x a Qfail (fun _ cn => Qok cn) $$ [HAU]
  · iframe Ht Hon
    isplit
    · imod HAU with ⟨%o, %S, Hl, Hp, HF⟩
      imodintro
      iexists o
      iframe Hl
      iintro Hl
      icases HF with ⟨HF, -⟩
      iapply HF $$ Hl Hp
    · iintro %a' %ha'
      have e : a = a' := (lisAccepts_addrOk Hok).mp ha'.2
      subst e
      imod HAU with ⟨%o, %S, Hl, Hp, HF⟩
      imodintro
      iexists o, S
      iframe Hl Hp
      icases HF with ⟨-, HF⟩
      iexact HF
  inext
  iintro %c %err H
  icases H with (⟨%Herr, %cn, %a', %ha', #Hc, HQ⟩ | ⟨%k, HQ, #Herr⟩)
  · have e : a = a' := (lisAccepts_addrOk Hok).mp ha'.2
    subst e
    iapply HΦ
    ileft
    isplitr
    · ipureintro; exact Herr
    iexists cn
    iframe Hc HQ
  · iapply HΦ
    iright
    iexists k
    iframe HQ Herr

end instances

end net
end Perennial
