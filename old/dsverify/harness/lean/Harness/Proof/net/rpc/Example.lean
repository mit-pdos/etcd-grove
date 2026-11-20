/-
A worked example of the rpc specs (`Results.lean`): a client `Call` proved against a server's
method spec over the net model, for a toy service `"Arith"` with one method `"Add"`.

There is no Go package behind it: the example is generic in the kit's codec (`RpcCodec`), and
its hypotheses are what a kit's codec proof provides for its types:
* the pure encodings of `Add`'s argument (`encArgs x y`) and reply (`encReply r`), and the
  reply's decoder `decReply` (a round trip: `decReply (encReply r) = some r`);
* ownership of a Go argument value `args` holding `(x, y)` (`ArgsOwn args x y`) and of a reply
  pointer `reply` holding `r` (`ReplyOwn reply r`);
* `enc_args`: encoding `args` yields `encArgs x y` and gives `ArgsOwn` back;
* `dec_reply`: decoding bytes `bs` into `reply` either succeeds with `ReplyOwn reply r` for
  `decReply bs = some r`, or fails with `reply` owned in some state;
* `call_add` (the server's dispatch): `Call(rcvr, "Add", encArgs x y)` finds the method and
  returns `encReply (x + y)` with an empty error message.

The method spec `addSpec` says: a caller of `Add` on the encoding of `(x, y)` gets its
continuation on the encoding of `x + y` and the empty message (`Add` never fails). Server side:
`rcvrOk_add` (the receiver meets `addSpec`) and `arith_defaultServes` (once `Arith` is
registered at the `DefaultServer` (`RegisterName.wp_proof`), it serves every address whose only
service is `Arith`, which is what `rpc_ListenAndServe_pre` needs). Client side: `wp_call_add`,
from `Client.Call.wp`, for a client that only tests `err != nil`: it instantiates the
continuation trivially for a non-empty message (`⌜msg = [] → rep = encReply (x + y)⌝`), so
`Call`'s `ServerError` outcome folds into the error case with nothing lost. `wp_call_div` (a
method `Div` whose spec answers `"divide by zero"` for a zero divisor; `rcvrOk_div` at the
server) is a client that tells the server's error apart: `ServerError("divide by zero")`
exactly when `Div` ran with `y = 0`, and every other error is not a `ServerError`. Set-up:
`arith_setup` makes such an address with `rpcWorld_alloc` and `rpcAddr_set`; `rpcAddr W a` is
what `DialHTTP.wp` and `rpc_ListenAndServe_pre` take.
-/
module

public import Harness.Proof.net.rpc.Results

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode NetConn

namespace net.rpc.example

open net.rpc

section arith
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netConnExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.Assumptions] [net.model.Assumptions] [net.http.Assumptions] [net.rpc.Assumptions]
variable [RpcKit] [RpcCodec GF]
variable (encArgs : w64 → w64 → List w8) (encReply : w64 → List w8)

/-- `Add`'s spec: on the encoding of `(x, y)`, the continuation on the encoding of `x + y` and
the empty message. -/
def addSpec : MethodSpec GF := fun m bs Φ =>
  iprop(⌜m = go!"Add"⌝ ∗ ∃ x y : w64, ⌜bs = encArgs x y⌝ ∗ Φ (encReply (x + y)) [])

/-- The services of an `Arith` address: only `Arith`. -/
def arithSS : GoString → Option (MethodSpec GF) := fun svc =>
  if svc = go!"Arith" then some (addSpec encArgs encReply) else none

/-! ## Server side -/

/-- A receiver whose dispatch runs `Add` meets `addSpec`. -/
theorem rcvrOk_add (rcvr : GoInterface)
    (call_add : ∀ (x y : w64) (Ψ : List w8 → GoString → Bool → IProp GF),
      Ψ (encReply (x + y)) [] true ⊢ RpcCodec.call rcvr go!"Add" (encArgs x y) Ψ) :
    ⊢ rcvrOk (GF := GF) rcvr (addSpec encArgs encReply) := by
  unfold rcvrOk addSpec
  imodintro
  iintro %m %args %Φ ⟨%Hm, %x, %y, %Hbs, HΦ⟩
  subst Hm Hbs
  iapply call_add x y
  isplitr
  · ipureintro; rfl
  iexact HΦ

/-- Once `Arith` is registered at the `DefaultServer` with such a receiver, the `DefaultServer`
serves every address whose only service is `Arith`. -/
theorem arith_defaultServes (rcvr : GoInterface) (W : RpcWorld GF) (a : GoString)
    (call_add : ∀ (x y : w64) (Ψ : List w8 → GoString → Bool → IProp GF),
      Ψ (encReply (x + y)) [] true ⊢ RpcCodec.call rcvr go!"Add" (encArgs x y) Ψ)
    (hSS : W.SS a = arithSS encArgs encReply) :
    isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗ defaultSvcReg go!"Arith" rcvr ⊢
      defaultServes W a := by
  iintro ⟨#Hpkg, #Hreg⟩
  iapply defaultServes_intro W a
  iframe Hpkg
  imodintro
  iintro %svc %S %HS
  rw [hSS] at HS
  unfold arithSS at HS
  split at HS
  · cases HS
    subst_vars
    iexists rcvr
    iframe Hreg
    iapply rcvrOk_add encArgs encReply rcvr call_add
  · cases HS

/-! ## Client side -/

theorem splitSM_arith : splitSM go!"Arith.Add" = some (go!"Arith", go!"Add") := by decide

/-- `c.Call("Arith.Add", args, reply)`: `nil` with the sum in `reply`, or an error with `reply`
owned in some state. -/
theorem wp_call_add (decReply : List w8 → Option w64)
    (ArgsOwn : GoInterface → w64 → w64 → IProp GF) (ReplyOwn : GoInterface → w64 → IProp GF)
    (round : ∀ r, decReply (encReply r) = some r)
    (enc_args : ∀ args x y (Ψ : List w8 → IProp GF),
      ArgsOwn args x y ∗ (ArgsOwn args x y -∗ Ψ (encArgs x y)) ⊢ RpcCodec.enc args Ψ)
    (dec_reply : ∀ bs reply r0 (Ψ : Bool → IProp GF),
      ReplyOwn reply r0 ∗
        ((∀ r, ⌜decReply bs = some r⌝ -∗ ReplyOwn reply r -∗ Ψ true) ∧
          (∀ r, ReplyOwn reply r -∗ Ψ false)) ⊢ RpcCodec.dec bs reply Ψ)
    (c : Loc) (W : RpcWorld GF) (a : GoString) (hSS : W.SS a = arithSS encArgs encReply)
    (args reply : GoInterface) (x y r0 : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗ codecSet (GF := GF) ∗ kitCodecOk ∗
        isClient c W a ∗ ArgsOwn args x y ∗ ReplyOwn reply r0 }}
      (App (App (App (Val (c @!! go.GoType.PointerType net.rpc.Client.ty @!! go!"Call"))
        (Val #(go!"Arith.Add"))) (Val #args)) (Val #reply))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ArgsOwn args x y ∗ ReplyOwn reply (x + y)) ∨
        (⌜err ≠ interface.nil⌝ ∗ ∃ r, ReplyOwn reply r) }} := by
  wp_start_folded as ⟨#Hcs, #Hko, #Hcl, Ha, Hr⟩
  wp_apply Client.Call.wp c W a go!"Arith.Add" go!"Arith" go!"Add" (addSpec encArgs encReply)
      args reply (fun rep msg => iprop(⌜msg = [] → rep = encReply (x + y)⌝)) (ArgsOwn args x y)
      (iprop(∃ r, ReplyOwn reply r))
      (fun rep ok => if ok then iprop(∃ r, ⌜decReply rep = some r⌝ ∗ ReplyOwn reply r)
        else iprop(∃ r, ReplyOwn reply r))
      $$ [$Hpkg $Hcs $Hko $Hcl Ha Hr] as %err Hpost
  · isplitr
    · ipureintro; exact ⟨splitSM_arith, by rw [hSS]; simp [arithSS]⟩
    isplitl [Ha]
    · iapply enc_args args x y
      iframe Ha
      iintro Ha
      iframe Ha
      unfold addSpec
      isplitr
      · ipureintro; rfl
      iexists x, y
      isplitr <;> ipureintro
      · rfl
      · intro _; rfl
    isplitl [Hr]
    · iexists r0; iexact Hr
    imodintro
    iintro ⟨%r1, Hr⟩ %rep
    iapply dec_reply rep reply r1
    iframe Hr
    isplit
    · iintro %r %Hd Hr
      simp only [↓reduceIte]
      iexists r; iframe Hr; ipureintro; exact Hd
    · iintro %r Hr
      simp only [Bool.false_eq_true, ↓reduceIte]
      iexists r; iexact Hr
  iapply HΦ
  icases Hpost with (⟨%He, Ha, %rep, %Hrep, %r, %Hd, Hr⟩ | ⟨%msg, ⟨%Hm, %He⟩, -, -, -, Hr⟩ |
    ⟨⟨%He, -⟩, -, Hpost⟩)
  · ileft
    have Hrep := Hrep (by trivial)
    subst Hrep
    rw [round] at Hd
    cases Hd
    iframe Ha Hr
    ipureintro; exact He
  · iright
    isplitr
    · ipureintro; subst He; exact serverErr_ne_nil msg
    iexact Hr
  · iright
    isplitr
    · ipureintro; exact He
    icases Hpost with (⟨-, (H | ⟨%rep, H⟩)⟩ | ⟨-, H⟩) <;> iexact H

/-! ## A method that fails: the server's message at the client -/

/-- `Div`'s spec: on the encoding of `(x, y)`, the continuation on the encoding of `x / y` and
the empty message, or, for `y = 0`, on the message `"divide by zero"`. -/
def divSpec : MethodSpec GF := fun m bs Φ =>
  iprop(⌜m = go!"Div"⌝ ∗ ∃ x y : w64, ⌜bs = encArgs x y⌝ ∗
    (if y = 0 then Φ [] go!"divide by zero" else Φ (encReply (x / y)) []))

/-- A receiver whose dispatch runs `Div` (answering `"divide by zero"` for `y = 0`) meets
`divSpec`. -/
theorem rcvrOk_div (rcvr : GoInterface)
    (call_div : ∀ (x y : w64) (Ψ : List w8 → GoString → Bool → IProp GF),
      (if y = 0 then Ψ [] go!"divide by zero" true else Ψ (encReply (x / y)) [] true) ⊢
        RpcCodec.call rcvr go!"Div" (encArgs x y) Ψ) :
    ⊢ rcvrOk (GF := GF) rcvr (divSpec encArgs encReply) := by
  unfold rcvrOk divSpec
  imodintro
  iintro %m %args %Φ ⟨%Hm, %x, %y, %Hbs, HΦ⟩
  subst Hm Hbs
  iapply call_div x y
  split
  · isplitr
    · ipureintro; rfl
    iexact HΦ
  · isplitr
    · ipureintro; rfl
    iexact HΦ

/-- `c.Call("Calc.Div", args, reply)` at an address whose service `Calc` has `divSpec`, for a
client that tells the server's error apart (as with `err.(rpc.ServerError)`,
`wp_assert_serverErr` / `wp_assert_notServerErr`): `nil` with the quotient in `reply` and
`y ≠ 0`; `ServerError("divide by zero")` exactly when `Div` ran with `y = 0`; or another error,
which is not a `ServerError`. -/
theorem wp_call_div (decReply : List w8 → Option w64)
    (ArgsOwn : GoInterface → w64 → w64 → IProp GF) (ReplyOwn : GoInterface → w64 → IProp GF)
    (round : ∀ r, decReply (encReply r) = some r)
    (enc_args : ∀ args x y (Ψ : List w8 → IProp GF),
      ArgsOwn args x y ∗ (ArgsOwn args x y -∗ Ψ (encArgs x y)) ⊢ RpcCodec.enc args Ψ)
    (dec_reply : ∀ bs reply r0 (Ψ : Bool → IProp GF),
      ReplyOwn reply r0 ∗
        ((∀ r, ⌜decReply bs = some r⌝ -∗ ReplyOwn reply r -∗ Ψ true) ∧
          (∀ r, ReplyOwn reply r -∗ Ψ false)) ⊢ RpcCodec.dec bs reply Ψ)
    (c : Loc) (W : RpcWorld GF) (a : GoString)
    (hSS : W.SS a go!"Calc" = some (divSpec encArgs encReply))
    (args reply : GoInterface) (x y r0 : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗ codecSet (GF := GF) ∗ kitCodecOk ∗
        isClient c W a ∗ ArgsOwn args x y ∗ ReplyOwn reply r0 }}
      (App (App (App (Val (c @!! go.GoType.PointerType net.rpc.Client.ty @!! go!"Call"))
        (Val #(go!"Calc.Div"))) (Val #args)) (Val #reply))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil ∧ y ≠ 0⌝ ∗ ArgsOwn args x y ∗ ReplyOwn reply (x / y)) ∨
        (⌜err = serverErr go!"divide by zero" ∧ y = 0⌝ ∗ ∃ r, ReplyOwn reply r) ∨
        (⌜err ≠ interface.nil ∧ notServerErr err⌝ ∗ ∃ r, ReplyOwn reply r) }} := by
  wp_start_folded as ⟨#Hcs, #Hko, #Hcl, Ha, Hr⟩
  wp_apply Client.Call.wp c W a go!"Calc.Div" go!"Calc" go!"Div" (divSpec encArgs encReply)
      args reply
      (fun rep msg => iprop(⌜(msg = [] → y ≠ 0 ∧ rep = encReply (x / y)) ∧
        (msg ≠ [] → y = 0 ∧ msg = go!"divide by zero")⌝))
      (ArgsOwn args x y) (iprop(∃ r, ReplyOwn reply r))
      (fun rep ok => if ok then iprop(∃ r, ⌜decReply rep = some r⌝ ∗ ReplyOwn reply r)
        else iprop(∃ r, ReplyOwn reply r))
      $$ [$Hpkg $Hcs $Hko $Hcl Ha Hr] as %err Hpost
  · isplitr
    · ipureintro; exact ⟨by decide, hSS⟩
    isplitl [Ha]
    · iapply enc_args args x y
      iframe Ha
      iintro Ha
      iframe Ha
      unfold divSpec
      isplitr
      · ipureintro; rfl
      iexists x, y
      isplitr
      · ipureintro; rfl
      split
      · ipureintro
        exact ⟨fun h => absurd h (by decide), fun _ => ⟨by assumption, rfl⟩⟩
      · ipureintro
        exact ⟨fun _ => ⟨by assumption, rfl⟩, fun h => absurd rfl h⟩
    isplitl [Hr]
    · iexists r0; iexact Hr
    imodintro
    iintro ⟨%r1, Hr⟩ %rep
    iapply dec_reply rep reply r1
    iframe Hr
    isplit
    · iintro %r %Hd Hr
      simp only [↓reduceIte]
      iexists r; iframe Hr; ipureintro; exact Hd
    · iintro %r Hr
      simp only [Bool.false_eq_true, ↓reduceIte]
      iexists r; iexact Hr
  iapply HΦ
  icases Hpost with (⟨%He, Ha, %rep, %Hrep, %r, %Hd, Hr⟩ |
    ⟨%msg, ⟨%Hm, %He⟩, -, -, ⟨%rep, %Hrep⟩, Hr⟩ | ⟨%He, -, Hpost⟩)
  · ileft
    obtain ⟨hy, hrep⟩ := Hrep.1 (by trivial)
    subst hrep
    rw [round] at Hd
    cases Hd
    iframe Ha Hr
    ipureintro; exact ⟨He, hy⟩
  · iright; ileft
    obtain ⟨hy, hm⟩ := Hrep.2 Hm
    subst hm
    iframe Hr
    ipureintro; exact ⟨He, hy⟩
  · iright; iright
    isplitr
    · ipureintro; exact He
    icases Hpost with (⟨-, (H | ⟨%rep, H⟩)⟩ | ⟨-, H⟩) <;> iexact H

/-! ## Set-up -/

/-- In a run's start-up: a world in which `a` offers only `Arith`, and `a` an rpc address of it,
from the address's `addrUnset`. -/
theorem arith_setup [G : GooseGlobalGS HasLC.hasLC GF] (a : GoString) :
    ⊢@{IProp GF} addrUnset a ={⊤}=∗
      ∃ W : RpcWorld GF, ⌜W.SS a = arithSS encArgs encReply⌝ ∗ rpcAddr W a := by
  iintro Hu
  imod rpcWorld_alloc (fun _ => arithSS encArgs encReply) with ⟨%W, %HW, #Hinv⟩
  imod rpcAddr_set W a $$ Hu Hinv with Ha
  imodintro
  iexists W
  iframe Ha
  ipureintro; rw [HW]

end arith

end net.rpc.example

end Perennial
