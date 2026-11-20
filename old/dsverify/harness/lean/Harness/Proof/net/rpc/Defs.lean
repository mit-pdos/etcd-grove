/-
The node-level vocabulary of the specs of the lab's model of `net/rpc` (`notes/craq-net.md`,
"rpc specs"), over a node's heap; the protocol is in `Proto.lean`.

* Errors: `serverErr msg` is the `error` `rpc.ServerError(msg)` (Goose converts a value of the
  named string type to an interface as `interface.mkOk ServerError.ty #msg`); `notServerErr err`
  says `err`'s dynamic type is not `net/rpc.ServerError`, so the comma-ok assertion
  `err.(rpc.ServerError)` fails (`wp_assert_notServerErr`; `wp_assert_serverErr` on
  `serverErr msg`). `errMsg err msg` (persistent): `err` is a non-nil error, its dynamic type
  implements `error` (`go.typeSetContains e.ty go.error`, what the `log` model tests before
  calling `Error()`), and its `Error()` returns `msg`; `errAny err`: the same with `Error()`
  returning some string, possibly a different one per call (the `net` model's `*OpError`).
  `errMsg_errAny` weakens the first to the second; `errMsg_serverErr`: `ServerError(msg)` has
  message `msg`.
* `kitCodecOk` (persistent): the kit's codec functions (`kitFn`, `Base.lean`) meet the kit's
  `RpcCodec` predicate transformers (`Proto.lean`'s header); the run proves it of its kit's
  generated functions. `codecSet` (persistent): the model's `codec` variable holds a `*Codec`
  with the kit's functions for good, which every `getCodec` then returns (made by `SetCodec`;
  the package's `isPkgInit` keeps `codec` nil or such a codec).
  `kitNameOk` (persistent, under `RpcNames`): the kit's `rpcName` returns `RpcNames.name rcvr`
  (what `Register` needs; a separate obligation, for kits that call it).
  The decoding function's errors are not `ServerError`s and have a message (`decOk`): the
  client's reader passes a decoding error on to its pending calls.
* `rcvrOk rcvr S` (persistent): the receiver meets the method spec `S` through the codec's
  dispatch: from the deposit `S m args Φ`, `Call(rcvr, m, args)` finds the method and returns
  `Φ reply msg` for its reply and message (`""` for success), whatever the message.
* `svcReg s name rcvr` (persistent): server `s` has `rcvr` registered as `name`, for good
  (`RegisterName` succeeded; Go refuses a second registration of a name). `srvServes s W a`
  (persistent): every service address `a` offers in `W` is registered at `s` with a receiver
  that meets its spec: what `s`'s handler needs to serve a connection to `a`.
* `connIface cv cid side`: the `net.Conn` `cv` holds the `*TCPConn` of end `side` of `cid`.
-/
module

public import Harness.Proof.net.rpc.Proto
public import Harness.Proof.net.rpc.Base

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std NetConn

namespace net.rpc

section errs
variable [GooseExts] [go_gctx : GoGlobalContext]

/-- The `error` `rpc.ServerError(msg)`. -/
def serverErr (msg : GoString) : GoInterface :=
  interface.mkOk net.rpc.ServerError.ty #msg

/-- `err`'s dynamic type is not `net/rpc.ServerError` (`nil` is not one either). -/
def notServerErr (err : GoInterface) : Prop :=
  ∀ e : GoInterfaceOk, err = interface.ok e → e.ty ≠ net.rpc.ServerError.ty

theorem serverErr_ne_nil (msg : GoString) : serverErr msg ≠ interface.nil := by
  unfold serverErr interface.mkOk; simp

theorem notServerErr_serverErr (msg : GoString) : ¬ notServerErr (serverErr msg) := by
  intro h
  exact h _ rfl rfl

end errs

section errmsg
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `err` is a non-nil error whose `Error()` returns `msg` (persistent). -/
def errMsg (err : GoInterface) (msg : GoString) : IProp GF :=
  iprop(∃ e : GoInterfaceOk, ⌜err = interface.ok e⌝ ∗ ⌜go.typeSetContains e.ty go.error = true⌝ ∗
    □ ∀ Φ : val → IProp GF, ▷ Φ #msg -∗
      WP (App (Val #(methods e.ty go!"Error" e.v)) (Val #())) {{ Φ }})

instance errMsg_persistent (err : GoInterface) (msg : GoString) :
    Persistent (errMsg (GF := GF) err msg) := by
  unfold errMsg; infer_instance

/-- An error with a message is not `nil`. -/
theorem errMsg_ne_nil (err : GoInterface) (msg : GoString) :
    errMsg (GF := GF) err msg ⊢ ⌜err ≠ interface.nil⌝ := by
  unfold errMsg
  iintro ⟨%e, %h, -, -⟩
  ipureintro; subst h; simp

/-- `err` is a non-nil error whose `Error()` returns some string, possibly a different one per
call (persistent). -/
def errAny (err : GoInterface) : IProp GF :=
  iprop(∃ e : GoInterfaceOk, ⌜err = interface.ok e⌝ ∗ ⌜go.typeSetContains e.ty go.error = true⌝ ∗
    □ ∀ Φ : val → IProp GF, ▷ (∀ msg : GoString, Φ #msg) -∗
      WP (App (Val #(methods e.ty go!"Error" e.v)) (Val #())) {{ Φ }})

instance errAny_persistent (err : GoInterface) : Persistent (errAny (GF := GF) err) := by
  unfold errAny; infer_instance

/-- An error with a fixed message has some message. -/
theorem errMsg_errAny (err : GoInterface) (msg : GoString) :
    errMsg (GF := GF) err msg ⊢ errAny err := by
  unfold errMsg errAny
  iintro ⟨%e, %h, %ht, #H⟩
  iexists e
  isplitr
  · ipureintro; exact h
  isplitr
  · ipureintro; exact ht
  imodintro
  iintro %Φ HΦ
  iapply H
  inext
  iapply HΦ

theorem errAny_ne_nil (err : GoInterface) : errAny (GF := GF) err ⊢ ⌜err ≠ interface.nil⌝ := by
  unfold errAny
  iintro ⟨%e, %h, -, -⟩
  ipureintro; subst h; simp

variable [net.rpc.Assumptions]

/-- `rpc.ServerError` implements `error`. -/
theorem serverErr_isError :
    go.typeSetContains net.rpc.ServerError.ty go.error = true := by
  go_type_set

/-- `ServerError(msg).Error()` returns `msg`. -/
theorem errMsg_serverErr (msg : GoString) : ⊢ errMsg (GF := GF) (serverErr msg) msg := by
  unfold errMsg serverErr
  iexists _
  isplitr
  · ipureintro; rfl
  isplitr
  · ipureintro; exact serverErr_isError
  imodintro
  iintro %Φ HΦ
  wp_method_call
  wp_call
  wp_auto
  iexact HΦ

/-- `err.(rpc.ServerError)` (comma-ok) on `ServerError(msg)`: `(msg, true)`. -/
theorem wp_assert_serverErr (msg : GoString) (Φ : val → IProp GF) :
    ▷ Φ (PairV #msg #true) ⊢
      WP (App (Val (GoInstruction (TypeAssert2 net.rpc.ServerError.ty))) (Val #(serverErr msg)))
        {{ Φ }} := by
  iintro HΦ
  wp_auto
  iexact HΦ

/-- `err.(rpc.ServerError)` (comma-ok) on an error that is not a `ServerError`:
`("", false)`. -/
theorem wp_assert_notServerErr (err : GoInterface) (h : notServerErr err)
    (Φ : val → IProp GF) :
    ▷ Φ (PairV #(go!"") #false) ⊢
      WP (App (Val (GoInstruction (TypeAssert2 net.rpc.ServerError.ty))) (Val #err)) {{ Φ }} := by
  iintro HΦ
  wp_auto
  rcases err with e | _
  · simp only [h e rfl, ↓reduceIte, decide_false]
    iexact HΦ
  · iexact HΦ

end errmsg

section node
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netConnExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.Assumptions] [net.model.Assumptions] [net.rpc.Assumptions]
variable [RpcKit] [RpcCodec GF]

/-- `Encode`'s function meets `RpcCodec.enc`. -/
def encOk (fe : GoFunc) : IProp GF :=
  iprop(□ ∀ (v : GoInterface) (Ψ : List w8 → IProp GF) (Φ : val → IProp GF),
    RpcCodec.enc v Ψ -∗ ▷ (∀ (s : GoSlice) (bs : List w8), s ↦* bs -∗ Ψ bs -∗ Φ #s) -∗
    WP (App (Val #fe) (Val #v)) {{ Φ }})

/-- `Decode`'s function meets `RpcCodec.dec`; its errors are not `ServerError`s and have a
message (`errMsg`). -/
def decOk (fd : GoFunc) : IProp GF :=
  iprop(□ ∀ (data : GoSlice) (dq : DFrac) (bs : List w8) (ptr : GoInterface)
      (Ψ : Bool → IProp GF) (Φ : val → IProp GF),
    data ↦*{dq} bs -∗ RpcCodec.dec bs ptr Ψ -∗
    ▷ (∀ (err : GoInterface) (ok : Bool), data ↦*{dq} bs -∗ ⌜err = interface.nil ↔ ok = true⌝ -∗
        ⌜notServerErr err⌝ -∗
        Ψ ok -∗ (if ok then iprop(True) else ∃ msg, errMsg err msg) -∗ Φ #err) -∗
    WP (App (App (Val #fd) (Val #data)) (Val #ptr)) {{ Φ }})

/-- `Methods`'s function meets `RpcCodec.methods`. -/
def methodsOk (fm : GoFunc) : IProp GF :=
  iprop(□ ∀ (rcvr : GoInterface) (Φ : val → IProp GF),
    RpcCodec.methods rcvr -∗ ▷ (∀ n : w64, Φ #n) -∗ WP (App (Val #fm) (Val #rcvr)) {{ Φ }})

/-- `Call`'s function (the dispatch) meets `RpcCodec.call`. -/
def callOk (fc : GoFunc) : IProp GF :=
  iprop(□ ∀ (rcvr : GoInterface) (m : GoString) (args : GoSlice) (dq : DFrac) (bs : List w8)
      (Ψ : List w8 → GoString → Bool → IProp GF) (Φ : val → IProp GF),
    args ↦*{dq} bs -∗ RpcCodec.call rcvr m bs Ψ -∗
    ▷ (∀ (rep : GoSlice) (rbs : List w8) (msg : GoString) (found : Bool),
        rep ↦* rbs -∗ Ψ rbs msg found -∗ Φ (PairV (PairV #rep #msg) #found)) -∗
    WP (App (App (App (Val #fc) (Val #rcvr)) (Val #m)) (Val #args)) {{ Φ }})

/-- The kit's codec functions meet the kit's `RpcCodec` (persistent; the run's to prove). -/
def kitCodecOk : IProp GF :=
  iprop(encOk (kitFn go!"rpcEncode") ∗ decOk (kitFn go!"rpcDecode") ∗
    methodsOk (kitFn go!"rpcMethods") ∗ callOk (kitFn go!"rpcCall"))

/-- `Name`'s function returns `RpcNames.name rcvr` (for any value). -/
def nameOk [RpcNames] (fn : GoFunc) : IProp GF :=
  iprop(□ ∀ (rcvr : GoInterface) (Φ : val → IProp GF),
    ▷ Φ #(RpcNames.name rcvr) -∗ WP (App (Val #fn) (Val #rcvr)) {{ Φ }})

/-- The kit's name function meets `RpcNames` (persistent; the run's to prove, if it calls
`Register`). -/
def kitNameOk [RpcNames] : IProp GF := nameOk (kitFn go!"rpcName")

/-- A codec with the kit's functions is registered, for good (persistent). -/
def codecSet : IProp GF :=
  iprop(∃ c : Loc, ⌜c ≠ null⌝ ∗ globalAddr net.rpc.codec ↦□ c ∗ codecFns c)

/-- The receiver meets the method spec `S` through the codec's dispatch, for every answer
(persistent). -/
def rcvrOk (rcvr : GoInterface) (S : MethodSpec GF) : IProp GF :=
  iprop(□ ∀ (m : GoString) (args : List w8) (Φ : List w8 → GoString → IProp GF),
    S m args Φ -∗
    RpcCodec.call rcvr m args (fun reply msg found => iprop(⌜found = true⌝ ∗ Φ reply msg)))

/-- The `net.Conn` `cv` holds the `*TCPConn` of end `side` of `cid`. -/
def connIface (cv : GoInterface) (cid : w64) (side : Bool) : IProp GF :=
  iprop(∃ c : Loc, ⌜cv = interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #c⌝ ∗
    net.ownTCPConn c cid side)

instance kitCodecOk_persistent : Persistent (kitCodecOk (GF := GF)) := by
  unfold kitCodecOk encOk decOk methodsOk callOk; infer_instance
instance kitNameOk_persistent [RpcNames] : Persistent (kitNameOk (GF := GF)) := by
  unfold kitNameOk nameOk; infer_instance
instance codecSet_persistent : Persistent (codecSet (GF := GF)) := by
  unfold codecSet; infer_instance
instance rcvrOk_persistent (rcvr : GoInterface) (S : MethodSpec GF) :
    Persistent (rcvrOk (GF := GF) rcvr S) := by
  unfold rcvrOk; infer_instance
instance connIface_persistent (cv : GoInterface) (cid : w64) (side : Bool) :
    Persistent (connIface (GF := GF) cv cid side) := by
  unfold connIface; infer_instance

end node

end net.rpc

end Perennial
