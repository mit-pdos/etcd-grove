/-
The net/rpc model's codec registry, as the specs see it (`codec.go`: `Codec`, `SetCodec`,
`getCodec`). A program registers one `*Codec` (generated for its types by `rpcgen.py`), whose
functions stand in for gob and reflection.

* `CodecSpec GF`: what the program's proof chooses its codec to meet, as predicate transformers
  (dsverify's `RpcCodec`, `Harness/Proof/net/rpc/Proto.lean`, without its `call` and `methods`,
  which were its own dispatch: here the server's dispatch is net/rpc's own code, through the
  `Receiver`'s `Method`s): `enc v Ψ` is what `Encode(v)` needs, and it returns a fresh slice of
  bytes `bs` with `Ψ bs`; `dec bs ptr Ψ` is what `Decode(bs, ptr)` needs, and it returns `nil`
  with `Ψ true` or an error (some error, `errAny`) with `Ψ false`.
* `codecIs C c` (persistent): `c` holds a `Codec` whose `Encode` and `Decode` meet `C`
  (`encOk`, `decOk`; a decoding error is an `errors.New` error, `decErr`, as the generated codec's
  `rpcErrDecode()`). The `Receiver`'s obligations are the server's (not yet stated:
  `notes/dsverify-net-port-plan.md`, phase 5.2).
* The registry: `codecMu`'s invariant `codecInv` holds half of `codec`'s points-to; the other half
  is `codecUnset` (at `nil`, the package's initial state) until `SetCodec` writes it and keeps it
  for good (`codecSet C`, persistent: what `getCodec` needs). So `getCodec` after a `SetCodec`
  finds the registered codec, and a second `SetCodec` (which panics) has no `codecUnset` to start
  from.
-/
module

public import Net.Proof.net.rpc.Base
public import Net.Proof.models_lab.Errors
public import Perennial.Proof.sync.Base
public import Perennial.Proof.errors.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace net.rpc

/-- See the file header. -/
structure CodecSpec [GooseExts] (GF : BundledGFunctors) where
  enc : GoInterface → (List w8 → IProp GF) → IProp GF
  dec : List w8 → GoInterface → (Bool → IProp GF) → IProp GF

section errs
variable [GooseExts] [go_gctx : GoGlobalContext]

/-- The `error` `rpc.ServerError(msg)` (Goose converts a value of the named string type to an
interface as `interface.mkOk ServerError.ty #msg`). -/
def serverErr (msg : GoString) : GoInterface :=
  interface.mkOk net.rpc.ServerError.ty #msg

/-- `err`'s dynamic type is not `net/rpc.ServerError` (`nil` is not one either): a comma-ok
assertion `err.(rpc.ServerError)` fails. -/
def notServerErr (err : GoInterface) : Prop :=
  ∀ e : GoInterfaceOk, err = interface.ok e → e.ty ≠ net.rpc.ServerError.ty

theorem serverErr_ne_nil (msg : GoString) : serverErr msg ≠ interface.nil := by
  unfold serverErr interface.mkOk; simp

theorem notServerErr_serverErr (msg : GoString) : ¬ notServerErr (serverErr msg) := by
  intro h
  exact h _ rfl rfl

end errs

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions]

/-- `Encode`'s function `fe` meets `C.enc`. -/
def encOk (C : CodecSpec GF) (fe : GoFunc) : IProp GF :=
  iprop(□ ∀ (v : GoInterface) (Ψ : List w8 → IProp GF) (Φ : val → IProp GF),
    C.enc v Ψ -∗
    ▷ (∀ (sl : GoSlice) (bs : List w8), sl ↦* bs -∗ ownSliceCap w8 sl (DFrac.own 1) -∗ Ψ bs -∗
        Φ #sl) -∗
    WP (App (Val #fe) (Val #v)) {{ Φ }})

/-- A decoding error: a fresh `errors.New` error (an `*errors.errorString`) whose `Error()` returns
its message `msg`, not empty, persistently. The generated codec's `Decode` fails only with
`rpcErrDecode()`, `errors.New("net/rpc model: malformed value")` (`models/net/rpc/rpcgen_core.py`).
What the client needs of it: not a `ServerError`, an `Error()`, and a pointer, which `==` compares
(`input`'s `err == io.EOF`). What the server needs: a message that is not empty, so that the error
response it sends for a request whose body does not decode is one (`sendResponse` with a
message `""` would encode the placeholder `invalidRequest`, a type no generated codec lists). -/
def decErr (err : GoInterface) : IProp GF :=
  iprop(∃ (x : Loc) (msg : GoString),
    ⌜err = interface.mkOk (go.GoType.PointerType errors.errorString.ty) #x ∧ msg ≠ []⌝ ∗
    □ ∀ Φ : val → IProp GF, ▷ Φ #msg -∗
      WP (App (Val #(methods (go.GoType.PointerType errors.errorString.ty) go!"Error" #x))
        (Val #())) {{ Φ }})

instance decErr_persistent (err : GoInterface) : Persistent (decErr (GF := GF) err) := by
  unfold decErr; infer_instance

/-- `Decode`'s function `fd` meets `C.dec`; its errors are decoding errors (`decErr`). -/
def decOk (C : CodecSpec GF) (fd : GoFunc) : IProp GF :=
  iprop(□ ∀ (data : GoSlice) (dq : DFrac) (bs : List w8) (ptr : GoInterface)
      (Ψ : Bool → IProp GF) (Φ : val → IProp GF),
    data ↦*{dq} bs -∗ C.dec bs ptr Ψ -∗
    ▷ (∀ (err : GoInterface) (ok : Bool), data ↦*{dq} bs -∗ ⌜err = interface.nil ↔ ok = true⌝ -∗
        Ψ ok -∗ (if ok then iprop(True) else decErr err) -∗ Φ #err) -∗
    WP (App (App (Val #fd) (Val #data)) (Val #ptr)) {{ Φ }})

/-- `c` holds a `Codec` whose `Encode` and `Decode` meet `C` (persistent). -/
def codecIs (C : CodecSpec GF) (c : Loc) : IProp GF :=
  iprop(∃ v : net.rpc.Codec, c ↦□ v ∗ encOk C v.Encode' ∗ decOk C v.Decode')

/-- `codecMu`'s invariant: half of `codec`'s points-to. -/
def codecInv : IProp GF :=
  iprop(∃ c : Loc, typedPointsto (globalAddr net.rpc.codec) c (DFrac.own (1 : Qp).half))

/-- No codec is registered yet (the package's initial state): the other half, at `nil`. -/
def codecUnset : IProp GF :=
  typedPointsto (globalAddr net.rpc.codec) null (DFrac.own (1 : Qp).half)

/-- A codec meeting `C` is registered, for good (persistent; `SetCodec`'s). -/
def codecSet (C : CodecSpec GF) : IProp GF :=
  iprop(isPkgInit (PROP := IProp GF) pkg_id.sync ∗ sync.isMutex (globalAddr net.rpc.codecMu) codecInv ∗
    ∃ c : Loc, ⌜c ≠ null⌝ ∗ globalAddr net.rpc.codec ↦□ c ∗ codecIs C c)

instance codecIs_persistent (C : CodecSpec GF) (c : Loc) : Persistent (codecIs (GF := GF) C c) := by
  unfold codecIs encOk decOk; infer_instance

instance codecSet_persistent (C : CodecSpec GF) : Persistent (codecSet (GF := GF) C) := by
  unfold codecSet; infer_instance

/-- What a body read needs to decode into `body` from the decoding resource `D` (persistent):
nothing for a `nil` body (the frame is discarded), else a registered codec meeting `C` and, from
`D`, its `dec` of any payload, `Θ pl` its outcome. -/
def bodyDec (C : CodecSpec GF) (body : GoInterface) (D : IProp GF)
    (Θ : List w8 → Bool → IProp GF) : IProp GF :=
  match body with
  | interface.nil => iprop(True)
  | interface.ok _ => iprop(codecSet C ∗ □ (D -∗ ∀ pl, C.dec pl body (Θ pl)))

instance bodyDec_persistent (C : CodecSpec GF) (body : GoInterface) (D : IProp GF)
    (Θ : List w8 → Bool → IProp GF) : Persistent (bodyDec C body D Θ) := by
  cases body <;> unfold bodyDec <;> infer_instance

/-- What a body read of the payload `pl` gives: `nil` and `D` for a `nil` body; else the
decoding's outcome. -/
def bodyRes (body : GoInterface) (D : IProp GF) (Θ : List w8 → Bool → IProp GF) (pl : List w8)
    (err : GoInterface) : IProp GF :=
  match body with
  | interface.nil => iprop(⌜err = interface.nil⌝ ∗ D)
  | interface.ok _ => iprop(∃ ok : Bool, ⌜err = interface.nil ↔ ok = true⌝ ∗ Θ pl ok ∗
      (if ok then iprop(True) else decErr err))

end defs

end net.rpc
end Perennial
