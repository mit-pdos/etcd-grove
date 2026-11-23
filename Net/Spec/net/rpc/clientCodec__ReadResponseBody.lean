/-
`c.ReadResponseBody(body)` on the model's client codec `c` (`codec.go`), whose `rwc` holds the end
`s` of the connection `cn` (kept, `↦□`): `readFrame` of the next frame (through the caller's reader
predicate `P` and accessor, as `readFrame.spec`), then, unless `body` is `nil` (the frame is
discarded), the registered codec's `Decode` of its payload into `body`.

The caller's decoding resource `D` is what it gives up for a decoding; `bodyDec C body D Θ`
(persistent) says what it is worth: nothing for a `nil` body, else a registered codec meeting `C`
and, from `D`, the codec's `dec` of any payload into `body`, `Θ pl` its outcome. It returns:

* after a whole frame `frameOf pl` (at most `maxFrameN` bytes): `nil` with `D` for a `nil` body;
  else the decoding's result `ok` with `Θ pl ok` (`nil` exactly when `ok`, otherwise a decoding
  error, `decErr`);
* or a read failure (`errFrame`, `ef`, or `readFrame`'s `readErr`), with `D` back (nothing was
  decoded).

Proved in `Net/Proof/net/rpc/clientCodec__ReadResponseBody.lean`.
-/
module

public import Net.Spec.net.rpc.readFrame
public import Net.Proof.net.rpc.Codec

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace net.rpc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions] [field_sem : net.FieldAssumptions]

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

/-- See the file header. -/
abbrev clientCodec.ReadResponseBody.spec : Prop :=
  ∀ (c t : Loc) (cn : Nat) (s : Bool) (a : GoString) (la ra : GoInterface) (body : GoInterface)
    (C : CodecSpec GF) (D : IProp GF) (Θ : List w8 → Bool → IProp GF)
    (P : List w8 → IProp GF) (eof ueof ed ef : GoInterface),
  {{ structFieldRef net.rpc.clientCodec go!"rwc" c ↦□
        interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t ∗
      net.connAt (GF := GF) t cn s a la ra ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
      globalAddr io.EOF ↦□ eof ∗ globalAddr io.ErrUnexpectedEOF ↦□ ueof ∗
      globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed ∗ globalAddr net.rpc.errFrame ↦□ ef ∗
      errors.newVar net.rpc.errFrame go!"rpc: malformed frame" ∗ bodyDec C body D Θ ∗ D ∗ P [] ∗
      □ (∀ (got : List w8) (m : Nat), P got -∗
        |={⊤,∅}=> ∃ st d, netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn s st ∗
          netDir (extGlobalGS netExt (G := hG.goose_globalGS)) cn (!s) d ∗
          ∀ r d', ⌜ReadOutcome st d m r d'⌝ -∗
            netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn s st -∗
            netDir (extGlobalGS netExt (G := hG.goose_globalGS)) cn (!s) d' ={∅,⊤}=∗
              P (got ++ r.got)) }}
    (App (Val (c @!! go.GoType.PointerType net.rpc.clientCodec.ty @!! go!"ReadResponseBody"))
      (Val #body))
  {{ (err : GoInterface), RET #err; ∃ got : List w8, P got ∗
      ((∃ pl : List w8, ⌜got = frameOf pl ∧ pl.length ≤ maxFrameN⌝ ∗ bodyRes body D Θ pl err) ∨
        ⌜err ≠ interface.nil⌝ ∗ D ∗
          (⌜err = ef⌝ ∨ readErr la ra eof ueof ed true got err)) }}

end spec

end net.rpc
end Perennial
