/-
`c.ReadRequestBody(body)` on the model's server codec `c` (`codec.go`), whose `rwc` holds the end
`s` of the connection `cn` (kept, `↦□`): `readFrame` of the next frame (through the caller's reader
predicate `P` and accessor, with what a failed `Read` gives, `F`, as `readFrame.spec`), then, unless
`body` is `nil` (the frame is discarded), the registered codec's `Decode` of its payload into `body`.

The caller's decoding resource `D` is what it gives up for a decoding; `bodyDecG C body D G Θ`
(persistent) says what it is worth: nothing for a `nil` body, else a registered codec meeting `C`
and, from `D`, the codec's `dec` into `body` of every payload `pl` with `G pl`, `Θ pl` its outcome.
The guard `G pl` comes from the caller's reader predicate once the frame is read: from
`P (frameOf pl)`, a step later, `P (frameOf pl)` again and `G pl` (the server's: the frame is the
argument bytes of the request whose deposit it holds, `req_guard`; a generated codec decodes only
bytes of the target's type, as `clientCodec.ReadResponseBody.spec`'s). It returns:

* after a whole frame `frameOf pl` (at most `maxFrameN` bytes): `nil` with `D` for a `nil` body;
  else the decoding's result `ok` with `Θ pl ok` (`nil` exactly when `ok`, otherwise a decoding
  error, `decErr`);
* or a read failure, with `D` back (nothing was decoded): `errFrame` (`ef`) after a length beyond
  `maxFrame` (what it read: those 8 bytes), or `readFrame`'s `readErr` with `F`.

Proved in `Net/Proof/net/rpc/serverCodec__ReadRequestBody.lean`.
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

/-- See the file header. -/
abbrev serverCodec.ReadRequestBody.spec : Prop :=
  ∀ (c t : Loc) (cn : Nat) (s : Bool) (a : GoString) (la ra : GoInterface) (body : GoInterface)
    (C : CodecSpec GF) (D : IProp GF) (G : List w8 → IProp GF) (Θ : List w8 → Bool → IProp GF)
    (P : List w8 → IProp GF) (F : IProp GF) (eof ueof ed ef : GoInterface),
  {{ structFieldRef net.rpc.serverCodec go!"rwc" c ↦□
        interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t ∗
      net.connAt (GF := GF) t cn s a la ra ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
      globalAddr io.EOF ↦□ eof ∗ globalAddr io.ErrUnexpectedEOF ↦□ ueof ∗
      globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed ∗ globalAddr net.rpc.errFrame ↦□ ef ∗
      errors.newVar net.rpc.errFrame go!"rpc: malformed frame" ∗ bodyDecG C body D G Θ ∗ D ∗ P [] ∗
      □ (∀ pl : List w8, ⌜pl.length ≤ maxFrameN⌝ -∗ P (frameOf pl) -∗
        ▷ (P (frameOf pl) ∗ G pl)) ∗
      □ (∀ (got : List w8) (m : Nat), P got -∗
        |={⊤,∅}=> ∃ st d, netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn s st ∗
          netDir (extGlobalGS netExt (G := hG.goose_globalGS)) cn (!s) d ∗
          ∀ r d', ⌜ReadOutcome st d m r d'⌝ -∗
            netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn s st -∗
            netDir (extGlobalGS netExt (G := hG.goose_globalGS)) cn (!s) d' ={∅,⊤}=∗
              P (got ++ r.got) ∗ (⌜∀ bs, r ≠ .bytes bs⌝ -∗ F)) }}
    (App (Val (c @!! go.GoType.PointerType net.rpc.serverCodec.ty @!! go!"ReadRequestBody"))
      (Val #body))
  {{ (err : GoInterface), RET #err; ∃ got : List w8, P got ∗
      ((∃ pl : List w8, ⌜got = frameOf pl ∧ pl.length ≤ maxFrameN⌝ ∗ bodyRes body D Θ pl err) ∨
        ⌜err ≠ interface.nil⌝ ∗ D ∗
          (⌜err = ef ∧ got.length = 8 ∧ maxFrameN < uint.nat (leToU64 got)⌝ ∨
            readErr la ra eof ueof ed true got err ∗ F)) }}

end spec

end net.rpc
end Perennial
