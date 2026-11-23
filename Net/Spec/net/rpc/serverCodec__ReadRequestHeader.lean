/-
`c.ReadRequestHeader(r)` on the model's server codec `c` (`codec.go`), whose `rwc` holds the end
`s` of the connection `cn` (kept, `↦□`) and whose sticky read error `rerr` the caller owns (`r0`): with
`r0` not `nil` it returns `r0` and reads nothing; otherwise `readFrame` of the next frame (through the caller's reader
predicate `P` and accessor, as `readFrame.spec`), its payload parsed as a request header. It
returns `nil` when what it read is a frame of `reqHdr seq sm` (at most `maxFrameN` bytes), and then `r`'s `ServiceMethod`,
`Seq` are `sm`, `seq`; otherwise an error, `r` unchanged: `errFrame` (`ef`; a frame
that is not a request header, or too long) or `readFrame`'s (`readErr`), which `rerr` may then
hold (a frame read's error does, a header that does not parse does not). Proved in
`Net/Proof/net/rpc/serverCodec__ReadRequestHeader.lean`.
-/
module

public import Net.Spec.net.rpc.readFrame

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
abbrev serverCodec.ReadRequestHeader.spec : Prop :=
  ∀ (c t : Loc) (cn : Nat) (s : Bool) (a : GoString) (la ra : GoInterface) (r : Loc)
    (rv : net.rpc.Request) (r0 : GoInterface) (P : List w8 → IProp GF) (eof ueof ed ef : GoInterface),
  {{ structFieldRef net.rpc.serverCodec go!"rwc" c ↦□
        interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t ∗
      net.connAt (GF := GF) t cn s a la ra ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
      globalAddr io.EOF ↦□ eof ∗ globalAddr io.ErrUnexpectedEOF ↦□ ueof ∗
      globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed ∗ globalAddr net.rpc.errFrame ↦□ ef ∗
      errors.newVar net.rpc.errFrame go!"rpc: malformed frame" ∗ r ↦ rv ∗ P [] ∗
      structFieldRef net.rpc.serverCodec go!"rerr" c ↦ r0 ∗
      □ (∀ (got : List w8) (m : Nat), P got -∗
        |={⊤,∅}=> ∃ st d, netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn s st ∗
          netDir (extGlobalGS netExt (G := hG.goose_globalGS)) cn (!s) d ∗
          ∀ r d', ⌜ReadOutcome st d m r d'⌝ -∗
            netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn s st -∗
            netDir (extGlobalGS netExt (G := hG.goose_globalGS)) cn (!s) d' ={∅,⊤}=∗
              P (got ++ r.got)) }}
    (App (Val (c @!! go.GoType.PointerType net.rpc.serverCodec.ty @!! go!"ReadRequestHeader"))
      (Val #r))
  {{ (err : GoInterface), RET #err;
      (⌜r0 ≠ interface.nil ∧ err = r0⌝ ∗ P [] ∗ r ↦ rv ∗
          structFieldRef net.rpc.serverCodec go!"rerr" c ↦ r0) ∨
      (⌜r0 = interface.nil⌝ ∗ ∃ got : List w8, P got ∗
        ((∃ (seq : w64) (sm : GoString),
            ⌜err = interface.nil ∧ got = frameOf (reqHdr seq sm) ∧
              (reqHdr seq sm).length ≤ maxFrameN⌝ ∗
            r ↦ { rv with ServiceMethod' := sm, Seq' := seq } ∗
            structFieldRef net.rpc.serverCodec go!"rerr" c ↦ interface.nil) ∨
          ⌜err ≠ interface.nil⌝ ∗ r ↦ rv ∗ (⌜err = ef⌝ ∨ readErr la ra eof ueof ed true got err) ∗
            ∃ r1 : GoInterface, structFieldRef net.rpc.serverCodec go!"rerr" c ↦ r1 ∗
              ⌜r1 = interface.nil ∨ r1 = err⌝)) }}

end spec

end net.rpc
end Perennial
