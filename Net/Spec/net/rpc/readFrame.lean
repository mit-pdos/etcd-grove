/-
`readFrame(r)` on an `io.Reader` `r` holding the end `s` of the connection `cn`: the next frame's
8-byte length, then (if at most `maxFrame`) its payload, each by `readFull` (`first` for the
length only). The reads go through the caller's reader predicate `P` and accessor, as in
`readFull.spec`. It returns `(p, nil)` with what it read a whole frame `frameOf pl` and `p` a fresh
slice of the payload `pl` (at most `maxFrameN` bytes); or `(nil, err)`: `errFrame` (`ef`, which
holds `errors.New("rpc: malformed frame")`) after a length beyond `maxFrame` (what it read: the
8 bytes of that length), or `readFull`'s error (`readErr`, with what it read: `io.EOF` only when it
read nothing) with what the failed `Read` gave the caller (`F`, `readFull.spec`). Proved in
`Net/Proof/net/rpc/readFrame.lean`.
-/
module

public import Net.Spec.net.rpc.readFull

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace net.rpc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions]

/-- See the file header. -/
abbrev readFrame.spec : Prop :=
  ∀ (t : Loc) (cn : Nat) (s : Bool) (a : GoString) (la ra : GoInterface)
    (P : List w8 → IProp GF) (F : IProp GF) (eof ueof ed ef : GoInterface),
  {{ net.connAt (GF := GF) t cn s a la ra ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
      globalAddr io.EOF ↦□ eof ∗ globalAddr io.ErrUnexpectedEOF ↦□ ueof ∗
      globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed ∗ globalAddr net.rpc.errFrame ↦□ ef ∗
      errors.newVar net.rpc.errFrame go!"rpc: malformed frame" ∗ P [] ∗
      □ (∀ (got : List w8) (m : Nat), P got -∗
        |={⊤,∅}=> ∃ st d, netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn s st ∗
          netDir (extGlobalGS netExt (G := hG.goose_globalGS)) cn (!s) d ∗
          ∀ r d', ⌜ReadOutcome st d m r d'⌝ -∗
            netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn s st -∗
            netDir (extGlobalGS netExt (G := hG.goose_globalGS)) cn (!s) d' ={∅,⊤}=∗
              P (got ++ r.got) ∗ (⌜∀ bs, r ≠ .bytes bs⌝ -∗ F)) }}
    (App (Val (@! net.rpc.readFrame))
      (Val #(interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t)))
  {{ (p : GoSlice) (err : GoInterface), RET (PairV #p #err); ∃ got : List w8, P got ∗
      ((∃ pl : List w8, ⌜err = interface.nil ∧ got = frameOf pl ∧ pl.length ≤ maxFrameN⌝ ∗
          p ↦* pl ∗ ownSliceCap w8 p (DFrac.own 1)) ∨
        ⌜err ≠ interface.nil⌝ ∗
          (⌜err = ef ∧ got.length = 8 ∧ maxFrameN < uint.nat (leToU64 got)⌝ ∨
            readErr la ra eof ueof ed true got err ∗ F)) }}

end spec

end net.rpc
end Perennial
