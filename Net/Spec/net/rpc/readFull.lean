/-
`readFull(r, b, first)` on an `io.Reader` `r` holding the end `s` of the connection `cn`
(`connAt`, its addresses `la`, `ra`): `r.Read`s into the rest of `b` until it is full or a read
fails (gob's `recvMessage`, which the model's frames reproduce). As `wire.ReadFull`
(`Net/Spec/.../wire/ReadFull.lean`), the caller makes the reads through a reader predicate `P got`
(`got`: the bytes read so far, the start of `b`) and an accessor used once per `Read` (a reader of
the library `GooseLang/Ext/Net/Proto.lean` uses `readP` and `readP_acc`,
`Net/Proof/net/rpc/Wire.lean`).

It returns `nil` exactly when `b` is full of the bytes read (an empty `b` reads nothing). Otherwise
`got` is not all of `b`, and the error is `io.EOF` when the connection ended before any byte and
`first` (between two frames), `io.ErrUnexpectedEOF` when it ended after some byte or with
`first = false` (within a frame), or the `Read`'s `*OpError` (`resErr` of a failure kind, D14).
Proved in `Net/Proof/net/rpc/readFull.lean`.
-/
module

public import Net.Proof.net.rpc.Base
public import Net.Proof.net.Base
public import Perennial.Proof.io.Base

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

/-- What `readFull` and `readFrame` return on a failure, besides `nil`: `io.EOF` (`eof`), only with
nothing read (`got = []`) when `first`; `io.ErrUnexpectedEOF` (`ueof`); or the `Read`'s error, the
`*OpError` of a failure kind. -/
def readErr (la ra eof ueof ed : GoInterface) (first : Bool) (got : List w8)
    (err : GoInterface) : IProp GF :=
  iprop(⌜err = eof ∧ got = [] ∧ first = true⌝ ∨ ⌜err = ueof⌝ ∨
    ∃ k, net.resErr (some k) go!"read" la ra (some ed) (· = go!"read") err)

instance readErr_persistent (la ra eof ueof ed : GoInterface) (first : Bool) (got : List w8)
    (err : GoInterface) : Persistent (readErr (GF := GF) la ra eof ueof ed first got err) := by
  unfold readErr; infer_instance

/-- See the file header. -/
abbrev readFull.spec : Prop :=
  ∀ (t : Loc) (cn : Nat) (s : Bool) (a : GoString) (la ra : GoInterface) (b : GoSlice)
    (bs0 : List w8) (first : Bool) (P : List w8 → IProp GF) (eof ueof ed : GoInterface),
  {{ net.connAt (GF := GF) t cn s a la ra ∗ b ↦* bs0 ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
      globalAddr io.EOF ↦□ eof ∗ globalAddr io.ErrUnexpectedEOF ↦□ ueof ∗
      globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed ∗ P [] ∗
      □ (∀ (got : List w8) (m : Nat), P got -∗
        |={⊤,∅}=> ∃ st d, netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn s st ∗
          netDir (extGlobalGS netExt (G := hG.goose_globalGS)) cn (!s) d ∗
          ∀ r d', ⌜ReadOutcome st d m r d'⌝ -∗
            netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn s st -∗
            netDir (extGlobalGS netExt (G := hG.goose_globalGS)) cn (!s) d' ={∅,⊤}=∗
              P (got ++ r.got)) }}
    (App (App (App (Val (@! net.rpc.readFull))
      (Val #(interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t))) (Val #b)) (Val #first))
  {{ (err : GoInterface), RET #err; ∃ (got bs' : List w8), P got ∗ b ↦* bs' ∗
      ⌜bs'.length = bs0.length ∧ got <+: bs'⌝ ∗
      (⌜err = interface.nil ∧ got = bs'⌝ ∨
        ⌜got ≠ bs'⌝ ∗ readErr la ra eof ueof ed first got err) }}

end spec

end net.rpc
end Perennial
