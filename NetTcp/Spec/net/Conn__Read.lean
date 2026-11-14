/-
`c.Read(b)` on a `Conn` `c` that is the end `s` of a TCP connection `cn` (`isConn`), through the
interface (a `*TCPConn`, whose `Read` is `conn`'s, promoted; the model `conn.Read.impl`,
`NetTcp/TrustedCode/net.lean`): the extension's `Read` of `len(b)` bytes, whose outcome
(`ReadOutcome`, `GooseLang/Ext/Tcp/Impl.lean`, D1) the caller takes by a logically atomic update over
the end's state and the direction towards it (`tcpEnd`, `tcpDir`), then the bytes copied into `b`.
The update's result `Q r` is handed back with what the call returns (`ReadOut`): `(len bs, nil)`
and `b` starting with `bs` for bytes, `(0, io.EOF)` for EOF, `(0, err)` with an `*OpError` for an
error, `b` unchanged. Proved in `NetTcp/Proof/net/Conn__Read.lean`.
-/
module

public import NetTcp.Proof.net.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Tcp

namespace net

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt tcpExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.Assumptions] [field_sem : net.FieldAssumptions]

/-- What `c.Read(b)` returns for the extension's result `r`: the count `k`, the error `err` and
`b`'s bytes after, from its bytes before, `bs0`. -/
def ReadOut (bs0 : List w8) (r : ReadRes) (k : w64) (err eof : GoInterface) (bs' : List w8) :
    Prop :=
  match r with
  | .bytes bs => sint.nat k = min bs0.length bs.length ∧ err = interface.nil ∧
      bs' = bs.take bs0.length ++ bs0.drop bs.length
  | .eof => k = 0 ∧ err = eof ∧ bs' = bs0
  | _ => k = 0 ∧ netErr err ∧ bs' = bs0

/-- See the file header. -/
abbrev Conn.Read.spec : Prop :=
  ∀ (t : Loc) (cn : Nat) (s : Bool) (a : GoString) (b : GoSlice) (bs0 : List w8)
    (eof : GoInterface) (Q : ReadRes → IProp GF),
  {{ connAt (GF := GF) t cn s a ∗ b ↦* bs0 ∗ globalAddr io.EOF ↦□ eof ∗
      (|={⊤,∅}=> ∃ st d, tcpEnd (extGlobalGS tcpExt (G := hG.goose_globalGS)) cn s st ∗ tcpDir (extGlobalGS tcpExt (G := hG.goose_globalGS)) cn (!s) d ∗
        ∀ r d', ⌜ReadOutcome st d b.len.toNat r d' ∧ r ≠ .wait⌝ -∗
          tcpEnd (extGlobalGS tcpExt (G := hG.goose_globalGS)) cn s st -∗ tcpDir (extGlobalGS tcpExt (G := hG.goose_globalGS)) cn (!s) d' ={∅,⊤}=∗ Q r) }}
    (App (Val #(methods (go.GoType.PointerType TCPConn.ty) go!"Read" #t)) (Val #b))
  {{ (k : w64) (err : GoInterface), RET (PairV #k #err);
      ∃ (r : ReadRes) (bs' : List w8), Q r ∗ b ↦* bs' ∗ ⌜ReadOut bs0 r k err eof bs'⌝ }}

end spec

end net
end Perennial
