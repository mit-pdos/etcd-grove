/-
`c.Read(b)` on a `Conn` `c` that is the end `s` of a TCP connection `cn` (`isConn`), through the
interface (a `*TCPConn`, whose `Read` is `conn`'s, promoted; the model `conn.Read.impl`,
`NetTcp/TrustedCode/net.lean`): the extension's `Read` of `len(b)` bytes, whose outcome the caller
takes by a logically atomic update over the end's state (`tcpEnd`; `ReadPost`, `Specs.lean`),
then the bytes copied into `b`. The update's result `Q (readRes bs code)` is handed back with
what the call returns: `(len bs, nil)` and `b` starting with `bs` for bytes (`code = 0`),
`(0, io.EOF)` for EOF (`code = 1`), `(0, err)` with an `*OpError` otherwise, `b` unchanged.
Proved in `NetTcp/Proof/net/Conn__Read.lean`.
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

/-- What a read that the extension answered with `bs` and `code` returns, `(k, err)`, and leaves
in the buffer `b` that held `bs0`. -/
def ReadOut (bs0 bs : List w8) (code k : w64) (err eof : GoInterface) (bs' : List w8) : Prop :=
  (code = 0 ∧ sint.nat k = min bs0.length bs.length ∧ err = interface.nil ∧
    bs' = bs.take bs0.length ++ bs0.drop bs.length) ∨
  (code = 1 ∧ k = 0 ∧ err = eof ∧ bs' = bs0) ∨
  (code ≠ 0 ∧ code ≠ 1 ∧ k = 0 ∧ netErr err ∧ bs' = bs0)

/-- See the file header. -/
abbrev Conn.Read.spec : Prop :=
  ∀ (t : Loc) (cn : Nat) (s : Bool) (a : GoString) (b : GoSlice) (bs0 : List w8)
    (eof : GoInterface) (Q : val → IProp GF),
  {{ connAt (GF := GF) t cn s a ∗ b ↦* bs0 ∗ globalAddr io.EOF ↦□ eof ∗
      (|={⊤,∅}=> ∃ st r, tcpEnd (extGlobalGS tcpExt (G := hG.goose_globalGS)) cn s st r ∗
        ∀ res, ReadPost (extGlobalGS tcpExt (G := hG.goose_globalGS)) cn s b.len st r res ={∅,⊤}=∗
          Q res) }}
    (App (Val #(methods (go.GoType.PointerType TCPConn.ty) go!"Read" #t)) (Val #b))
  {{ (k : w64) (err : GoInterface), RET (PairV #k #err);
      ∃ (bs : List w8) (code : w64) (bs' : List w8), Q (readRes bs code) ∗ b ↦* bs' ∗
        ⌜ReadOut bs0 bs code k err eof bs'⌝ }}

end spec

end net
end Perennial
