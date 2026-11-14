/-
`c.Write(b)` on a `Conn` `c` that is the end `s` of a TCP connection `cn` (`connAt`, with the end's
addresses `la`, `ra`), through the interface (`conn.Write.impl`, promoted): `b`'s bytes read (any
fraction), then the extension's `Write`, whose outcome (`WriteOutcome`,
`GooseLang/Ext/Tcp/Impl.lean`, D2, D15) the caller takes by a logically atomic update over the end's
state and the direction from it (`tcpEnd`, `tcpDir`). Its result `Q k res` is handed back with what
the call returns: `(k, nil)` if all was written (`res = none`), else `(k, err)` with the
`*OpError{Op: "write", Source: la, Addr: ra}` of the failure's kind (`resErr`, D14). Proved in
`NetTcp/Proof/net/Conn__Write.lean`.
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

/-- See the file header. -/
abbrev Conn.Write.spec : Prop :=
  ∀ (t : Loc) (cn : Nat) (s : Bool) (a : GoString) (la ra : GoInterface) (b : GoSlice)
    (bs : List w8) (dq : DFrac) (ed : GoInterface) (Q : Nat → Option TcpErr → IProp GF),
  {{ connAt (GF := GF) t cn s a la ra ∗ b ↦*{dq} bs ∗
      globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed ∗
      (|={⊤,∅}=> ∃ st d, tcpEnd (extGlobalGS tcpExt (G := hG.goose_globalGS)) cn s st ∗ tcpDir (extGlobalGS tcpExt (G := hG.goose_globalGS)) cn s d ∗
        ∀ k res d', ⌜WriteOutcome st d bs k res d'⌝ -∗ tcpEnd (extGlobalGS tcpExt (G := hG.goose_globalGS)) cn s st -∗
          tcpDir (extGlobalGS tcpExt (G := hG.goose_globalGS)) cn s d' ={∅,⊤}=∗ Q k res) }}
    (App (Val #(methods (go.GoType.PointerType TCPConn.ty) go!"Write" #t)) (Val #b))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
      ∃ k res, Q k res ∗ b ↦*{dq} bs ∗ ⌜n = BitVec.ofNat 64 k⌝ ∗
        resErr res go!"write" la ra (some ed) (· = go!"write") err }}

end spec

end net
end Perennial
