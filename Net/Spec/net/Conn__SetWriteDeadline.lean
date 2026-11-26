/-
`c.SetWriteDeadline(tm)` on a `Conn` `c` that is the end `s` of a TCP connection `cn`
(`connAt`), through the interface (stated on the resolved method; `conn.SetWriteDeadline.impl`, promoted, the model
`model.setDeadline`, `Net/TrustedCode/net.lean`): the extension's `SetDeadline` of the write
deadline only (kind `2`), whose outcome (`DeadlineOutcome`, `GooseLang/Ext/Net/Impl.lean`, D5) the
caller takes by a logically atomic update over the end's state (`netEnd`): on a closed end
`closed`; otherwise the write deadline set, unless `tm` is Go's zero time (`timeIsZero` of its two
words, `Time.IsZero`), which clears it. The deadline's value is not modeled: with a deadline set,
an operation may time out. Its result `Q res` is handed back with the error: `nil` for success,
else the `*OpError{Op: "set", Source: nil, Addr: la}` of the failure's kind (`resErr`).
As `Conn.SetDeadline.spec`; added 2026-11-19 for the kits' net/rpc, net/http and gRPC models,
which set it. Proved in
`Net/Proof/net/Conn__SetWriteDeadline.lean`.
-/
module

public import Net.Proof.net.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace net

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.Assumptions]

/-- See the file header. -/
abbrev Conn.SetWriteDeadline.spec : Prop :=
  ∀ (t : Loc) (cn : Nat) (s : Bool) (a : GoString) (la ra : GoInterface) (tm : time.Time)
    (Q : Option NetErr → IProp GF),
  {{ connAt (GF := GF) t cn s a la ra ∗
      (|={⊤,∅}=> ∃ st, netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn s st ∗
        ∀ res st', ⌜DeadlineOutcome st (W64 2) (!timeIsZero tm.wall' tm.ext') res st'⌝ -∗
          netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn s st' ={∅,⊤}=∗ Q res) }}
    (App (Val #(methods (go.GoType.PointerType TCPConn.ty) go!"SetWriteDeadline" #t)) (Val #tm))
  {{ (err : GoInterface), RET #err;
      ∃ res, Q res ∗ resErr res go!"set" interface.nil la none (· = go!"set") err }}

end spec

end net
end Perennial
