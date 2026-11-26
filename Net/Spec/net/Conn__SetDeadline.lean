/-
`c.SetDeadline(tm)` on a `Conn` `c` that is the end `s` of a TCP connection `cn` (`connAt`), through
the interface (stated on the resolved method; `conn.SetDeadline.impl`, promoted, the model
`model.setDeadline`, `Net/TrustedCode/net.lean`): the extension's `SetDeadline` of both the read
and the write deadline, whose outcome (`DeadlineOutcome`, `GooseLang/Ext/Net/Impl.lean`, D5) the
caller takes by a logically atomic update over the end's state (`netEnd`): on a closed end
`closed`; otherwise both deadlines set, unless `tm` is Go's zero time (`timeIsZero` of its two
words, `Time.IsZero`), which clears them. The deadline's value is not modeled: with a deadline set,
an operation may time out. Its result `Q res` is handed back with the error: `nil` for success,
else the `*OpError{Op: "set", Source: nil, Addr: la}` of the failure's kind (`resErr`). Proved in
`Net/Proof/net/Conn__SetDeadline.lean`.
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
abbrev Conn.SetDeadline.spec : Prop :=
  ∀ (t : Loc) (cn : Nat) (s : Bool) (a : GoString) (la ra : GoInterface) (tm : time.Time)
    (Q : Option NetErr → IProp GF),
  {{ connAt (GF := GF) t cn s a la ra ∗
      (|={⊤,∅}=> ∃ st, netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn s st ∗
        ∀ res st', ⌜DeadlineOutcome st (W64 0) (!timeIsZero tm.wall' tm.ext') res st'⌝ -∗
          netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn s st' ={∅,⊤}=∗ Q res) }}
    (App (Val #(methods (go.GoType.PointerType TCPConn.ty) go!"SetDeadline" #t)) (Val #tm))
  {{ (err : GoInterface), RET #err;
      ∃ res, Q res ∗ resErr res go!"set" interface.nil la none (· = go!"set") err }}

end spec

end net
end Perennial
