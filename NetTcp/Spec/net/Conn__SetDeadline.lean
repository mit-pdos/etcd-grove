/-
`c.SetDeadline(tm)` on a `Conn` `c` that is the end `s` of a TCP connection `cn` (`isConn`), through
the interface (`conn.SetDeadline.impl`, promoted), for any `time.Time` `tm` (the model does not
read it: a deadline in the past, in the future or cleared, `time.Time{}`, all record the same):
the extension's `SetDeadline`, whose outcome the caller takes by a logically atomic update over the
end's state: a failure of a closed end, which changes nothing, or the deadline recorded
(`TcpEnd.dl`, after which a failed operation does not break the end, `TcpEnd.onFail`). Its result
`Q ok` is handed back with the error: `nil` for `ok`, else an `*OpError`. Proved in
`NetTcp/Proof/net/Conn__SetDeadline.lean`.
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
abbrev Conn.SetDeadline.spec : Prop :=
  ∀ (t : Loc) (cn : Nat) (s : Bool) (a : GoString) (tm : time.Time) (Q : Bool → IProp GF),
  {{ connAt (GF := GF) t cn s a ∗
      (|={⊤,∅}=> ∃ st, tcpEnd (extGlobalGS tcpExt (G := hG.goose_globalGS)) cn s st ∗
        ∀ ok st', ⌜DeadlineOutcome st (W64 0) (!timeIsZero tm.wall' tm.ext') ok st'⌝ -∗
          tcpEnd (extGlobalGS tcpExt (G := hG.goose_globalGS)) cn s st' ={∅,⊤}=∗ Q ok) }}
    (App (Val #(methods (go.GoType.PointerType TCPConn.ty) go!"SetDeadline" #t)) (Val #tm))
  {{ (err : GoInterface), RET #err;
      ∃ ok, Q ok ∗ ⌜(ok = true → err = interface.nil) ∧ (ok = false → netErr err)⌝ }}

end spec

end net
end Perennial
