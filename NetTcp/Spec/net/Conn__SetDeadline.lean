/-
`c.SetDeadline(tm)` on a `Conn` `c` that is the end `s` of a TCP connection `cn` (`isConn`), through
the interface (stated on the resolved method; `conn.SetDeadline.impl`, promoted, the model
`model.setDeadline`, `NetTcp/TrustedCode/net.lean`): the extension's `SetDeadline` of both the read
and the write deadline, whose outcome (`DeadlineOutcome`, `GooseLang/Ext/Tcp/Impl.lean`, D5) the
caller takes by a logically atomic update over the end's state (`tcpEnd`): on a closed end an
error; otherwise both deadlines set, unless `tm` is Go's zero time (`timeIsZero` of its two words,
`Time.IsZero`), which clears them. The deadline's value is not modeled: with a deadline set, an
operation may time out. Its result `Q ok` is handed back with the error: `nil` for `ok`, else an
`*OpError`. Proved in `NetTcp/Proof/net/Conn__SetDeadline.lean`.
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
