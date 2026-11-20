/-
`c.Write(b)` on a `*TCPConn` (`net.go`, promoted from `*conn`): in the model
(`TrustedCode/net.lean`, `conn.Write.impl`), the extension's `Write` of `b`'s bytes. With the
end's writer token (`sendTok cid side P W`, `W` written so far) and the protocol of `W ++ bs`
(`□ P cid (W ++ bs)`): the first `n` bytes of `bs` are added to what was written (all of them
when there is no error; they may be lost in a break). The error is `nil` exactly on success,
an `*OpError` of `"write"` otherwise (`connErr`). A call through the `net.Conn` interface
holding `c` reduces to this one. Proved in `Proof/net/TCPConn__Write.lean`.
-/
module

public import Harness.Proof.net.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI NetConn

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netConnExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [net.Assumptions] [net.model.Assumptions]

/-- See the file header. -/
abbrev net.TCPConn.Write.spec : Prop :=
  ∀ (c : Loc) (cid : w64) (side : Bool) (b : GoSlice) (bs : List w8) (dq : DFrac)
    (P : Proto GF) (W : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net ∗ net.ownTCPConn (GF := GF) c cid side ∗
      sendTok cid side P W ∗ □ P cid (W ++ bs) ∗ b ↦*{dq} bs }}
    (App (Val (c @!! go.GoType.PointerType net.TCPConn.ty @!! go!"Write")) (Val #b))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
      ∃ (k : Nat) (code : w64),
      ⌜n = W64 k ∧ k ≤ bs.length ∧ (err = interface.nil ↔ code = errNone) ∧
        (err = interface.nil → k = bs.length)⌝ ∗
      b ↦*{dq} bs ∗ sendTok cid side P (W ++ bs.take k) ∗ net.connErr go!"write" code err }}

end spec

end Perennial
