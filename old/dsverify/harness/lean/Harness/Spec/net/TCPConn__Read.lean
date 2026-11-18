/-
`c.Read(b)` on a `*TCPConn` (`net.go`, promoted from `*conn`): in the model
(`TrustedCode/net.lean`, `conn.Read.impl`), the extension's `Read` of at most `len(b)` bytes,
copied into `b`. With the end's reader token (`recvTok cid side P R`, `R` read so far): the next
bytes `data` of the stream (at most `len(b)`, at least one on success unless `b` is empty, none
on error) are in `b`'s first `n` elements and added to what was read, and the reader learns the
protocol `P` of an extension of `R ++ data` (in `recvTok`). The error is `nil` on success, the
value of `io.EOF` at the end of the stream, an `*OpError` of `"read"` otherwise (`connErr`).
Stated for the program logic with later credits (`HasLC.hasLC`), as `NetConn.wp_Read` is. A
call through the `net.Conn` interface holding `c` reduces to this one (`method_interface_ok`).
Proved in `Proof/net/TCPConn__Read.lean`.
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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.Assumptions] [net.model.Assumptions]

/-- See the file header. -/
abbrev net.TCPConn.Read.spec : Prop :=
  ∀ (c : Loc) (cid : w64) (side : Bool) (b : GoSlice) (bs : List w8) (P : Proto GF)
    (R : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net ∗ net.ownTCPConn (GF := GF) c cid side ∗
      recvTok cid side P R ∗ b ↦* bs }}
    (App (Val (c @!! go.GoType.PointerType net.TCPConn.ty @!! go!"Read")) (Val #b))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
      ∃ (data : List w8) (code : w64),
      ⌜n = W64 data.length ∧ data.length ≤ bs.length ∧
        (err = interface.nil ↔ code = errNone) ∧ (err ≠ interface.nil → data = []) ∧
        (err = interface.nil → bs ≠ [] → data ≠ [])⌝ ∗
      b ↦* (data ++ bs.drop data.length) ∗ recvTok cid side P (R ++ data) ∗
      net.connErr go!"read" code err }}

end spec

end Perennial
