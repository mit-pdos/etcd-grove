/-
`cr.startBackgroundRead()` (the model's `server.go`) in the main phase (the main thread holds its
half of `γ.ph`, at "main", and the whole of `γ.r`, at the head `hs`; it owns the reader's fields, no
read running, no byte kept, the byte buffer and the reader's token at exactly `hs`): under the mutex,
`inRead` set, the read deadline cleared, and `backgroundRead` forked with the background reader's
token, the buffer and the reader's token; the fields go to the mutex invariant in the background
phase. In the end the main thread's halves of `γ.ph`, at "background", and of `γ.r`
(`abortPendingRead`'s precondition). Proved in
`Net/Proof/net/http/connReader__startBackgroundRead.lean`.
-/
module

public import Net.Proof.net.http.ConnReader
public import Net.Proof.net.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace net.http

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem' : net.http.Assumptions]
variable [π : NetProtoGS]

/-- See the file header. -/
abbrev connReader.startBackgroundRead.spec : Prop :=
  ∀ (cr : Loc) (γ : CrNames) (t : Loc) (cn : Nat) (a : GoString) (la ra : GoInterface)
    (P : Proto GF) (hs : List w8) (Z : Nat → IProp GF) (c : Loc) (ab fl : Bool)
    (arr : GoArray w8 1),
  {{ crIs cr γ cn P hs Z ∗ headLaw P hs Z ∗ readEnv ∗
      structFieldRef net.http.connReader go!"rwc" cr ↦□
        interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t ∗
      connAt t cn true a la ra ∗ connIs (Gg := hG.goose_globalGS) cn ∗
      ghostVar γ.ph (1 : Qp).half false ∗ ghostVar γ.r (1 : Qp) hs ∗
      structFieldRef net.http.connReader go!"conn" cr ↦ c ∗
      structFieldRef net.http.connReader go!"hasByte" cr ↦ false ∗
      structFieldRef net.http.connReader go!"inRead" cr ↦ false ∗
      structFieldRef net.http.connReader go!"aborted" cr ↦ ab ∗
      structFieldRef net.http.connReader go!"failed" cr ↦ fl ∗ crConnOk c ∗
      structFieldRef net.http.connReader go!"byteBuf" cr ↦ arr ∗
      recvTok (Gg := hG.goose_globalGS) cn true P hs }}
    (App (Val (cr @!! go.GoType.PointerType net.http.connReader.ty @!! go!"startBackgroundRead"))
      (Val #()))
  {{ RET #(); ghostVar γ.ph (1 : Qp).half true ∗ ghostVar γ.r (1 : Qp).half hs }}

end spec

end net.http
end Perennial
