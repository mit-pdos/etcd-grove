/-
`cr.abortPendingRead()` (the model's `server.go`) in the background phase (`startBackgroundRead` ran:
the main thread holds its halves of `γ.ph`, at "background", and of `γ.r`, at the head `hs`): under
the mutex, if the background read still runs (`inRead`), `aborted` set, the read deadline set in
the past (`aLongTimeAgo`) and the condition variable waited on until it is done, then the deadline
cleared; in the end the main phase again, with the fields, the byte buffer and the reader's token
back with the main thread (`crOwn`). Proved in `Net/Proof/net/http/connReader__abortPendingRead.lean`.
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
abbrev connReader.abortPendingRead.spec : Prop :=
  ∀ (cr : Loc) (γ : CrNames) (t : Loc) (cn : Nat) (a : GoString) (la ra : GoInterface)
    (P : Proto GF) (hs : List w8) (Z : Nat → IProp GF) (tm : time.Time),
  {{ crIs cr γ cn P hs Z ∗ globalAddr net.http.aLongTimeAgo ↦□ tm ∗
      structFieldRef net.http.connReader go!"rwc" cr ↦□
        interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t ∗
      connAt t cn true a la ra ∗ connIs (Gg := hG.goose_globalGS) cn ∗
      ghostVar γ.ph (1 : Qp).half true ∗ ghostVar γ.r (1 : Qp).half hs }}
    (App (Val (cr @!! go.GoType.PointerType net.http.connReader.ty @!! go!"abortPendingRead"))
      (Val #()))
  {{ RET #(); ghostVar γ.ph (1 : Qp).half false ∗ ghostVar γ.r (1 : Qp) hs ∗
      crOwn cr cn P hs Z }}

end spec

end net.http
end Perennial
