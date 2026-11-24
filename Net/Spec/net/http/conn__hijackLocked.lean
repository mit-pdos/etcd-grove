/-
`c.hijackLocked()` (the model's `server.go`), `c.mu` held, the connection not hijacked yet, the
background read started on its reader `cr` (the main thread's halves of `γ.ph` at "background" and
of `γ.r` at the head `hs`), nothing written by the acceptor (`sendTok cn true Q []`): the background
read aborted (`abortPendingRead`), `hijackedv` set, both deadlines cleared, the reader's byte refuted
(a byte past the head gives `Z cn`, which `zLaw` refutes with nothing written), the writer reset to
the connection, a `bufio.ReadWriter` made, the connection untracked (`setState(StateHijacked)`);
it returns the connection (`*TCPConn` `t`) and `nil`, with the reader's token at exactly `hs` and
the reader's fields with the main thread. Proved in `Net/Proof/net/http/conn__hijackLocked.lean`.
-/
module

public import Net.Proof.net.http.ServerConn
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
abbrev conn.hijackLocked.spec : Prop :=
  ∀ (c cr s : Loc) (γ : CrNames) (t : Loc) (cn : Nat) (a : GoString) (la ra : GoInterface)
    (P Q : Proto GF) (hs : List w8) (Z : Nat → IProp GF) (tm : time.Time) (br bw : Loc)
    (sz : Nat) (b : Bool),
  {{ structFieldRef net.http.conn go!"hijackedv" c ↦ false ∗
      structFieldRef net.http.conn go!"r" c ↦□ cr ∗
      structFieldRef net.http.conn go!"rwc" c ↦□
        interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t ∗
      structFieldRef net.http.conn go!"bufr" c ↦□ br ∗
      structFieldRef net.http.conn go!"bufw" c ↦□ bw ∗ EtcdGrove.bufio.rawWriter (GF := GF) bw sz ∗
      structFieldRef net.http.conn go!"server" c ↦□ s ∗ srvConst s ∗
      (∃ v : w64, sync.atomic.ownUint64 (structFieldRef net.http.conn go!"curState" c)
        (DFrac.own 1) v) ∗
      crIs cr γ cn P hs Z ∗ globalAddr net.http.aLongTimeAgo ↦□ tm ∗
      structFieldRef net.http.connReader go!"rwc" cr ↦□
        interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t ∗
      ghostVar γ.ph (1 : Qp).half true ∗ ghostVar γ.r (1 : Qp).half hs ∗
      connAt t cn true a la ra ∗ sendTok (Gg := hG.goose_globalGS) cn true Q [] ∗ zLaw Z Q ∗
      rdlTok (Gg := hG.goose_globalGS) cn true b }}
    (App (Val (c @!! go.GoType.PointerType net.http.conn.ty @!! go!"hijackLocked")) (Val #()))
  {{ (buf : Loc), RET (PairV (PairV #(interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t)
        #buf) #(interface.nil : GoInterface));
      structFieldRef net.http.conn go!"hijackedv" c ↦ true ∗ EtcdGrove.bufio.rawWriter bw sz ∗
      (∃ v : w64, sync.atomic.ownUint64 (structFieldRef net.http.conn go!"curState" c)
        (DFrac.own 1) v) ∗
      recvTok (Gg := hG.goose_globalGS) cn true P hs ∗ sendTok (Gg := hG.goose_globalGS) cn true Q [] ∗
      crLeft cr γ hs ∗ ∃ b' : Bool, rdlTok (Gg := hG.goose_globalGS) cn true b' }}

end spec

end net.http
end Perennial
