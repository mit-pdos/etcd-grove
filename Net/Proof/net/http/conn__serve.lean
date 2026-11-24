/-
Proof of `Net/Spec/net/http/conn__serve.lean`. WIP (S5 session 9): the plan, step by step, over the
callees' specs taken as hypotheses (linked in `Net/Proof/net/http/Results.lean`). NOT LANDED.
-/
module

public import Net.Spec.net.http.conn__serve
public import Net.Spec.net.http.conn__readRequest
public import Net.Spec.net.http.conn__hijacked
public import Net.Spec.net.http.connReader__startBackgroundRead
public import Net.Spec.net.http.connReader__releaseConn
public import Net.Spec.net.http.response__Hijack
public import Net.Spec.net.Conn__RemoteAddr
public import Net.Spec.net.Conn__LocalAddr
public import Net.Spec.net.Conn__Close
public import Net.Spec.net.Conn__Write
public import Net.Spec.context.WithValuePtr
public import Net.Spec.context.WithCancelValBg
public import Net.Proof.net.http.ServerConnLemmas
public import Net.Proof.net.http.ServeDefs
public import Perennial.Spec.fmt.Fprintf

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net.http

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem' : net.http.Assumptions]
variable [package_sem : context.Assumptions] [bufio.Assumptions]
variable [π : NetProtoGS]

theorem conn.serve.wp_proof
    (wp_readRequest : conn.readRequest.spec (GF := GF) (hG := hG))
    (wp_hijacked : conn.hijacked.spec (GF := GF) (hG := hG))
    (wp_sbr : connReader.startBackgroundRead.spec (GF := GF) (hG := hG))
    (wp_release : connReader.releaseConn.spec (GF := GF) (hG := hG))
    (wp_Hijack : response.Hijack.spec (GF := GF) (hG := hG))
    (wp_RemoteAddr : net.Conn.RemoteAddr.spec (GF := GF) (hG := hG))
    (wp_LocalAddr : net.Conn.LocalAddr.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_WithValue : context.WithValue.specPtr (GF := GF) (hG := hG))
    (wp_WithCancelBg : context.WithCancel.specValBg (GF := GF) (hG := hG))
    (wp_Fprintf : fmt.Fprintf.spec (GF := GF) (hG := hG))
    (wp_RReset : EtcdGrove.bufio.Reader.Reset.spec (GF := GF) (hG := hG))
    (wp_NewReader : EtcdGrove.bufio.NewReader.specFresh (GF := GF) (hG := hG))
    (wp_WReset : EtcdGrove.bufio.Writer.Reset.spec (GF := GF) (hG := hG))
    (wp_NewWriterSize : EtcdGrove.bufio.NewWriterSize.specRep (GF := GF) (hG := hG)) :
    conn.serve.spec (GF := GF) (hG := hG) := by
  intro c s t cn a la ra P Q Z path ctx hp hlen hQ
  wp_start as ⟨#Henv, #Hrenv, #Hctxi, #Hsc, #Hsd, #Hss, #Hkeys, #Hpools, #Hrpool, ⟨%tm, #Htm⟩, #Hbg, Hc,
    #Hca, Hsend, Hrecv, Hfresh, Hrdl, #Hhl, #Hzl, #HQ400, #Hh, Htok⟩
  wp_apply wp_with_defer_recover as %defer %pnc defer pnc
  iunfold ctxKeys at Hkeys
  icases Hkeys with ⟨%sk, %lk, #Hsk, #Hlk⟩
  wp_auto
  sorry
/-PLAN
  -- 1. `with_defer_recover`; RemoteAddr (+ `TCPAddr.String`: `wp_net_AnyString`), store remoteAddr;
  --    `WithValue(ctx, LocalAddrContextKey, LocalAddr())` (wp_WithValue; ctxBg grows by one).
  -- 2. the two `connectionStater` assertions on a `*TCPConn` fail (TypeAssert2 to an interface).
  -- 3. `WithCancel` (wp_WithCancelBg); store `c.cancelCtx`, persist it; `defer cancelCtx()`.
  -- 4. `&connReader{conn: c, rwc: c.rwc}`: iStructNamed; ghost names (ph halves, bg token, r := hs);
  --    `sync.init_Mutex` with `crInv` (cond nil, phase false: token); `crIs`; `crMain cr γ cn P Q c [] 0`.
  --    curReq invariant (`inv curReqN (curReqInv c)`) from connNew's ownPointer; `crConnOk c`.
  -- 5. `newBufioReader(c.r)`: a freshReader variant of `wp_newBufioReader` (pool: Reset gives it;
  --    NewReader: unfold NewReaderSize/reset); `newBufioWriterSize(checkConnErrorWriter{c}, 4096)`.
  -- 6. readHeaderTimeout (srvServe: 0; srvDflt ReadTimeout 0): no deadline; protocols(): Protocols nil,
  --    TLSNextProto nil (lookup on a nil map), HTTP1 set, UnencryptedHTTP2 unset; `sync.init_Mutex` for
  --    `c.mu` with `connMuInv c γh` (hijackedv false).
  -- 7. `c.readRequest(ctx)` (wp_readRequest; c.bufr at 1); `c.r.remain != initialReadLimitSize()`
  --    -> setState(StateActive) (`wp_setState`); shuttingDown: `Bool.Load` on srvServe's discarded false.
  -- 8. error: `err == errTooLarge` false (`httpEnv_errTooLarge`: messages differ from io.EOF's,
  --    ErrUnexpectedEOF's, "malformed HTTP "...; other types differ); isUnsupportedTEError false;
  --    isCommonNetReadError: either way; statusError assertion false; `fmt.Fprintf(c.rwc, 400)`:
  --    SprintfOut of a verb-free format is the format; the write through `sendTok` with `HQ400`
  --    (`conn_streamWriterOk`/`write_acc`). Return: defers: cancel (cancelSpec), recover nil,
  --    inFlightResponse nil, hijacked false -> c.close(): finalFlush (putBufioReader on rawReader,
  --    `bufw.Flush()` on a raw writer: nothing to write, putBufioWriter), Conn.Close (`close_au`),
  --    setState(StateClosed).
  -- 9. success: persist c.bufr/c.bufw; split `req ↦ rrReqVal ...` (iStructNamed), persist Method and
  --    RemoteAddr (`reqHead`), the rest `reqRest`; expectsContinue false and `Header.get("Expect")`
  --    "" (empty map); `c.curReq.Store(w)` through the invariant (respNotify w from respNew);
  --    bodyRemains(nil) false; startBackgroundRead; `hjPre` from respNew + fields; `hijackOk` by
  --    wp_Hijack; the handler (`srvHandler`) returns threadTok and `hjDone`; `w.cancelCtx()`;
  --    hijacked() true; releaseConn (crLeft); return: defers: cancel, recover nil, hijacked true.
PLAN-/

end proof

end net.http
end Perennial
