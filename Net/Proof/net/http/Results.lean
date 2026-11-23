/-
The net/http model's linked results (2026-11-23): `http.ReadResponse` on net/rpc's `CONNECT`
answer (`Net/Spec/net/http/ReadResponse.lean`), each proof applied to its callees' linked proofs:
the model's head parser (`modelReadLine`, `modelReadMIMEHeader`), `modelCutByte`,
`modelTrimLeftByte`, `ParseHTTPVersion`, `badStringError` (over Perennial's `fmt.Errorf`),
`readTransfer` and its helpers (`shouldClose`, `parseTransferEncoding`, `fixLength`, `fixTrailer`,
`Header.Del`, textproto's `MIMEHeader.Del` and `CanonicalMIMEHeaderKey`, httpguts'
`HeaderValuesContainsToken`), `fixPragmaCacheControl`, Perennial's `strconv.Atoi`, and bufio's
`ReadByte` (`specNE`), `Peek` and `fill` (the main tree's `Proof/bufio/`).

The server's hijack (2026-11-23): `response.Hijack` (`hijackOk` from `hjPre`, what `conn.serve` has
when it calls the handler) over `conn.hijackLocked`, `connReader.abortPendingRead`, the net
extension's `Conn.SetDeadline`/`SetReadDeadline` and bufio's `Writer.Reset`; and the background
read, `connReader.backgroundRead`, over `Conn.Read` and `OpError.Timeout`, and its start,
`connReader.startBackgroundRead` (over `Conn.SetReadDeadline`); `connReader.releaseConn`.
-/
module

public import Net.Proof.net.http.ReadResponse
public import Net.Proof.net.http.modelReadLine
public import Net.Proof.net.http.modelReadMIMEHeader
public import Net.Proof.net.http.modelCutByte
public import Net.Proof.net.http.modelTrimLeftByte
public import Net.Proof.net.http.ParseHTTPVersion
public import Net.Proof.net.http.badStringError
public import Net.Proof.net.http.fixPragmaCacheControl
public import Net.Proof.net.http.readTransfer
public import Net.Proof.net.http.shouldClose
public import Net.Proof.net.http.transferReader__parseTransferEncoding
public import Net.Proof.net.http.fixLength
public import Net.Proof.net.http.fixTrailer
public import Net.Proof.net.http.Header__Del
public import Net.Proof.net.textproto.MIMEHeader__Del
public import Net.Proof.net.textproto.CanonicalMIMEHeaderKey
public import Net.Proof.vendor.golang_org.x.net.http.httpguts.HeaderValuesContainsToken
public import Proof.bufio.Reader__fill
public import Proof.bufio.Reader__Peek
public import Proof.bufio.Reader__ReadByteNE
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.strconv.Link
public import Net.Proof.net.http.response__Hijack
public import Net.Proof.net.http.conn__hijackLocked
public import Net.Proof.net.http.connReader__abortPendingRead
public import Net.Proof.net.http.connReader__backgroundRead
public import Net.Proof.net.http.connReader__startBackgroundRead
public import Net.Proof.net.http.connReader__releaseConn
public import Net.Proof.net.Conn__Read
public import Net.Proof.net.Conn__SetDeadline
public import Net.Proof.net.Conn__SetReadDeadline
public import Net.Proof.net.OpError__Timeout
public import Proof.bufio.Writer__Reset

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace net.http

section link
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.http.Assumptions]

theorem modelReadLine.wp : modelReadLine.spec (GF := GF) (hG := hG) :=
  modelReadLine.wp_proof
    (EtcdGrove.bufio.Reader.ReadByte.wp_proofNE EtcdGrove.bufio.Reader.fill.wp_proof)

theorem modelReadMIMEHeader.wp : modelReadMIMEHeader.spec (GF := GF) (hG := hG) :=
  modelReadMIMEHeader.wp_proof (EtcdGrove.bufio.Reader.Peek.wp_proof EtcdGrove.bufio.Reader.fill.wp_proof)
    modelReadLine.wp

theorem Header.Del.wp : Header.Del.spec (GF := GF) (hG := hG) :=
  Header.Del.wp_proof
    (net.textproto.MIMEHeader.Del.wp_proof net.textproto.CanonicalMIMEHeaderKey.wp_proof)

theorem readTransfer.wp : readTransfer.spec (GF := GF) (hG := hG) :=
  readTransfer.wp_proof
    (shouldClose.wp_proof vendor.golang_org.x.net.http.httpguts.HeaderValuesContainsToken.wp_proof)
    transferReader.parseTransferEncoding.wp_proof (fixLength.wp_proof Header.Del.wp)
    fixTrailer.wp_proof

theorem ReadResponse.wp : ReadResponse.spec (GF := GF) (hG := hG) :=
  ReadResponse.wp_proof modelReadLine.wp modelReadMIMEHeader.wp modelCutByte.wp_proof
    modelTrimLeftByte.wp_proof ParseHTTPVersion.wp_proof (badStringError.wp_proof fmt.wp_Errorf)
    fixPragmaCacheControl.wp_proof readTransfer.wp strconv.wp_Atoi

end link

section server
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : net.http.Assumptions]
variable [HasExt Net.netExt] [π : Net.NetProtoGS] [net.Assumptions] [field_sem : net.FieldAssumptions]
variable [bufio_sem : bufio.Assumptions]

theorem connReader.backgroundRead.wp :
    connReader.backgroundRead.spec (GF := GF) (hG := hG) :=
  connReader.backgroundRead.wp_proof net.Conn.Read.wp_proof net.OpError.Timeout.wp_proof

theorem connReader.startBackgroundRead.wp :
    connReader.startBackgroundRead.spec (GF := GF) (hG := hG) :=
  connReader.startBackgroundRead.wp_proof net.Conn.SetReadDeadline.wp_proof connReader.backgroundRead.wp

theorem connReader.releaseConn.wp : connReader.releaseConn.spec (GF := GF) (hG := hG) :=
  connReader.releaseConn.wp_proof

theorem connReader.abortPendingRead.wp :
    connReader.abortPendingRead.spec (GF := GF) (hG := hG) :=
  connReader.abortPendingRead.wp_proof net.Conn.SetReadDeadline.wp_proof

theorem conn.hijackLocked.wp : conn.hijackLocked.spec (GF := GF) (hG := hG) :=
  conn.hijackLocked.wp_proof connReader.abortPendingRead.wp net.Conn.SetDeadline.wp_proof
    EtcdGrove.bufio.Writer.Reset.wp_proof

theorem response.Hijack.wp : response.Hijack.spec (GF := GF) (hG := hG) :=
  response.Hijack.wp_proof conn.hijackLocked.wp EtcdGrove.bufio.Writer.Reset.wp_proof

end server

end net.http
end Perennial

#print axioms Perennial.net.http.ReadResponse.wp
#print axioms Perennial.net.http.connReader.backgroundRead.wp
#print axioms Perennial.net.http.response.Hijack.wp
#print axioms Perennial.net.http.connReader.startBackgroundRead.wp
#print axioms Perennial.net.http.connReader.releaseConn.wp
