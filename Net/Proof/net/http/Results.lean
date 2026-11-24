/-
The net/http model's linked results (2026-11-23): `http.ReadResponse` on net/rpc's `CONNECT`
answer (`Net/Spec/net/http/ReadResponse.lean`), each proof applied to its callees' linked proofs:
the model's head parser (`modelReadLine`, `modelReadMIMEHeader`), Perennial's `strings.Cut` and
`strings.TrimLeft` (`section links_strings`, below), `ParseHTTPVersion`, `badStringError` (over Perennial's `fmt.Errorf`),
`readTransfer` and its helpers (`shouldClose`, `parseTransferEncoding`, `fixLength`, `fixTrailer`,
`Header.Del`, textproto's `MIMEHeader.Del` and `CanonicalMIMEHeaderKey`, the model's
`modelHeaderValuesContainsToken` and its helpers), `fixPragmaCacheControl`, Perennial's `strconv.Atoi`
and `strings.HasPrefix`, and bufio's `ReadByte` (`specNE`), `Peek` and `fill` (the main tree's
`Proof/bufio/`); since 2026-11-23 also on net/http's `400` answer (its two header lines: the model's
`modelReadMIMEHeader` over httpguts' `ValidHeaderFieldName`/`ValidHeaderFieldValue` and `fmt.Sprintf`).

The server's hijack (2026-11-23): `response.Hijack` (`hijackOk` from `hjPre`, what `conn.serve` has
when it calls the handler) over `conn.hijackLocked`, `connReader.abortPendingRead`, the net
extension's `Conn.SetDeadline`/`SetReadDeadline` and bufio's `Writer.Reset`; and the background
read, `connReader.backgroundRead`, over `Conn.Read` and `OpError.Timeout`, and its start,
`connReader.startBackgroundRead` (over `Conn.SetReadDeadline`); `connReader.releaseConn`; and the
head's read, `connReader.Read` in the head phase (`crHead`, over `Conn.Read`).

The request's URI (2026-11-23): the model's `modelParseRequestURI` (`url.ParseRequestURI`) on a
`reqPath`, over `modelPathBytes` and `modelPathByte`; the request line's `parseRequestLine` (over
Perennial's `strings.Cut`) and `validMethod` (over `isToken` and httpguts' `ValidHeaderFieldName`, which reads
`isTokenTable`: `tokenTable`, a premise).

The request (2026-11-23): `readRequestLimit` on net/rpc's `CONNECT` request, and
`Server.maxHeaderValueCount`; and (2026-11-24, phase 7 S5) what `conn.readRequest` calls on it:
`http1ServerSupportsRequest`, `Request.ProtoAtLeast`, `Request.isH2Upgrade`, `Request.wantsClose` and
`Request.wantsHttp10KeepAlive` (over `Header.get` and `hasToken`, both on a header with no
`Connection` entry: `hasToken`'s loop calls `isTokenBoundary` and `ascii.EqualFold`, names only),
`conn.hijacked`, and the read limit's `connReader.setReadLimit`/`setInfiniteReadLimit`/`hitReadLimit`.

net/url's escaping (2026-11-24, phase 7 S5; what the ServeMux runs on a request's path): `shouldEscape`,
`ishex` (over net/url's fact `urlInit`: its table, proved by its initializer), `unhex`, `validEncoded`, `escape`,
`unescape`, `PathUnescape` and `URL.EscapedPath`; `unescape` over Perennial's `strings.Builder.Grow`,
`WriteByte` and `String`.

The chunked writer (2026-11-24, phase 7 S5): `net/http/internal`'s `NewChunkedWriter`,
`chunkedWriter.Write` (over Perennial's `fmt.Fprintf`) and `chunkedWriter.Close`; both methods call
`io.WriteString`, names only at the pin (`notes/perennial-changes.md`): linked over its spec
(`Spec/io/WriteString.lean`) as a hypothesis `h_WriteString` (`section chunked`).
No axiom, no `sorry`.
-/
module

public import Net.Proof.net.http.ReadResponse
public import Net.Proof.net.http.modelReadLine
public import Net.Proof.net.http.modelReadMIMEHeader
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
public import Net.Proof.net.http.modelHeaderValuesContainsToken
public import Net.Proof.net.http.modelHeaderValueContainsToken
public import Net.Proof.net.http.modelIndexByte
public import Net.Proof.net.http.modelTrimOWS
public import Net.Proof.net.http.modelTokenEqual
public import Net.Proof.net.http.modelLowerASCII
public import Net.Proof.net.http.readRequestLimit
public import Net.Proof.net.http.Server__maxHeaderValueCount
public import Net.Proof.vendor.golang_org.x.net.http.httpguts.ValidHeaderFieldValue
public import Perennial.Proof.strings.Link
public import Proof.bufio.Reader__fill
public import Proof.bufio.Reader__Peek
public import Proof.bufio.Reader__ReadByteNE
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.fmt.BytesResults
public import Perennial.Proof.strconv.Link
public import Net.Proof.net.http.response__Hijack
public import Net.Proof.net.http.conn__hijackLocked
public import Net.Proof.net.http.connReader__abortPendingRead
public import Net.Proof.net.http.connReader__backgroundRead
public import Net.Proof.net.http.connReader__startBackgroundRead
public import Net.Proof.net.http.connReader__releaseConn
public import Net.Proof.net.http.connReader__Read
public import Net.Proof.net.http.ConnReaderStream
public import Net.Proof.net.Conn__Read
public import Net.Proof.net.Conn__SetDeadline
public import Net.Proof.net.Conn__SetReadDeadline
public import Net.Proof.net.OpError__Timeout
public import Proof.bufio.Writer__Reset
public import Net.Proof.net.http.modelParseRequestURI
public import Net.Proof.net.http.modelPathBytes
public import Net.Proof.net.http.modelPathByte
public import Net.Proof.net.http.parseRequestLine
public import Net.Proof.net.http.validMethod
public import Net.Proof.net.http.internal.NewChunkedWriter
public import Proof.net.url.shouldEscape
public import Proof.net.url.ishex
public import Proof.net.url.unhex
public import Proof.net.url.validEncoded
public import Proof.net.url.escape
public import Proof.net.url.unescape
public import Proof.net.url.PathUnescape
public import Proof.net.url.URL__EscapedPath
public import Net.Proof.net.http.internal.chunkedWriter__Write
public import Net.Proof.net.http.internal.chunkedWriter__Close
public import Net.Proof.net.http.isToken
public import Net.Proof.vendor.golang_org.x.net.http.httpguts.ValidHeaderFieldName
public import Net.Proof.net.http.Header__get
public import Net.Proof.net.http.hasToken
public import Net.Proof.net.http.Request__isH2Upgrade
public import Net.Proof.net.http.Request__wantsClose
public import Net.Proof.net.http.Request__wantsHttp10KeepAlive
public import Net.Proof.net.http.conn__hijacked
public import Net.Proof.net.http.connReader__setReadLimit
public import Net.Proof.net.http.connReader__setInfiniteReadLimit
public import Net.Proof.net.http.connReader__hitReadLimit
public import Net.Proof.net.http.Request__ProtoAtLeast
public import Net.Proof.net.http.http1ServerSupportsRequest

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
    modelReadLine.wp net.textproto.CanonicalMIMEHeaderKey.wp_proof
    vendor.golang_org.x.net.http.httpguts.ValidHeaderFieldName.wp_proof
    vendor.golang_org.x.net.http.httpguts.ValidHeaderFieldValue.wp_proof fmt.wp_Sprintf

theorem Header.Del.wp : Header.Del.spec (GF := GF) (hG := hG) :=
  Header.Del.wp_proof
    (net.textproto.MIMEHeader.Del.wp_proof net.textproto.CanonicalMIMEHeaderKey.wp_proof)

theorem modelHeaderValuesContainsToken.wp : modelHeaderValuesContainsToken.spec (GF := GF) (hG := hG) :=
  modelHeaderValuesContainsToken.wp_proof
    (modelHeaderValueContainsToken.wp_proof modelIndexByte.wp_proof modelTrimOWS.wp_proof
      (modelTokenEqual.wp_proof modelLowerASCII.wp_proof))

theorem shouldClose.wp : shouldClose.spec (GF := GF) (hG := hG) :=
  shouldClose.wp_proof modelHeaderValuesContainsToken.wp Header.Del.wp

theorem readTransfer.wp : readTransfer.spec (GF := GF) (hG := hG) :=
  readTransfer.wp_proof shouldClose.wp
    transferReader.parseTransferEncoding.wp_proof (fixLength.wp_proof Header.Del.wp)
    fixTrailer.wp_proof

theorem ParseHTTPVersion.wp : ParseHTTPVersion.spec (GF := GF) (hG := hG) :=
  ParseHTTPVersion.wp_proof strings.wp_HasPrefix

theorem modelParseRequestURI.wp : modelParseRequestURI.spec (GF := GF) (hG := hG) :=
  modelParseRequestURI.wp_proof (modelPathBytes.wp_proof modelPathByte.wp_proof)

theorem validMethod.wp : validMethod.spec (GF := GF) (hG := hG) :=
  validMethod.wp_proof
    (isToken.wp_proof vendor.golang_org.x.net.http.httpguts.ValidHeaderFieldName.wp_proof)

theorem Server.maxHeaderValueCount.wp : Server.maxHeaderValueCount.spec (GF := GF) (hG := hG) :=
  Server.maxHeaderValueCount.wp_proof

theorem Request.ProtoAtLeast.wp : Request.ProtoAtLeast.spec (GF := GF) (hG := hG) :=
  Request.ProtoAtLeast.wp_proof
theorem http1ServerSupportsRequest.wp : http1ServerSupportsRequest.spec (GF := GF) (hG := hG) :=
  http1ServerSupportsRequest.wp_proof
theorem Request.isH2Upgrade.wp : Request.isH2Upgrade.spec (GF := GF) (hG := hG) :=
  Request.isH2Upgrade.wp_proof
theorem Header.get.wp : Header.get.spec (GF := GF) (hG := hG) := Header.get.wp_proof
theorem hasToken.wp : hasToken.spec (GF := GF) (hG := hG) := hasToken.wp_proof
theorem Request.wantsHttp10KeepAlive.wp : Request.wantsHttp10KeepAlive.spec (GF := GF) (hG := hG) :=
  Request.wantsHttp10KeepAlive.wp_proof Header.get.wp hasToken.wp
theorem Request.wantsClose.wp : Request.wantsClose.spec (GF := GF) (hG := hG) :=
  Request.wantsClose.wp_proof Header.get.wp hasToken.wp
theorem connReader.setReadLimit.wp : connReader.setReadLimit.spec (GF := GF) (hG := hG) :=
  connReader.setReadLimit.wp_proof
theorem connReader.setInfiniteReadLimit.wp :
    connReader.setInfiniteReadLimit.spec (GF := GF) (hG := hG) :=
  connReader.setInfiniteReadLimit.wp_proof
theorem connReader.hitReadLimit.wp : connReader.hitReadLimit.spec (GF := GF) (hG := hG) :=
  connReader.hitReadLimit.wp_proof

end link

section links_strings
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.http.Assumptions]
theorem ReadResponse.wp : ReadResponse.spec (GF := GF) (hG := hG) :=
  ReadResponse.wp_proof modelReadLine.wp modelReadMIMEHeader.wp strings.wp_Cut
    strings.wp_TrimLeft ParseHTTPVersion.wp (badStringError.wp_proof fmt.wp_Errorf)
    fixPragmaCacheControl.wp_proof readTransfer.wp strconv.wp_Atoi

theorem parseRequestLine.wp : parseRequestLine.spec (GF := GF) (hG := hG) :=
  parseRequestLine.wp_proof strings.wp_Cut

theorem readRequestLimit.wp : readRequestLimit.spec (GF := GF) (hG := hG) :=
  readRequestLimit.wp_proof modelReadLine.wp modelReadMIMEHeader.wp parseRequestLine.wp
    validMethod.wp ParseHTTPVersion.wp (badStringError.wp_proof fmt.wp_Errorf)
    modelParseRequestURI.wp fixPragmaCacheControl.wp_proof shouldClose.wp readTransfer.wp
    strings.wp_HasPrefix

end links_strings

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

theorem connReader.Read.wp : connReader.Read.spec (GF := GF) (hG := hG) :=
  connReader.Read.wp_proof net.Conn.Read.wp_proof

theorem connReader.releaseConn.wp : connReader.releaseConn.spec (GF := GF) (hG := hG) :=
  connReader.releaseConn.wp_proof

theorem connReader.abortPendingRead.wp :
    connReader.abortPendingRead.spec (GF := GF) (hG := hG) :=
  connReader.abortPendingRead.wp_proof net.Conn.SetReadDeadline.wp_proof

theorem conn.hijackLocked.wp : conn.hijackLocked.spec (GF := GF) (hG := hG) :=
  conn.hijackLocked.wp_proof connReader.abortPendingRead.wp net.Conn.SetDeadline.wp_proof
    EtcdGrove.bufio.Writer.Reset.wp_proof

theorem conn.hijacked.wp : conn.hijacked.spec (GF := GF) (hG := hG) := conn.hijacked.wp_proof

theorem response.Hijack.wp : response.Hijack.spec (GF := GF) (hG := hG) :=
  response.Hijack.wp_proof conn.hijackLocked.wp EtcdGrove.bufio.Writer.Reset.wp_proof

end server

end net.http

namespace net.http.internal

section chunked
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.http.internal.Assumptions]

theorem NewChunkedWriter.wp : NewChunkedWriter.spec (GF := GF) (hG := hG) :=
  NewChunkedWriter.wp_proof

-- Pending: Perennial's `io.WriteString` (see the file header).
variable (h_WriteString : EtcdGrove.io.WriteString.spec (GF := GF) (hG := hG))

include h_WriteString in
theorem chunkedWriter.Write.wp : chunkedWriter.Write.spec (GF := GF) (hG := hG) :=
  chunkedWriter.Write.wp_proof fmt.wp_Fprintf h_WriteString

include h_WriteString in
theorem chunkedWriter.Close.wp : chunkedWriter.Close.spec (GF := GF) (hG := hG) :=
  chunkedWriter.Close.wp_proof h_WriteString

end chunked

end net.http.internal

namespace net.url

/-! ### net/url's escaping, for the ServeMux (phase 7 S5, 2026-11-24) -/

section url
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.url.Assumptions]

theorem shouldEscape.wp : shouldEscape.spec (GF := GF) (hG := hG) := shouldEscape.wp_proof
theorem ishex.wp : ishex.spec (GF := GF) (hG := hG) := ishex.wp_proof
theorem unhex.wp : unhex.spec (GF := GF) (hG := hG) := unhex.wp_proof
theorem validEncoded.wp : validEncoded.spec (GF := GF) (hG := hG) :=
  validEncoded.wp_proof shouldEscape.wp
theorem escape.wp : escape.spec (GF := GF) (hG := hG) := escape.wp_proof shouldEscape.wp

variable [package_sem_strings : _root_.Perennial.strings.Assumptions]

theorem unescape.wp : unescape.spec (GF := GF) (hG := hG) :=
  unescape.wp_proof ishex.wp unhex.wp shouldEscape.wp strings.Builder.wp_Grow strings.Builder.wp_WriteByte
    strings.Builder.wp_String

theorem PathUnescape.wp : PathUnescape.spec (GF := GF) (hG := hG) :=
  PathUnescape.wp_proof unescape.wp

theorem URL.EscapedPath.wp : URL.EscapedPath.spec (GF := GF) (hG := hG) :=
  URL.EscapedPath.wp_proof unescape.wp escape.wp validEncoded.wp

end url

end net.url
end Perennial

#print axioms Perennial.net.http.internal.NewChunkedWriter.wp
#print axioms Perennial.net.http.internal.chunkedWriter.Write.wp
#print axioms Perennial.net.http.internal.chunkedWriter.Close.wp
#print axioms Perennial.net.http.ReadResponse.wp
#print axioms Perennial.net.http.modelReadMIMEHeader.wp
#print axioms Perennial.net.http.connReader.backgroundRead.wp
#print axioms Perennial.net.http.response.Hijack.wp
#print axioms Perennial.net.http.connReader.startBackgroundRead.wp
#print axioms Perennial.net.http.connReader.releaseConn.wp
#print axioms Perennial.net.http.connReader.Read.wp
#print axioms Perennial.net.http.modelParseRequestURI.wp
#print axioms Perennial.net.http.parseRequestLine.wp
#print axioms Perennial.net.http.validMethod.wp
#print axioms Perennial.net.http.readRequestLimit.wp
#print axioms Perennial.net.http.Server.maxHeaderValueCount.wp
#print axioms Perennial.net.http.Request.ProtoAtLeast.wp
#print axioms Perennial.net.http.http1ServerSupportsRequest.wp
#print axioms Perennial.net.http.Request.isH2Upgrade.wp
#print axioms Perennial.net.http.Header.get.wp
#print axioms Perennial.net.http.hasToken.wp
#print axioms Perennial.net.http.Request.wantsHttp10KeepAlive.wp
#print axioms Perennial.net.http.Request.wantsClose.wp
#print axioms Perennial.net.http.connReader.setReadLimit.wp
#print axioms Perennial.net.http.connReader.setInfiniteReadLimit.wp
#print axioms Perennial.net.http.connReader.hitReadLimit.wp
#print axioms Perennial.net.http.conn.hijacked.wp
#print axioms Perennial.net.url.shouldEscape.wp
#print axioms Perennial.net.url.ishex.wp
#print axioms Perennial.net.url.unhex.wp
#print axioms Perennial.net.url.validEncoded.wp
#print axioms Perennial.net.url.escape.wp
#print axioms Perennial.net.url.unescape.wp
#print axioms Perennial.net.url.PathUnescape.wp
#print axioms Perennial.net.url.URL.EscapedPath.wp
