/-
The net/http model's linked results (2026-11-23): `http.ReadResponse` on net/rpc's `CONNECT`
answer (`Net/Spec/net/http/ReadResponse.lean`), each proof applied to its callees' linked proofs:
the model's head parser (`modelReadLine`, `modelReadMIMEHeader`), `modelCutByte`,
`modelTrimLeftByte`, `ParseHTTPVersion`, `badStringError` (over Perennial's `fmt.Errorf`),
`readTransfer` and its helpers (`shouldClose`, `parseTransferEncoding`, `fixLength`, `fixTrailer`,
`Header.Del`, textproto's `MIMEHeader.Del` and `CanonicalMIMEHeaderKey`, httpguts'
`HeaderValuesContainsToken`), `fixPragmaCacheControl`, Perennial's `strconv.Atoi`, and bufio's
`ReadByte` (`specNE`), `Peek` and `fill` (the main tree's `Proof/bufio/`).
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

end net.http
end Perennial

#print axioms Perennial.net.http.ReadResponse.wp
