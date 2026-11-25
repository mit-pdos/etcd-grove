/- Lean-first (no Rocq counterpart).

# `net/httpdriver`: the proof's shared definitions

The driver's requests (`DReq`: what `randomRequest` returns, `qOf`, its wire and its slot), its protocol
`drvP` (`net.http.HProto`: what the client's requests are, `hreq`, with their bodies saved at the
request's ghost name, `dghostVar τ □ B`; what an answer may be, `resp`: a body of at most `32` bytes;
what a complete answer says, `respEnd`, by path: `/echo`'s `200` echoes the request, `/status`
answers `418` with `"short and stout"`, any other path `404`), what the client's checks take of an
answer (`chkPre`), the driver's variables (`drvFacts`), the address's protocols (`drvAddr`) and the
client's knowledge of the answer at index `i` of a connection (`drvQ`).
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.Base
public import Net.Proof.net.http.ProtoDefs
public import Perennial.Ghost.DGhostVar

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net
open net.http (HReq HProto Resp RespSlot ReqSlot HdrLine HttpProtoGS)

namespace github_com.mit_pdos.etcd_grove.examples.net.httpdriver

/-! ## The driver's requests (pure) -/

/-- A word of `randomWord`: at most `maxLen = 32` lowercase letters. -/
def isWord (s : List w8) : Prop := s.length ≤ 32 ∧ ∀ c ∈ s, 97 ≤ c.toNat ∧ c.toNat ≤ 122

/-- The `Host` the client sends. -/
def driverHost : GoString := go!"driver"

/-- The server's address (`Addr`). -/
def addrS : GoString := go!"127.0.0.1:7401"

/-- What `randomRequest` returns: an `/echo` request (method, `X-Driver` value, body), `GET /status`,
`GET /nope/<w>`, or the junk line. -/
inductive DReq where
  | echo (m v b : GoString)
  | status
  | nope (w : GoString)
  | junk

/-- Its words are words, `/echo`'s method `POST` or `PUT`. -/
def DReq.ok : DReq → Prop
  | .echo m v b => (m = go!"POST" ∨ m = go!"PUT") ∧ isWord v ∧ isWord b
  | .status => True
  | .nope w => isWord w
  | .junk => True

/-- The request (`HReq`) of a request that is not junk. -/
def DReq.hreq : DReq → HReq
  | .echo m v b => ⟨m, driverHost, go!"/echo",
      [(go!"X-Driver", v), (go!"Content-Length", fmt.decimalNat b.length)]⟩
  | .status => ⟨go!"GET", driverHost, go!"/status", []⟩
  | .nope w => ⟨go!"GET", driverHost, go!"/nope/" ++ w, []⟩
  | .junk => ⟨[], [], [], []⟩

/-- Its body. -/
def DReq.body : DReq → List w8
  | .echo _ _ b => b
  | _ => []

/-- Its `kind` field. -/
def DReq.kind : DReq → GoString
  | .echo .. => go!"echo"
  | .status => go!"status"
  | .nope _ => go!"notfound"
  | .junk => go!"bad"

/-- The junk request's bytes. -/
def junkWire : List w8 := go!"NOT A REQUEST\r\n\r\n"

/-- Its bytes on the connection (`raw`). -/
def DReq.wire : DReq → List w8
  | .junk => junkWire
  | d => net.http.reqWire d.hreq d.body

/-- Its slot on the connection, `τ` its ghost name. -/
def DReq.slot (d : DReq) (τ : GName) : ReqSlot :=
  match d with
  | .junk => .inr junkWire
  | _ => .inl (d.hreq, τ, d.body)

section qof
variable [GooseExts]

/-- The struct `q` is the request `d`. -/
def qOf (q : request) (d : DReq) : Prop :=
  q.raw' = d.wire ∧ q.kind' = d.kind ∧
  match d with
  | .echo m v b => q.meth' = m ∧ q.value' = v ∧ q.body' = b
  | _ => True

end qof

/-- The requests the client sends, with their bodies (not junk). -/
def drvReq (R : HReq) (B : List w8) : Prop :=
  ∃ d : DReq, d.ok ∧ d ≠ .junk ∧ R = d.hreq ∧ B = d.body

/-- What a complete answer to `R` (body `B`) with status `st`, the handler's lines `hs` and body `bs`
says, by `R`'s path. -/
def drvRespEnd (R : HReq) (B : List w8) (st : w64) (hs : List HdrLine) (bs : List w8) : Prop :=
  (R.path = go!"/echo" → st = W64 200 →
    net.http.hdrGetL hs go!"X-Method" = R.meth ∧ net.http.hdrGetL hs go!"X-Path" = go!"/echo" ∧
    net.http.hdrGetL hs go!"X-Echo" = net.http.hdrGetL R.hdr go!"X-Driver" ∧ bs = B) ∧
  (R.path = go!"/status" → st = W64 418 ∧ bs = go!"short and stout") ∧
  (R.path ≠ go!"/echo" → R.path ≠ go!"/status" → st = W64 404)

/-- What `check` takes of an answer with status `st`, written lines `hc` and body `body` to the request
`d`: the server's `400`, or not junk and a complete answer of its handler (`hdrView`). -/
def chkPre (d : DReq) (st : w64) (hc : List HdrLine) (body : List w8) : Prop :=
  st = W64 400 ∨
    (d ≠ .junk ∧ ∃ hs, net.http.hdrView hs hc ∧ drvRespEnd d.hreq d.body st hs body)

/-! ## The protocol -/

section proto
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

/-- The driver's protocol (see the file header). -/
def drvP : HProto GF where
  hreq R τ := iprop(∃ B : List w8, ⌜drvReq R B⌝ ∗ dghostVar τ DFrac.discard B)
  bodyPre _ _ _ := iprop(True)
  body _ τ B := dghostVar τ DFrac.discard B
  resp _ _ _ _ w := iprop(⌜w.length ≤ 32⌝)
  respEnd R τ st hs bs := iprop(∃ B : List w8, dghostVar τ DFrac.discard B ∗ ⌜drvRespEnd R B st hs bs⌝)

end proto

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]

/-- The driver's variable: `reached`, a function that returns. -/
def drvFacts : IProp GF :=
  iprop(∃ f : GoFunc, globalAddr reached ↦□ f ∗
      □ ∀ s : GoString, WP (App (Val #f) (Val #s)) {{ v, ⌜v = #()⌝ }})

instance drvFacts_persistent : Persistent (drvFacts (GF := GF)) := by
  unfold drvFacts; infer_instance

variable [π : NetProtoGS] [hπ : HttpProtoGS]

/-- The server's address serves `drvP` (persistent): its protocols and the connection registry. -/
def drvAddr : IProp GF :=
  iprop(addrProto (Gg := hG.goose_globalGS) addrS (net.http.httpReqP (Gg := hG.goose_globalGS) drvP)
      (net.http.httpRespP (Gg := hG.goose_globalGS) drvP) ∗
    inv net.http.httpRegN (net.http.httpRegInv (Gg := hG.goose_globalGS)))

instance drvAddr_persistent : Persistent (drvAddr (GF := GF)) := by
  unfold drvAddr; infer_instance

/-- What the client knows of the answer `ρ` at index `i` of a connection whose slots are (at least)
`L`: the server's `400`, or a complete answer of the handler of the request at `i`. -/
def drvQ (L : List ReqSlot) (i : Nat) (ρ : Resp) : IProp GF :=
  iprop(⌜ρ = net.http.badResp⌝ ∨
    ∃ (R : HReq) (τ : GName) (B : List w8) (hs : List HdrLine),
      ⌜L[i]? = some (.inl (R, τ, B)) ∧ net.http.respOk ρ ∧ ρ.close = false ∧
        net.http.hdrView hs ρ.hc⌝ ∗
      □ drvP.respEnd R τ ρ.st hs ρ.body)

instance drvQ_persistent (L : List ReqSlot) (i : Nat) (ρ : Resp) :
    Persistent (drvQ (GF := GF) L i ρ) := by
  unfold drvQ; simp only [drvP]; infer_instance

end defs

end github_com.mit_pdos.etcd_grove.examples.net.httpdriver
end Perennial
