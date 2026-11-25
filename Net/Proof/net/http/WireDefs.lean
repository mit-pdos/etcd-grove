/-
The pure vocabulary of HTTP/1.1 requests and responses as the net/http model's server and
`ReadResponse` read and write them (httpdriver, 2026-11-25): `HReq`, `reqWire`, `reqOk`, `ReqSlot`,
`junkOk`; `Resp`, `respWire`, `respOk`, `badResp`, `dropConn`; `srvKeys`, `hdrView`, `hdrsOk`;
`pathUnder`, `pathClean`, `notFoundBody`. Each is described in `ProtoDefs.lean`'s header, which uses
them (split out so that `ReadResponse`'s spec imports no server vocabulary).
-/
module

public import Net.Proof.net.http.RequestDefs
public import Net.Proof.net.http.Defs
public import Perennial.Proof.fmt.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace net.http

/-! ## Requests -/

/-- See the file header. -/
structure HReq where
  meth : GoString
  host : GoString
  path : GoString
  hdr : List HdrLine

instance HReq.countable : Pos.Countable HReq :=
  .ofInjective (fun R => Pos.Countable.encode (R.meth, R.host, R.path, R.hdr))
    (fun ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩ h => by
      have h' := Pos.encode_inj h
      simp only [Prod.mk.injEq] at h'
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h'
      rfl)

/-- The value of the line named `k` of `hb` (the first), or `""` (`Header.Get` of a canonical key
on the map of `hb`). -/
def hdrGetL (hb : List HdrLine) (k : GoString) : GoString :=
  ((hb.find? (fun kv => decide (kv.1 = k))).map Prod.snd).getD []

/-- `hb` with the line `k: v` in place of the ones named `k` (`Header.Set` of a canonical key). -/
def hdrSetL (hb : List HdrLine) (k v : GoString) : List HdrLine :=
  hb.filter (fun kv => decide (kv.1 ≠ k)) ++ [(k, v)]

/-- See the file header. -/
def methOk (m : GoString) : Prop :=
  m ≠ [] ∧ m.all fieldByte = true ∧ m ≠ go!"CONNECT" ∧ m ≠ go!"HEAD" ∧ m ≠ go!"PRI"

/-- See the file header. -/
def reqKeysOut : List GoString :=
  [go!"Host", go!"Transfer-Encoding", go!"Expect", go!"Connection", go!"Trailer", go!"Upgrade",
    go!"Te", go!"Pragma"]

/-- A byte of a `Host` value the server accepts (a subset of httpguts' `validHostByte`: letters,
digits, `-`, `.`, `:`). -/
def hostByte (c : w8) : Bool :=
  decide ((97 ≤ c.toNat ∧ c.toNat ≤ 122) ∨ (65 ≤ c.toNat ∧ c.toNat ≤ 90) ∨
    (48 ≤ c.toNat ∧ c.toNat ≤ 57) ∨ c ∈ [W8 45, W8 46, W8 58])

/-- See the file header. -/
def reqWire (R : HReq) (B : List w8) : List w8 :=
  R.meth ++ [W8 32] ++ R.path ++ go!" HTTP/1.1" ++ [W8 13, W8 10] ++
    hdrWire ((go!"Host", R.host) :: R.hdr) [W8 13] ++ B

/-- See the file header. -/
def reqOk (R : HReq) (B : List w8) : Prop :=
  methOk R.meth ∧ reqPath R.path ∧ R.host.all hostByte = true ∧
  hdrBlockOk ((go!"Host", R.host) :: R.hdr) ∧
  (∀ kv ∈ R.hdr, kv.1 ∉ reqKeysOut) ∧
  (hdrGetL R.hdr go!"Content-Length" = fmt.decimalNat B.length ∨
    (go!"Content-Length" ∉ R.hdr.map Prod.fst ∧ B = [])) ∧
  R.hdr.length + 1 ≤ 500 ∧ (reqWire R []).length ≤ 2 ^ 20 ∧ B.length < 2 ^ 60

/-- See the file header: a request `(R, τ, B)` or junk. -/
abbrev ReqSlot := (HReq × GName × List w8) ⊕ List w8

/-- See the file header. -/
def junkOk (j : List w8) : Prop :=
  ∃ l rest : List w8, j = l ++ [W8 10] ++ rest ∧ W8 10 ∉ l ∧ l.length ≤ 2 ^ 20 ∧
    l.head? ≠ none ∧ l.head? ≠ some (W8 13) ∧
    ¬ (go!"HTTP/" <+: (parseReqLine (dropCR l)).2.2.1)

/-- A slot's wire. -/
def slotWire : ReqSlot → List w8
  | .inl (R, _, B) => reqWire R B
  | .inr j => j

/-- A slot is well-formed. -/
def slotOk : ReqSlot → Prop
  | .inl (R, _, B) => reqOk R B
  | .inr j => junkOk j

/-- Every slot well-formed, junk only as the last. -/
def slotsOk (L : List ReqSlot) : Prop :=
  (∀ s ∈ L, slotOk s) ∧ ∀ (i : Nat) (j : List w8), L[i]? = some (.inr j) → i + 1 = L.length

/-- See the file header. -/
def slotsWire (L : List ReqSlot) : List w8 := (L.map slotWire).flatten

/-! ## Responses -/

/-- See the file header. -/
structure Resp where
  st : w64
  reason : List w8
  hc : List HdrLine
  body : List w8
  close : Bool

/-- A status whose response has a body (net/http's `bodyAllowedForStatus`, for statuses from `200`). -/
def bodyAllowed (st : w64) : Bool := decide (st ≠ W64 204 ∧ st ≠ W64 304)

/-- See the file header. -/
def respHeadWire (st : w64) (reason : List w8) (hc : List HdrLine) : List w8 :=
  go!"HTTP/1.1 " ++ fmt.decimalNat (uint.nat st) ++ [W8 32] ++ reason ++ [W8 13, W8 10] ++
    hdrWire hc [W8 13]

/-- See the file header. -/
def respWire (ρ : Resp) : List w8 := respHeadWire ρ.st ρ.reason ρ.hc ++ ρ.body

/-- See the file header. -/
def respOk (ρ : Resp) : Prop :=
  200 ≤ uint.nat ρ.st ∧ uint.nat ρ.st ≤ 999 ∧ ρ.reason.all valByte = true ∧ hdrBlockOk ρ.hc ∧
  (∀ k ∈ [go!"Transfer-Encoding", go!"Trailer", go!"Pragma"], k ∉ ρ.hc.map Prod.fst) ∧
  (∀ kv ∈ ρ.hc, kv.1 = go!"Connection" → kv.2 = go!"close") ∧ ρ.body.length < 2 ^ 60 ∧
  (if ρ.close then go!"Content-Length" ∉ ρ.hc.map Prod.fst ∧ bodyAllowed ρ.st = true
   else if bodyAllowed ρ.st then hdrGetL ρ.hc go!"Content-Length" = fmt.decimalNat ρ.body.length
   else go!"Content-Length" ∉ ρ.hc.map Prod.fst ∧ ρ.body = [])

/-- The header lines of a response as `ReadResponse` leaves them in its map: without a
`Connection: close` line (`shouldClose` deletes it). -/
def dropConn (hc : List HdrLine) : List HdrLine := hc.filter (fun kv => decide (kv.1 ≠ go!"Connection"))

/-- net/http's `400` answer to a request it could not read (`net.rpc.badReqAns`). -/
def badResp : Resp :=
  ⟨W64 400, go!"Bad Request", badHdr, go!"400 Bad Request", true⟩

/-- See the file header (`SpecPlan`'s). -/
def srvKeys : List GoString :=
  [go!"Date", go!"Content-Type", go!"Content-Length", go!"Transfer-Encoding", go!"Connection"]

/-- See the file header. -/
def hdrView (hs hc : List HdrLine) : Prop :=
  ∀ k, k ∉ srvKeys → hdrGetL hc k = hdrGetL hs k

/-- The keys a handler may not commit (they change the response's framing). -/
def respKeysOut : List GoString :=
  [go!"Content-Length", go!"Transfer-Encoding", go!"Connection", go!"Trailer", go!"Pragma"]

/-- See the file header. The size bound is the handler's obligation (it commits these lines through
`respOps`): a header block of at most `2 ^ 21` bytes, which the mux's own answers meet (a `307`'s
`Location` holds a path of at most `2 ^ 20` bytes, `reqOk`); `respFacts` bounds the written head by it
(interim, 2026-11-25, httpdriver's proof: the client's stream must be bounded for `bufio.NewReader`). -/
def hdrsOk (hs : List HdrLine) : Prop :=
  hdrBlockOk hs ∧ (∀ kv ∈ hs, kv.1 ∉ respKeysOut) ∧ (hs.flatMap hdrLineWire).length ≤ 2 ^ 21

/-- `p` is a path under the mux pattern `pfx` (`SpecPlan`'s): `pfx` itself, or, for a pattern
ending in `/`, below it. -/
def pathUnder (pfx p : GoString) : Prop :=
  p = pfx ∨ (pfx.getLast? = some (W8 47) ∧ pfx <+: p)

/-- `cleanPath(p) = p` for a `/`-initial `p`: every `/`-separated segment after the first `/` is
neither `.` nor `..`, and none but the last is empty. -/
def pathClean (p : GoString) : Prop :=
  let segs := (p.drop 1).splitOn (W8 47)
  ∀ (i : Nat) (s : List w8), segs[i]? = some s →
    s ≠ go!"." ∧ s ≠ go!".." ∧ (i + 1 < segs.length → s ≠ [])

/-- The body of `NotFound`'s answer (`Error(w, "404 page not found", 404)`, `fmt.Fprintln`). -/
def notFoundBody : List w8 := go!"404 page not found" ++ [W8 10]

end net.http
end Perennial
