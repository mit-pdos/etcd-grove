/-
**The HTTP boundary of rafthttp** (D38 (A), stage 2; `notes/rafthttp-http-boundary.md`, reviewed by
the user 2026-10-22). Lean-first. Definitions and the statements of the boundary's specs
(`…_spec : Prop`); the proofs take them as hypotheses, and those they use are trust-boundary
axioms in `Proof/net/http/Axioms.lean` (stage 4e, 2026-10-23), with the registration of an
address's protocol (`http.register`).

The model (the note's points 1-6):
* An `HReq` is what a client sends: method, host (the address `http://host` names), path, headers
  (as set, in order) and body bytes.
* An `HttpNet` fixes, for the whole run, each address's protocol (`Proto`): a persistent predicate
  `req` on the requests sent to it and `resp` on a request, the status its handler set and the
  bytes the handler wrote. A program's peer addresses are its own (`netAddrFree`); every request a
  server of the program receives comes from a client of the program that went through
  `RoundTrip` (the closed-world statement, accepted 2026-10-22), so the handler gets `□ req R` of
  the request `R` it receives, and the client gets `□ resp R st w` of the response's status and of
  the bytes it reads (a prefix of `w`).
* Body streams are prefixes; a request body's reader returns `EOF` only at the end. Any operation
  may fail with an error.
* The response's status is the one the handler set (revised 2026-10-22: a `403`/`410` is
  `errMemberRemoved`, which matters in a dynamic cluster).
* (2026-10-23, stage 4e) **An address's protocol is registered once.** `HttpNet` names a protocol
  for every address, but a spec stated for any `H` would let a client and a server of one
  address use different ones. So the protocol a client sends with and the one a server serves
  with are tied to the address: `http.register` turns the address's listener (`netListenerAt l
  a`, one per address in a run: `net.Listen` consumes `netAddrFree a`) into `httpListenerAt l a P`,
  which `Serve` takes, and `httpProtoAt a P` (persistent), which `RoundTrip` needs of a request's
  host. Two `httpProtoAt a P` of one address are of the one registration: the facts' model is a
  global ghost map from addresses to saved protocols, an entry set once. (D39a, 2026-10-23,
  stage 6a) The entry is set before the listener exists: `http.reserve` turns the address's
  protocol right (`httpProtoFree a`, from program start) into `httpProtoAt a P` and the right to
  serve it (`httpProtoOwn a P`), which `register` takes with the listener; a member sends to its
  peers before they listen.
* (2026-10-23, D38b, the user's choice) **A request is handled at most once**: `RoundTrip` takes a
  fresh exclusive ghost ticket (`reqTicket γk`) and the handler of the request receives it; the
  protocols are indexed by the ticket's name. Go's client never replays a `POST`
  (`Request.isReplayable`), and its server runs one handler per request it reads. What a one-shot
  payload needs: the receiver withdraws a deposit with the ticket, so only once.
* (2026-10-24, D42, rafthttp stage 7b) **A request's body is fixed or streamed.** A fixed body's
  bytes are the request's (`HReq.body`, from `NewRequest`'s reader at its bytes). A streamed body
  is a reader whose bytes the client does not hold (rafthttp's snapshot: the envelope, then the
  merged snapshot's pipe), which Go sends chunked as `RoundTrip` reads it (`Body`). Each address's
  protocol says which requests are streamed (`Proto.streamed`), and states of a streamed request
  `sreq R γk Pre Φ`: its body's every prefix is in `Pre`, its every complete stream in `Φ`. The
  client sends a streamed request with a reader keeping that contract (`streamHas`); its handler
  reads the body with it (`bodyStream`): what it reads is in `Pre`, and in `Φ` once a read
  returns `EOF`. The physical assumption: a chunked body the server reads is a prefix of what the
  client's reader yielded, and ends with `EOF` only at the end of the reader's stream (a truncated
  one, as the client's reader failing or the connection dropping, ends with
  `io.ErrUnexpectedEOF`).
* A handler's contract is a WP whose postcondition also covers a panic (`Serve` recovers it), and
  each invocation borrows one of `httpProcSlots` resources (the concurrency bound, a physical fact:
  each handler is a goroutine with its own stack).

`http.Request` and `http.Response` are axiomatized types (Goose does not translate their
structs): the predicates speak of their fields' addresses.
-/
module

public import Proof.net.InvNet
public import GeneratedProof.net.http
public import GeneratedProof.net.url
public import Perennial.Code.io
public import Perennial.Code.bytes
public import Perennial.Code.encoding.binary
public import Perennial.Proof.ProofPrelude
public import Perennial.Ghost.DGhostVar
public import Proof.unicode.utf8.Valid
public import Perennial.Proof.errors.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace http

open Iris Iris.BI

/-- **A request as a client sends it** (see the file header). -/
structure HReq where
  meth : GoString
  host : GoString
  path : GoString
  hdr : List (GoString × GoString)
  body : List w8

section fields
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- The field `f` of the `*http.Request` at `r`. -/
abbrev reqF (f : GoString) (r : Loc) : Loc :=
  structFieldRef _root_.Perennial.net.http.Request f r

/-- The field `f` of the `*url.URL` at `u`. -/
abbrev urlF (f : GoString) (u : Loc) : Loc :=
  structFieldRef _root_.Perennial.net.url.URL f u

/-- The field `f` of the `*http.Response` at `r`. -/
abbrev respF (f : GoString) (r : Loc) : Loc :=
  structFieldRef _root_.Perennial.net.http.Response f r

end fields

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **An address's protocol** (persistent predicates; see the file header). -/
structure Proto (GF : BundledGFunctors) where
  req : HReq → GName → IProp GF
  req_pers : ∀ R γk, Persistent (req R γk)
  resp : HReq → GName → w64 → List w8 → IProp GF
  resp_pers : ∀ R γk st w, Persistent (resp R γk st w)
  /-- (2026-10-23, rafthttp stage 5e) The headers a handler of the request may commit. -/
  rhdr : HReq → List (GoString × GoString) → Prop
  /-- (2026-10-24, D42) **The requests sent with a streamed body** (see the file header). -/
  streamed : HReq → Prop
  /-- (D42) **A streamed request's contract** `sreq R γk Pre Φ`: of a request of ticket `γk`
  whose body's prefixes are in `Pre` and complete streams in `Φ` (see the file header). -/
  sreq : HReq → GName → (List w8 → Prop) → (List w8 → Prop) → IProp GF
  sreq_pers : ∀ R γk Pre Φ, Persistent (sreq R γk Pre Φ)

instance Proto.req_persistent (P : Proto GF) (R : HReq) (γk : GName) : Persistent (P.req R γk) :=
  P.req_pers R γk

instance Proto.resp_persistent (P : Proto GF) (R : HReq) (γk : GName) (st : w64) (w : List w8) :
    Persistent (P.resp R γk st w) :=
  P.resp_pers R γk st w

instance Proto.sreq_persistent (P : Proto GF) (R : HReq) (γk : GName) (Pre Φ : List w8 → Prop) :
    Persistent (P.sreq R γk Pre Φ) :=
  P.sreq_pers R γk Pre Φ

/-- **The program's HTTP network**: each address's protocol, fixed for the run. -/
structure HttpNet (GF : BundledGFunctors) where
  proto : GoString → Proto GF

/-- **A request's ticket** (exclusive; D38b): allocated fresh by the client, given up to
`RoundTrip`, received by the handler of the request. -/
def reqTicket (γk : GName) : IProp GF := dghostVar γk (DFrac.own 1) ()

/-- A ticket is exclusive. -/
theorem reqTicket_excl (γk : GName) : reqTicket (GF := GF) γk ∗ reqTicket γk ⊢ False := by
  unfold reqTicket
  iintro ⟨H1, H2⟩
  ihave %Hbad := dghostVar_valid_2 γk () _ () _ $$ H1 H2
  exfalso
  have h := DFrac.valid_own_op Hbad.1
  exact absurd h (by decide)

/-- A fresh ticket. -/
theorem reqTicket_alloc : ⊢ |==> ∃ γk, reqTicket (GF := GF) γk := by
  unfold reqTicket
  iapply dghostVar_alloc

/-! ### Registration (stage 4e; see the file header) -/

/-- `httpProtoAt`'s fact, raw (opaque). -/
opaque httpProtoAtRaw (a : GoString) (P : Proto GF) : IProp GF

/-- **The address `a` is served with the protocol `P`** (persistent): what `http.register` gives
with the address's listener. -/
def httpProtoAt (a : GoString) (P : Proto GF) : IProp GF := iprop(□ httpProtoAtRaw a P)

instance httpProtoAt_persistent (a : GoString) (P : Proto GF) :
    Persistent (httpProtoAt (GF := GF) a P) := by
  unfold httpProtoAt; infer_instance

/-- **The right to serve the address `a` with the protocol `P`** (exclusive, opaque; D39a,
2026-10-23): what `reserve` gives with `httpProtoAt a P`, and `register` takes with the address's
listener. -/
opaque httpProtoOwn (a : GoString) (P : Proto GF) : IProp GF

/-- **The listener `l` bound at `a`, its protocol registered as `P`** (exclusive, opaque): what
`Serve` takes. -/
opaque httpListenerAt (l : GoInterface) (a : GoString) (P : Proto GF) : IProp GF

/-- The concurrency bound (D21 M2's `netProcSlots`, the user's (A)): at most `2 ^ 29` handlers at
once. -/
def httpProcSlots : Nat := 2 ^ 29

/-- **The URL string naming `host` and `path`** (opaque, pure): what
`url.URL{Scheme: "http", Host: host, Path: path}.String()` returns. -/
opaque urlOf (host path : GoString) : GoString

/-- **A host `url.Parse` accepts** (opaque, pure; 2026-10-23, stage 4e): the `Host` of a URL that
`url.Parse` returned (rafthttp's peer URLs, `types.NewURLs`). `NewRequest` of `urlOf host path`
parses again; a host `url.Parse` rejects may fail it (a Go test: `"a b"`, `"a:b:c"`, `"a/b"` make
`NewRequest` fail), so `NewRequest_spec` asks for it. -/
opaque urlHostOk (host : GoString) : Prop

/-- `io.EOF`'s value (`io`'s package variable). -/
def ioEOF (e : GoInterface) : IProp GF := globalAddr _root_.Perennial.io.EOF ↦□ e

instance ioEOF_persistent (e : GoInterface) : Persistent (ioEOF (GF := GF) e) := by
  unfold ioEOF; infer_instance

/-! ### The client's side -/

/-! ### Headers -/

/-- A header key's byte (`textproto.validHeaderFieldByte`): a token byte, RFC 7230's `tchar`. -/
def hdrTokenByte (c : w8) : Bool :=
  decide ((48 ≤ c.toNat ∧ c.toNat ≤ 57) ∨ (65 ≤ c.toNat ∧ c.toNat ≤ 90) ∨
    (97 ≤ c.toNat ∧ c.toNat ≤ 122) ∨
    c.toNat ∈ [33, 35, 36, 37, 38, 39, 42, 43, 45, 46, 94, 95, 96, 124, 126])

/-- `canonicalMIMEHeaderKey`'s loop: the first letter and each letter after `-` upper case, the
other letters lower case. -/
def canonLoop : Bool → List w8 → List w8
  | _, [] => []
  | upper, c :: cs =>
    let c' := if upper = true ∧ 97 ≤ c.toNat ∧ c.toNat ≤ 122 then c - W8 32
      else if upper = false ∧ 65 ≤ c.toNat ∧ c.toNat ≤ 90 then c + W8 32 else c
    c' :: canonLoop (c' == W8 45) cs

/-- **A header key canonicalized**: `textproto.CanonicalMIMEHeaderKey`, which `Header.Set` and
`Header.Get` apply to their key; a key with a byte that is not a token byte is left as it is.
(2026-10-23, rafthttp stage 5e: a definition, until then opaque, so that distinct keys are known
distinct.) -/
def canonKey (k : GoString) : GoString := if k.all hdrTokenByte then canonLoop true k else k

example : canonKey go!"X-Etcd-Cluster-ID" = go!"X-Etcd-Cluster-Id" := by decide
example : canonKey go!"x-server-version" = go!"X-Server-Version" := by decide

/-- `Header.Set(k, v)`'s effect on the list of (canonical key, value) pairs: `k`'s values
replaced by `v`. -/
def hdrSet (hs : List (GoString × GoString)) (k v : GoString) : List (GoString × GoString) :=
  hs.filter (fun kv => kv.1 ≠ canonKey k) ++ [(canonKey k, v)]

/-- `Header.Get(k)`: the first value of `k` (canonical), or `""`. -/
def hdrGet (hs : List (GoString × GoString)) (k : GoString) : GoString :=
  ((hs.find? (fun kv => kv.1 = canonKey k)).map Prod.snd).getD ""

theorem hdrGet_nil (k : GoString) : hdrGet [] k = "" := rfl

/-- `Get` of a key after `Set` of another (canonically distinct) key. -/
theorem hdrGet_hdrSet_ne (hs : List (GoString × GoString)) (k k' v : GoString)
    (h : canonKey k ≠ canonKey k') : hdrGet (hdrSet hs k v) k' = hdrGet hs k' := by
  unfold hdrGet hdrSet
  rw [List.find?_append]
  have h1 : (List.find? (fun kv => decide (kv.1 = canonKey k')) [(canonKey k, v)]) = none := by
    simp [h]
  have h2 : List.find? (fun kv => decide (kv.1 = canonKey k'))
      (List.filter (fun kv => decide (kv.1 ≠ canonKey k)) hs) =
      List.find? (fun kv => decide (kv.1 = canonKey k')) hs := by
    induction hs with
    | nil => rfl
    | cons x xs ih =>
      by_cases hx : x.1 = canonKey k
      · have : ¬ x.1 = canonKey k' := by rw [hx]; exact h
        rw [List.filter_cons_of_neg (by simp [hx]), List.find?_cons_of_neg (by simp [this]), ih]
      · rw [List.filter_cons_of_pos (by simp [hx])]
        by_cases hx' : x.1 = canonKey k'
        · rw [List.find?_cons_of_pos (by simp [hx']), List.find?_cons_of_pos (by simp [hx'])]
        · rw [List.find?_cons_of_neg (by simp [hx']), List.find?_cons_of_neg (by simp [hx']), ih]
  rw [h2, h1]
  cases List.find? (fun kv => decide (kv.1 = canonKey k')) hs <;> rfl

/-- `Get` of a key after its `Set`. -/
theorem hdrGet_hdrSet_eq (hs : List (GoString × GoString)) (k v : GoString) :
    hdrGet (hdrSet hs k v) k = v := by
  unfold hdrGet hdrSet
  rw [List.find?_append]
  have : List.find? (fun kv => decide (kv.1 = canonKey k))
      (List.filter (fun kv => decide (kv.1 ≠ canonKey k)) hs) = none := by
    rw [List.find?_eq_none]; intro x hx; simp [List.mem_filter] at hx; simp [hx.2]
  rw [this]; simp

/-- **A header map `hm` holding `hs`** (exclusive; a request's headers being built, or a response
writer's). -/
opaque hdrOwn (hm : Loc) (hs : List (GoString × GoString)) : IProp GF

/-- The header map `hm` of a received request, holding `hs` (opaque). -/
opaque hdrAtRaw (hm : Loc) (hs : List (GoString × GoString)) : IProp GF

/-- **A received request's header map `hm`, holding `hs`** (persistent): `Get` reads it. -/
def hdrAt (hm : Loc) (hs : List (GoString × GoString)) : IProp GF := iprop(□ hdrAtRaw hm hs)

instance hdrAt_persistent (hm : Loc) (hs : List (GoString × GoString)) :
    Persistent (hdrAt (GF := GF) hm hs) := by
  unfold hdrAt; infer_instance


/-- **The response headers Go's server sets itself** (canonical keys): `Date`, the body's
`Content-Type`, `Content-Length`, `Transfer-Encoding`, `Connection`, and `http.Error`'s
`X-Content-Type-Options`. (2026-10-23, rafthttp stage 5e.) -/
def srvKeys : List GoString :=
  [go!"Date", go!"Content-Type", go!"Content-Length", go!"Transfer-Encoding", go!"Connection",
    go!"X-Content-Type-Options"]

/-- **What the client sees of a response's committed headers `hs`**: `hc` agrees with them but
for the keys Go's server sets itself (`srvKeys`). -/
def srvView (hs hc : List (GoString × GoString)) : Prop :=
  ∀ k, canonKey k ∉ srvKeys → hdrGet hc k = hdrGet hs k

/-- **A response writer's header map, holding `hs`, not yet committed** (exclusive, opaque;
2026-10-23, rafthttp stage 5e): what `w.Header()` lends, and what the first `WriteHeader` or
`Write` commits. -/
opaque respHdrs (wr : GoInterface) (hs : List (GoString × GoString)) : IProp GF

/-! ### The client's side (continued) -/

/-- `reqRest`'s fact, raw (opaque): of the method, host, path and body only. -/
opaque reqRestRaw (r : Loc) (meth host path : GoString) (body : List w8) : IProp GF

/-- **The rest of a request being built** at `r` (exclusive): its method, URL, body and
context, those of `R` but for the headers, which `reqOwn` keeps in its `Header` map (2026-10-23,
stage 5e-3: stated over those fields only, so that setting a header leaves it as it is). -/
def reqRest (r : Loc) (R : HReq) : IProp GF := reqRestRaw r R.meth R.host R.path R.body

/-- **A request being built** at `r` (exclusive): `NewRequest`'s result; its `Header` field holds
the map `hm`, whose `Set`s before `RoundTrip` build `R.hdr`. -/
def reqOwn (r : Loc) (R : HReq) : IProp GF :=
  iprop(∃ hm : Loc, reqF go!"Header" r ↦□ hm ∗ hdrOwn hm R.hdr ∗ reqRest r R)

/-- **An error `ei` is of a well-formed error tree** (persistent; Perennial's `errors.errorIsTree`):
for a pointer target, it is in a tree `S` whose `Is` and `Unwrap` methods return, and whose errors
of the target's type hold pointers (`errors.TreeTyped`, Go's typing): what `errors.Is(err, target)`
needs (`errors.Is.spec`). (2026-10-23, rafthttp stage 5c: the stream reader's `run` asks
`errors.Is` of the errors `dial` and `decodeLoop` return.) -/
def errTreeOk (ei : GoInterfaceOk) : IProp GF :=
  iprop(□ ∀ target : GoInterface,
    ⌜∀ tii, target = GoInterface.ok tii → _root_.Perennial.errors.IsPointerError tii⌝ -∗
    ∃ (S : GoInterface → Prop) (M : GoInterfaceOk → Prop),
      ⌜S (GoInterface.ok ei) ∧ _root_.Perennial.errors.TreeTyped S target⌝ ∗
      _root_.Perennial.errors.errorIsTree S M target)

instance errTreeOk_persistent (ei : GoInterfaceOk) : Persistent (errTreeOk (GF := GF) ei) := by
  unfold errTreeOk; infer_instance

/-- **An error whose `Error()` returns** (persistent; `nil`, or a value whose `Error` method
returns some string, of a well-formed error tree, `errTreeOk`): what net/http's errors are (rafthttp
logs them, `err.Error()`, and asks `errors.Is` of them; the tree since 2026-10-23, stage 5c). -/
def errStrOk (e : GoInterface) : IProp GF :=
  iprop(⌜e = GoInterface.nil⌝ ∨ ∃ ei : GoInterfaceOk, ⌜e = GoInterface.ok ei⌝ ∗
    □ (∀ Φ : val → IProp GF, ▷ (∀ s : GoString, Φ #s) -∗
      WP (App (Val #(methods ei.ty go!"Error" ei.v)) (Val #())) {{ Φ }}) ∗ errTreeOk ei)

instance errStrOk_persistent (e : GoInterface) : Persistent (errStrOk (GF := GF) e) := by
  unfold errStrOk; infer_instance

/-- `nil` is an error whose `Error()` returns (vacuously). -/
theorem errStrOk_nil : ⊢ errStrOk (GF := GF) GoInterface.nil := by
  unfold errStrOk
  ileft; ipureintro; rfl

/-- **A reader holding exactly `bs`** (exclusive; `bytes.NewBuffer(bs)` as an `io.Reader`, or `nil`
for an empty body): what `NewRequest` takes as the body. -/
opaque readerHas (rd : GoInterface) (bs : List w8) : IProp GF

/-- **A stream's prefixes** (D42): `Pre` holds of `[]` and of every prefix of what it holds of. -/
def prefixClosed (Pre : List w8 → Prop) : Prop := Pre [] ∧ ∀ a b, Pre (a ++ b) → Pre a

/-- **A reader of a stream in `Pre` and `Φ`** (persistent, D42): its `Read` from a state `Src r`
(`r` read so far; `io.EOF`'s value `e`) reads `ys` with `r ++ ys` in `Pre`, and returns `EOF` only
at a complete stream, in `Φ`. The contract of a streamed body's reader on either side of the
connection (`streamHas`, `bodyStream_streamReaderOk`), and of a reader wrapping one. -/
def streamReaderOk (rd : GoInterface) (Src : List w8 → IProp GF) (Pre Φ : List w8 → Prop)
    (e : GoInterface) : IProp GF :=
  iprop(∃ ri : GoInterfaceOk, ⌜rd = GoInterface.ok ri⌝ ∗
    □ (∀ (r : List w8) (p : GoSlice) (xs : List w8),
      {{ Src r ∗ p ↦* xs ∗ ioEOF e }}
        (App (Val #(methods ri.ty go!"Read" ri.v)) (Val #p))
      {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
          ∃ ys : List w8, ⌜ys.length = sint.nat n ∧ Pre (r ++ ys) ∧ (err = e → Φ (r ++ ys))⌝ ∗
          p ↦* (ys ++ xs.drop ys.length) ∗ Src (r ++ ys) }}))

instance streamReaderOk_persistent (rd : GoInterface) (Src : List w8 → IProp GF)
    (Pre Φ : List w8 → Prop) (e : GoInterface) : Persistent (streamReaderOk rd Src Pre Φ e) := by
  unfold streamReaderOk; infer_instance

/-- **The right to read the stream of `rd`, in `Pre` and `Φ`** (exclusive, D42): a reader keeping
the contract, at its start. What `NewRequest` takes as a streamed body. -/
def streamHas (rd : GoInterface) (Pre Φ : List w8 → Prop) : IProp GF :=
  iprop(∃ (Src : List w8 → IProp GF) (e : GoInterface), ioEOF e ∗ streamReaderOk rd Src Pre Φ e ∗
    Src [] ∗ ⌜prefixClosed Pre⌝)

/-- **A request body as its client gives it** (D42): fixed bytes, or a stream in `Pre` and `Φ`. -/
inductive Body where
  | fixed (bs : List w8)
  | stream (Pre Φ : List w8 → Prop)

/-- A body's bytes in its request (`HReq.body`): a streamed body's are not the request's. -/
@[reducible] def Body.bytes : Body → List w8
  | .fixed bs => bs
  | .stream _ _ => []

/-- **A reader of the body `K`** (exclusive, D42): `readerHas` of a fixed body's bytes, `streamHas`
of a stream. -/
def bodyHas (rd : GoInterface) : Body → IProp GF
  | .fixed bs => readerHas rd bs
  | .stream Pre Φ => streamHas rd Pre Φ

theorem bodyHas_fixed (rd : GoInterface) (bs : List w8) :
    bodyHas (GF := GF) rd (.fixed bs) = readerHas rd bs := rfl

/-- `reqStream`'s fact, raw (opaque). -/
opaque reqStreamRaw (r : Loc) (Pre Φ : List w8 → Prop) : IProp GF

/-- **A request's streamed body** (exclusive, D42): the right to its body's stream, which
`RoundTrip` takes; nothing for a fixed body (its bytes are in `reqOwn`'s `HReq`). -/
@[reducible] def reqStream (r : Loc) : Body → IProp GF
  | .fixed _ => iprop(True)
  | .stream Pre Φ => reqStreamRaw r Pre Φ

/-- **A response's body reader** for the request `R` to `a`, of status `st`, having read `r`
(exclusive): its reads stay a prefix of what the handler wrote. -/
opaque respReader (H : HttpNet GF) (rd : GoInterface) (R : HReq) (γk : GName) (st : w64)
  (r : List w8) : IProp GF

/-- **A received response** at `resp` for `R`, of status `st` (persistent field facts: its
`StatusCode` is `st`, its `Header` some header map, its `Body` the reader `rd`, not `nil`). -/
def respAt (resp : Loc) (st : w64) (rd : GoInterface) (Hd : List (GoString × GoString) → Prop) :
    IProp GF :=
  iprop(respF go!"StatusCode" resp ↦□ st ∗
    (∃ (hm : Loc) (hs : List (GoString × GoString)), respF go!"Header" resp ↦□ hm ∗
      hdrAt (GF := GF) hm hs ∗ ⌜Hd hs⌝) ∗
    respF go!"Body" resp ↦□ rd ∗ ⌜rd ≠ GoInterface.nil⌝)

instance respAt_persistent (resp : Loc) (st : w64) (rd : GoInterface)
    (Hd : List (GoString × GoString) → Prop) : Persistent (respAt (GF := GF) resp st rd Hd) := by
  unfold respAt; infer_instance

/-- `respCloserRaw`'s fact, raw (opaque). -/
opaque respCloserRaw (rd : GoInterface) : IProp GF

/-- **The right to close a response's body** `rd` (persistent; 2026-10-23, stage 5c): what
`RoundTrip` gives with the body. Go's response body supports a `Close` from another goroutine,
concurrent with a `Read` (it ends the connection's read: the reader then fails), and more than one
`Close`; the stream reader's `stop` closes the body its `decodeLoop` reads. -/
def respCloser (rd : GoInterface) : IProp GF := iprop(□ respCloserRaw rd)

instance respCloser_persistent (rd : GoInterface) : Persistent (respCloser (GF := GF) rd) := by
  unfold respCloser; infer_instance

/-- **How a request of body `K` may be sent** (D42): a fixed body for a request its host's
protocol does not stream; a streamed body for one it does, with the protocol's contract of it. -/
@[reducible] def reqSendOk (H : HttpNet GF) (R : HReq) (γk : GName) : Body → IProp GF
  | .fixed _ => iprop(⌜¬ (H.proto R.host).streamed R⌝)
  | .stream Pre Φ => iprop(⌜(H.proto R.host).streamed R ∧ R.body = []⌝ ∗
      □ (H.proto R.host).sreq R γk Pre Φ)

/-- `netErr`'s fact, raw (opaque). -/
opaque netErrRaw (e : GoInterface) : IProp GF

/-- **An error net/http made** (persistent; 2026-10-24, rafthttp stage 7d): `RoundTrip`'s, a
response body read's (`ReadAll_any_spec`). Such an error wraps nothing of the program's but its
request body's reader's errors; what rafthttp concludes of it is `rafthttp.netErrNotRemoved_spec`
(it is not rafthttp's `errMemberRemoved`). -/
def netErr (e : GoInterface) : IProp GF := iprop(□ netErrRaw e)

instance netErr_persistent (e : GoInterface) : Persistent (netErr (GF := GF) e) := by
  unfold netErr; infer_instance

/-- **A round tripper of the network `H`** (persistent; what rafthttp's names-only
`NewRoundTripper`/`newStreamRoundTripper` return): `RoundTrip` of a request built for `R`, with
its ticket `γk`, the protocol registered for its host (`httpProtoAt`) and
`□ (H.proto R.host).req R γk`, (D42) its body of a kind the protocol allows (`reqSendOk`, with a
streamed body's stream, `reqStream`, which `RoundTrip` consumes), either fails (with an error of
net/http's, `netErr`: stage 7d) or returns a response whose status
`st` is the handler's (with `□ ∃ w, resp R γk st w`) and whose body reader starts at `[]`, with
the right to close the body (`respCloser`, 2026-10-23, stage 5e-3); the request is the caller's
again (`RoundTrip` must not modify it). -/
def roundTripperOk (H : HttpNet GF) (rt : GoInterface) : IProp GF :=
  iprop(∃ ti : GoInterfaceOk, ⌜rt = GoInterface.ok ti⌝ ∗
    □ (∀ (r : Loc) (R : HReq) (γk : GName) (K : Body),
      {{ reqOwn r R ∗ reqStream r K ∗ reqSendOk H R γk K ∗ reqTicket γk ∗
          httpProtoAt R.host (H.proto R.host) ∗ □ (H.proto R.host).req R γk }}
        (App (Val #(methods ti.ty go!"RoundTrip" ti.v)) (Val #r))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); reqOwn r R ∗
          (⌜err ≠ GoInterface.nil⌝ ∗ errStrOk err ∗ netErr err ∨
           ⌜err = GoInterface.nil⌝ ∗ ∃ (st : w64) (rd : GoInterface),
            respAt resp st rd (fun hc => ∃ hs, (H.proto R.host).rhdr R hs ∧ srvView hs hc) ∗
            (□ ∃ w, (H.proto R.host).resp R γk st w) ∗
            respReader H rd R γk st [] ∗ respCloser rd) }}))

instance roundTripperOk_persistent (H : HttpNet GF) (rt : GoInterface) :
    Persistent (roundTripperOk H rt) := by
  unfold roundTripperOk; infer_instance

/-! ### The server's side -/

/-- **A received request** at `r` (persistent field facts): its `Method`, `URL` (a `*url.URL` whose
`Path` is `R.path`), `Header` (`hdrAt` of `R.hdr`), `RemoteAddr` (some ASCII string: the server
writes the peer's `ip:port`) and `Body` (the reader `rd`, never `nil`: the server sets `NoBody`
for an empty one). -/
def reqAt (r : Loc) (R : HReq) (rd : GoInterface) : IProp GF :=
  iprop(reqF go!"Method" r ↦□ R.meth ∗
    (∃ u : Loc, reqF go!"URL" r ↦□ u ∗
      urlF go!"Path" u ↦□ R.path) ∗
    (∃ hm : Loc, reqF go!"Header" r ↦□ hm ∗ hdrAt hm R.hdr) ∗
    (∃ ra : GoString, reqF go!"RemoteAddr" r ↦□ ra ∗ ⌜asciiStr ra⌝) ∗
    reqF go!"Body" r ↦□ rd ∗ ⌜rd ≠ GoInterface.nil⌝)

instance reqAt_persistent (r : Loc) (R : HReq) (rd : GoInterface) :
    Persistent (reqAt (GF := GF) r R rd) := by
  unfold reqAt; infer_instance

/-- **A request body's reader** for `R`, having read `r` (exclusive): reads stay a prefix of
`R.body`; `EOF` only once all of it is read. -/
opaque bodyReader (rd : GoInterface) (R : HReq) (r : List w8) : IProp GF

/-- **A streamed request body's reader**, in `Pre` and `Φ`, having read `r` (exclusive, D42): its
reads stay in `Pre`; `EOF` only at a complete stream, in `Φ` (`bodyStreamRead_spec`). -/
opaque bodyStream (rd : GoInterface) (Pre Φ : List w8 → Prop) (r : List w8) : IProp GF

/-- **A received request's body** (D42): the request's bytes for a request its protocol does not
stream (`bodyReader`); for one it does, a stream in `Pre` and `Φ` of the protocol's contract
(`bodyStream`). -/
def reqBody (H : HttpNet GF) (a : GoString) (R : HReq) (γk : GName) (rd : GoInterface) :
    IProp GF :=
  iprop((⌜¬ (H.proto a).streamed R⌝ ∗ bodyReader rd R []) ∨
    (⌜(H.proto a).streamed R⌝ ∗ ∃ Pre Φ : List w8 → Prop,
      □ (H.proto a).sreq R γk Pre Φ ∗ ⌜prefixClosed Pre⌝ ∗ bodyStream rd Pre Φ []))

/-- A request the protocol does not stream has its bytes as its body. -/
theorem reqBody_fixed (H : HttpNet GF) (a : GoString) (R : HReq) (γk : GName) (rd : GoInterface)
    (h : ¬ (H.proto a).streamed R) : reqBody H a R γk rd ⊢ bodyReader rd R [] := by
  unfold reqBody
  iintro (⟨-, Hb⟩ | ⟨%hs, -⟩)
  · iexact Hb
  · exact absurd hs h

/-- **A response writer** for the request `R` to `a`, with the status set (`none` before
`WriteHeader`) and the bytes written `w` (exclusive; it may be passed to another goroutine, as the
stream handler does). -/
opaque respWriter (H : HttpNet GF) (wr : GoInterface) (a : GoString) (R : HReq) (γk : GName)
  (st : Option w64) (w : List w8) : IProp GF

/-- **A handler's response writer when it returns** (2026-10-23, rafthttp stage 5e): given back
(Go: "A ResponseWriter may not be used after the Handler.ServeHTTP method has returned"),
committed, or not if the handler panics (`Serve` recovers the panic and drops the connection). -/
def handlerDone (H : HttpNet GF) (wr : GoInterface) (a : GoString) (R : HReq) (γk : GName)
    (v : val) : IProp GF :=
  iprop((∃ st w, respWriter H wr a R γk (some st) w) ∨
    ⌜v.isPanic = true⌝ ∗ respWriter H wr a R γk none [])

/-- **A handler of the address `a`** (persistent), lending each invocation the resource `Rs`:
`ServeHTTP` of any request the network delivers to `a`, with its ticket, its body (`reqBody`,
D42: fixed or streamed, as the protocol says) and a
fresh response writer (a non-`nil` interface value, an `http.Flusher`: the server's writers are)
with its empty header map, returns `Rs` and the writer (`handlerDone`; or panics, giving them back
too: `Serve` recovers the panic). -/
def handlerOk (H : HttpNet GF) (a : GoString) (Rs : IProp GF) (h : GoInterface) : IProp GF :=
  iprop(∃ hi : GoInterfaceOk, ⌜h = GoInterface.ok hi⌝ ∗
    □ (∀ (wi : GoInterfaceOk) (r : Loc) (R : HReq) (γk : GName) (rd : GoInterface),
      reqAt r R rd -∗ ⌜R.host = a⌝ -∗ □ (H.proto a).req R γk -∗ reqTicket γk -∗
        reqBody H a R γk rd -∗ respWriter H (GoInterface.ok wi) a R γk none [] -∗
        respHdrs (GoInterface.ok wi) [] -∗
        ⌜go.typeSetContains wi.ty _root_.Perennial.net.http.Flusher.ty = true⌝ -∗ Rs -∗
        WP (App (App (Val #(methods hi.ty go!"ServeHTTP" hi.v)) (Val #(GoInterface.ok wi)))
          (Val #r)) {{ v, Rs ∗ handlerDone H (GoInterface.ok wi) a R γk v }}))

/-- **Before a response's commit, its headers are ready** (2026-10-23, rafthttp stage 5e): the
header map not yet committed, holding headers of the protocol (`rhdr`); nothing once committed. -/
def hdrsReady (H : HttpNet GF) (wr : GoInterface) (a : GoString) (R : HReq) :
    Option w64 → IProp GF
  | none => iprop(∃ hs, respHdrs wr hs ∗ ⌜(H.proto a).rhdr R hs⌝)
  | some _ => iprop(True)

/-! ### The specs (statements for review; see the file header) -/

/-- `http.Serve(l, h)` on the listener bound at `a` with `a`'s protocol registered, with a handler
of `a` and `httpProcSlots`
copies of the resource its invocations borrow: returns an error if it returns (it serves each
request on its own goroutine). -/
def Serve_spec (H : HttpNet GF) : Prop :=
  ∀ (l h : GoInterface) (a : GoString) (Rs : IProp GF),
    ⊢ {{ httpListenerAt (GF := GF) l a (H.proto a) ∗ handlerOk H a Rs h ∗
          [∗list] _x ∈ List.replicate httpProcSlots (), Rs }}
        (App (App (Val (@! _root_.Perennial.net.http.Serve)) (Val #l)) (Val #h))
      {{ (err : GoInterface), RET #err; True }}

/-- A request body's `Read(p)`: some `n` bytes `ys` (into `p`'s first `n`), still a prefix of the
body; `EOF` only at the end. -/
def bodyRead_spec : Prop :=
  ∀ (rd : GoInterface) (ri : GoInterfaceOk) (R : HReq) (r : List w8) (p : GoSlice)
    (xs : List w8) (e : GoInterface),
    rd = GoInterface.ok ri →
    ⊢ {{ bodyReader (GF := GF) rd R r ∗ p ↦* xs ∗ ioEOF e }}
        (App (Val #(methods ri.ty go!"Read" ri.v)) (Val #p))
      {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
          ∃ ys : List w8, ⌜ys.length = sint.nat n ∧ r ++ ys <+: R.body ∧
            (err = e → r ++ ys = R.body)⌝ ∗
          p ↦* (ys ++ xs.drop ys.length) ∗ bodyReader rd R (r ++ ys) }}

/-- (D42) A streamed request body's `Read(p)`: some `n` bytes `ys` (into `p`'s first `n`), with
what has been read in `Pre`; `EOF` only at a complete stream, in `Φ`. The physical assumption of
the file header: a chunked body's bytes the server reads are a prefix of what the client's reader
yielded, and end with `EOF` only where the reader's stream did. -/
def bodyStreamRead_spec : Prop :=
  ∀ (rd : GoInterface) (ri : GoInterfaceOk) (Pre Φ : List w8 → Prop) (r : List w8) (p : GoSlice)
    (xs : List w8) (e : GoInterface),
    rd = GoInterface.ok ri →
    ⊢ {{ bodyStream (GF := GF) rd Pre Φ r ∗ p ↦* xs ∗ ioEOF e }}
        (App (Val #(methods ri.ty go!"Read" ri.v)) (Val #p))
      {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
          ∃ ys : List w8, ⌜ys.length = sint.nat n ∧ Pre (r ++ ys) ∧ (err = e → Φ (r ++ ys))⌝ ∗
          p ↦* (ys ++ xs.drop ys.length) ∗ bodyStream rd Pre Φ (r ++ ys) }}

/-- (D42) `io.ReadFull(rd, p)` of a streamed request body: `len(p)` bytes, with what has been read
in `Pre`, or fewer and an error whose `Error()` returns (net/http's or `io.ErrUnexpectedEOF`): the
envelope decoder's read (`messageDecoder.decodeLimit`, over `readFullAt`). -/
def ReadFull_stream_spec : Prop :=
  ∀ (rd : GoInterface) (Pre Φ : List w8 → Prop) (r : List w8) (p : GoSlice) (xs : List w8),
    ⊢ {{ bodyStream (GF := GF) rd Pre Φ r ∗ p ↦* xs }}
        (App (App (Val (@! _root_.Perennial.io.ReadFull)) (Val #rd)) (Val #p))
      {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
          ∃ ys : List w8, ⌜sint.Z n = ys.length ∧ ys.length ≤ xs.length ∧
            (err = GoInterface.nil → ys.length = xs.length) ∧ Pre (r ++ ys)⌝ ∗
          p ↦* (ys ++ xs.drop ys.length) ∗ bodyStream rd Pre Φ (r ++ ys) ∗ errStrOk err }}

/-- A response body's `Read(p)`: some bytes, still a prefix of some `w` the handler wrote with
`□ resp R st w`. -/
def respRead_spec (H : HttpNet GF) : Prop :=
  ∀ (rd : GoInterface) (ri : GoInterfaceOk) (R : HReq) (γk : GName) (st : w64) (r : List w8)
    (p : GoSlice) (xs : List w8),
    rd = GoInterface.ok ri →
    ⊢ {{ respReader H rd R γk st r ∗ p ↦* xs }}
        (App (Val #(methods ri.ty go!"Read" ri.v)) (Val #p))
      {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
          ∃ ys : List w8, ⌜ys.length = sint.nat n⌝ ∗
          (□ ∃ w, ⌜r ++ ys <+: w⌝ ∗ (H.proto R.host).resp R γk st w) ∗
          p ↦* (ys ++ xs.drop ys.length) ∗ respReader H rd R γk st (r ++ ys) }}

/-- `ResponseWriter.Write(b)`: needs the protocol of what has then been written; writes the first
`n` bytes, all of them unless it fails (`io.Writer`'s contract: an error if `n < len(b)`; 2026-10-23,
stage 5b: until then all of `b` was recorded, whatever `n`), with an error whose `Error()` returns
(net/http's, `errStrOk`). -/
def respWrite_spec (H : HttpNet GF) : Prop :=
  ∀ (wr : GoInterface) (wi : GoInterfaceOk) (a : GoString) (R : HReq) (γk : GName)
    (st : Option w64) (w : List w8) (b : GoSlice) (bs : List w8) (dq : DFrac),
    wr = GoInterface.ok wi →
    ⊢ {{ respWriter H wr a R γk st w ∗ b ↦*{dq} bs ∗
          □ (H.proto a).resp R γk (st.getD (W64 200)) (w ++ bs) ∗ hdrsReady H wr a R st }}
        (App (Val #(methods wi.ty go!"Write" wi.v)) (Val #b))
      {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
          ∃ k : Nat, b ↦*{dq} bs ∗ respWriter H wr a R γk (some (st.getD (W64 200))) (w ++ bs.take k) ∗
          ⌜sint.Z n = k ∧ k ≤ bs.length ∧ (err = GoInterface.nil → k = bs.length)⌝ ∗ errStrOk err }}

/-- `ResponseWriter.WriteHeader(st)` before any write: sets the status, which needs the protocol
of the (still empty) response with it. (Stage 4e) A final status, `200` to `999`: Go panics
outside `100`-`999` (`checkWriteHeaderCode`) and does not set an informational `1xx` one. -/
def respWriteHeader_spec (H : HttpNet GF) : Prop :=
  ∀ (wr : GoInterface) (wi : GoInterfaceOk) (a : GoString) (R : HReq) (γk : GName) (st : w64),
    wr = GoInterface.ok wi →
    ⊢ {{ respWriter H wr a R γk none [] ∗ □ (H.proto a).resp R γk st [] ∗
          ⌜200 ≤ sint.Z st ∧ sint.Z st ≤ 999⌝ ∗ hdrsReady H wr a R none }}
        (App (Val #(methods wi.ty go!"WriteHeader" wi.v)) (Val #st))
      {{ RET #(); respWriter H wr a R γk (some st) [] }}

/-- `http.NewRequest(method, url, body)`, with a body reader holding `bs` and a URL naming `host`
and `path` (`urlOf`, the URL `url.URL{Scheme: "http", Host: host, Path: path}.String()` gives, as
rafthttp builds them): a request of method, host, path and body, no headers. (2026-10-23, stage 4d)
No error for `GET` or `POST`: `NewRequest` fails only on an invalid method or a URL that does not
parse, and the string of a parsed URL's host and a path parses (`urlHostOk`, stage 4e). (2026-10-24,
D42) Of a fixed or a streamed body `K` (`bodyHas`): a streamed body's stream moves into the
request (`reqStream`); Go keeps a reader that is not a `*bytes.Buffer`, `*bytes.Reader` or
`*strings.Reader` as the body, of unknown length, which its client sends chunked. -/
def NewRequest_spec : Prop :=
  ∀ (meth u : GoString) (body : GoInterface) (K : Body) (host path : GoString),
    u = urlOf host path → urlHostOk host → (meth = go!"POST" ∨ meth = go!"GET") →
    ⊢ {{ bodyHas (GF := GF) body K }}
        (App (App (App (Val (@! _root_.Perennial.net.http.NewRequest)) (Val #meth)) (Val #u))
          (Val #body))
      {{ (r : Loc), RET (PairV #r #GoInterface.nil);
          reqOwn r ⟨meth, host, path, [], K.bytes⟩ ∗ reqStream r K }}

/-- `hm.Set(k, v)` (`http.Header`'s, a method of the map type) on a header map being built. -/
def HeaderSet_spec : Prop :=
  ∀ (hm : Loc) (hs : List (GoString × GoString)) (k v : GoString),
    ⊢ {{ hdrOwn (GF := GF) hm hs }}
        (App (App (Val (hm @!! _root_.Perennial.net.http.Header.ty @!! go!"Set")) (Val #k))
          (Val #v))
      {{ RET #(); hdrOwn hm (hdrSet hs k v) }}

/-- `(&hm).Set(k, v)`, through a pointer to a header map being built (Go's pointer-method wrapper of
`Set`, as `req.Header.Set(k, v)` compiles): the map's `Set`. (2026-10-23, rafthttp stage 5e-3.) -/
def HeaderSetPtr_spec : Prop :=
  ∀ (p hm : Loc) (hs : List (GoString × GoString)) (k v : GoString),
    ⊢ {{ p ↦□ hm ∗ hdrOwn (GF := GF) hm hs }}
        (App (App (Val (p @!! go.GoType.PointerType _root_.Perennial.net.http.Header.ty @!! go!"Set"))
          (Val #k)) (Val #v))
      {{ RET #(); hdrOwn hm (hdrSet hs k v) }}

/-- `hm.Get(k)` on a received request's header map. -/
def HeaderGet_spec : Prop :=
  ∀ (hm : Loc) (hs : List (GoString × GoString)) (k : GoString),
    ⊢ {{ hdrAt (GF := GF) hm hs }}
        (App (Val (hm @!! _root_.Perennial.net.http.Header.ty @!! go!"Get")) (Val #k))
      {{ RET #(hdrGet hs k); True }}

/-- `(&hm).Get(k)`, through a pointer to a header map (Go's pointer-method wrapper of `Get`, as
`r.Header.Get(k)` compiles): the map's `Get`. (2026-10-23, rafthttp stage 5e-2.) -/
def HeaderGetPtr_spec : Prop :=
  ∀ (p hm : Loc) (hs : List (GoString × GoString)) (k : GoString),
    ⊢ {{ p ↦□ hm ∗ hdrAt (GF := GF) hm hs }}
        (App (Val (p @!! go.GoType.PointerType _root_.Perennial.net.http.Header.ty @!! go!"Get"))
          (Val #k))
      {{ RET #(hdrGet hs k); True }}

/-- `w.Header()` of a response writer before its commit: its header map, lent to be `Set` (2026-10-23,
rafthttp stage 5e: the headers it holds, which the commit needs of the protocol; until then a
map the handler set freely, unconstrained for the client). -/
def RespHeader_spec : Prop :=
  ∀ (wr : GoInterface) (wi : GoInterfaceOk) (hs : List (GoString × GoString)),
    wr = GoInterface.ok wi →
    ⊢ {{ respHdrs (GF := GF) wr hs }}
        (App (Val #(methods wi.ty go!"Header" wi.v)) (Val #()))
      {{ (hm : Loc), RET #hm; hdrOwn hm hs ∗ (∀ hs', hdrOwn hm hs' -∗ respHdrs wr hs') }}

/-- **A reader of the bytes `B`** (persistent, D38b): its `Read` from a state `Src r` (`r` read so
far; `io.EOF`'s value `e`) reads `ys`, still a prefix of `B`, and returns `EOF` (`e`) only once `r ++ ys = B` -- the
`io.Reader` contract of a request body (`bodyRead_spec`) and of any reader wrapping one. -/
def prefixReaderOk (rd : GoInterface) (Src : List w8 → IProp GF) (B : List w8) (e : GoInterface) :
    IProp GF :=
  iprop(∃ ri : GoInterfaceOk, ⌜rd = GoInterface.ok ri⌝ ∗
    □ (∀ (r : List w8) (p : GoSlice) (xs : List w8),
      {{ Src r ∗ p ↦* xs ∗ ioEOF e }}
        (App (Val #(methods ri.ty go!"Read" ri.v)) (Val #p))
      {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
          ∃ ys : List w8, ⌜ys.length = sint.nat n ∧ r ++ ys <+: B ∧ (err = e → r ++ ys = B)⌝ ∗
          p ↦* (ys ++ xs.drop ys.length) ∗ Src (r ++ ys) }}))

instance prefixReaderOk_persistent (rd : GoInterface) (Src : List w8 → IProp GF) (B : List w8)
    (e : GoInterface) : Persistent (prefixReaderOk rd Src B e) := by
  unfold prefixReaderOk; infer_instance

/-- `io.ReadAll(rd)` of a reader of `B` (D38b: over any reader keeping the prefix contract, a
request body's or a wrapper's): the whole of `B`, or an error. -/
def ReadAll_spec : Prop :=
  ∀ (rd : GoInterface) (Src : List w8 → IProp GF) (B : List w8) (e : GoInterface),
    ⊢ {{ prefixReaderOk rd Src B e ∗ Src [] ∗ ioEOF e }}
        (App (Val (@! _root_.Perennial.io.ReadAll)) (Val #rd))
      {{ (sl : GoSlice) (err : GoInterface), RET (PairV #sl #err);
          ⌜err ≠ GoInterface.nil⌝ ∨ ⌜err = GoInterface.nil⌝ ∗ sl ↦* B }}

/-- `io.ReadFull(rd, p)` of a response body: `len(p)` bytes, still a prefix of what the handler
wrote, or fewer and an error (2026-10-23, stage 5c: the bound stated, and the error's `Error()`
returns, net/http's or `io.ErrUnexpectedEOF`). -/
def ReadFull_resp_spec (H : HttpNet GF) : Prop :=
  ∀ (rd : GoInterface) (R : HReq) (γk : GName) (st : w64) (r : List w8) (p : GoSlice)
    (xs : List w8),
    ⊢ {{ respReader H rd R γk st r ∗ p ↦* xs }}
        (App (App (Val (@! _root_.Perennial.io.ReadFull)) (Val #rd)) (Val #p))
      {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
          ∃ ys : List w8, ⌜sint.Z n = ys.length ∧ ys.length ≤ xs.length ∧
            (err = GoInterface.nil → ys.length = xs.length)⌝ ∗
          (□ ∃ w, ⌜r ++ ys <+: w⌝ ∗ (H.proto R.host).resp R γk st w) ∗
          p ↦* (ys ++ xs.drop ys.length) ∗ respReader H rd R γk st (r ++ ys) ∗ errStrOk err }}

/-- `w.(http.Flusher).Flush()` on a response writer: returns (it matters for latency, not for
safety). -/
def Flush_spec (H : HttpNet GF) : Prop :=
  ∀ (wr : GoInterface) (wi : GoInterfaceOk) (a : GoString) (R : HReq) (γk : GName)
    (st : Option w64) (w : List w8),
    wr = GoInterface.ok wi →
    ⊢ {{ respWriter H wr a R γk st w }}
        (App (Val #(methods wi.ty go!"Flush" wi.v)) (Val #()))
      {{ RET #(); respWriter H wr a R γk st w }}

/-- `http.Error(w, msg, code)` before any write: the status `code`, the body `msg` and a newline.
(Stage 4e) A final status, as `WriteHeader`'s (`respWriteHeader_spec`), which it calls. -/
def Error_spec (H : HttpNet GF) : Prop :=
  ∀ (wr : GoInterface) (a : GoString) (R : HReq) (γk : GName) (msg : GoString) (code : w64),
    ⊢ {{ respWriter H wr a R γk none [] ∗ □ (H.proto a).resp R γk code (msg ++ [W8 10]) ∗
          ⌜200 ≤ sint.Z code ∧ sint.Z code ≤ 999⌝ ∗ hdrsReady H wr a R none }}
        (App (App (App (Val (@! _root_.Perennial.net.http.Error)) (Val #wr)) (Val #msg))
          (Val #code))
      {{ RET #(); respWriter H wr a R γk (some code) (msg ++ [W8 10]) }}

/-! ### The pipeline's client side (rafthttp stage 4d) -/

/-- `bytes.NewBuffer(b)` (`bytes`, names-only): a reader holding `b`'s bytes, which it takes. -/
def NewBuffer_spec : Prop :=
  ∀ (b : GoSlice) (bs : List w8),
    ⊢ {{ (b ↦* bs : IProp GF) }}
        (App (Val (@! _root_.Perennial.bytes.NewBuffer)) (Val #b))
      {{ (rd : Loc), RET #rd;
          readerHas (interface.mkOk (go.GoType.PointerType _root_.Perennial.bytes.Buffer.ty) #rd) bs }}

/-- `r.WithContext(ctx)` of a request being built: a shallow copy, the same request (for a
non-`nil` context); (D42) its body too (a streamed body's stream, `reqStream`). -/
def WithContext_spec : Prop :=
  ∀ (r : Loc) (R : HReq) (K : Body) (ctx : GoInterfaceOk),
    ⊢ {{ reqOwn (GF := GF) r R ∗ reqStream r K }}
        (App (Val (r @!! go.GoType.PointerType _root_.Perennial.net.http.Request.ty @!! go!"WithContext"))
          (Val #(GoInterface.ok ctx)))
      {{ (r' : Loc), RET #r'; reqOwn r' R ∗ reqStream r' K }}

/-- `io.ReadAll(rd)` of a response body: some bytes read (a prefix of what the handler wrote,
`respRead_spec`'s), or an error. -/
def ReadAll_resp_spec (H : HttpNet GF) : Prop :=
  ∀ (rd : GoInterface) (R : HReq) (γk : GName) (st : w64),
    ⊢ {{ respReader H rd R γk st [] }}
        (App (Val (@! _root_.Perennial.io.ReadAll)) (Val #rd))
      {{ (sl : GoSlice) (err : GoInterface), RET (PairV #sl #err);
          ∃ bs : List w8, sl ↦* bs ∗ respReader H rd R γk st bs ∗ errStrOk err }}

/-- `respReadAny`'s fact, raw (opaque). -/
opaque respReadAnyRaw (rd : GoInterface) : IProp GF

/-- **A response body read without a guarantee** (persistent; 2026-10-24, rafthttp stage 7d): its
reads, from any goroutine, return any bytes. Two goroutines reading one body (the snapshot sender's
`io.ReadAll` and its timer's `GracefulClose`, which drains the body after a timeout) may each take
bytes the other would have read, so neither read is a prefix of what the handler wrote; Go's
response body serializes its reads, so they are safe. What a reader of the body becomes by giving
up its guarantee (`respReadAny_of_spec`). -/
def respReadAny (rd : GoInterface) : IProp GF := iprop(□ respReadAnyRaw rd)

instance respReadAny_persistent (rd : GoInterface) : Persistent (respReadAny (GF := GF) rd) := by
  unfold respReadAny; infer_instance

/-- **A response body's reader gives up its guarantee** (stage 7d): its reads from then on are
`respReadAny`'s. -/
def respReadAny_of_spec (H : HttpNet GF) : Prop :=
  ∀ (rd : GoInterface) (R : HReq) (γk : GName) (st : w64) (r : List w8),
    respReader H rd R γk st r ⊢ respReadAny rd

/-- `io.ReadAll(rd)` of a response body read without a guarantee (stage 7d): some bytes and an
error whose `Error()` returns. -/
def ReadAll_any_spec : Prop :=
  ∀ (rd : GoInterface),
    ⊢ {{ respReadAny (GF := GF) rd }}
        (App (Val (@! _root_.Perennial.io.ReadAll)) (Val #rd))
      {{ (sl : GoSlice) (err : GoInterface), RET (PairV #sl #err);
          ∃ bs : List w8, sl ↦* bs ∗ errStrOk err ∗ netErr err }}

/-- A response body's `Close()` with its closer right, from any goroutine, any number of times:
some error, whose `Error()` returns. -/
def RespCloseAny_spec : Prop :=
  ∀ (rd : GoInterface) (ri : GoInterfaceOk),
    rd = GoInterface.ok ri →
    ⊢ {{ respCloser (GF := GF) rd }}
        (App (Val #(methods ri.ty go!"Close" ri.v)) (Val #()))
      {{ (err : GoInterface), RET #err; errStrOk err }}

/-- (`rafthttp.Transport.Stop`'s; stage 6c) `tr.CloseIdleConnections()` of a round tripper of
`roundTripperOk` whose dynamic type is `*http.Transport`: its value is a pointer `tr` (Go's typing:
a value of a pointer type), and closing `tr`'s idle connections returns. Go's
`CloseIdleConnections` is safe concurrently with requests; a `*http.Transport` round tripper is
not `nil` (`RoundTrip` of a `nil` one panics, which `roundTripperOk`'s `RoundTrip` does not). -/
def CloseIdleConnections_spec (H : HttpNet GF) : Prop :=
  ∀ ti : GoInterfaceOk, ti.ty = go.GoType.PointerType _root_.Perennial.net.http.Transport.ty →
    ⊢ roundTripperOk H (GoInterface.ok ti) -∗ ∃ tr : Loc, ⌜ti.v = #tr⌝ ∗
      {{ True }}
        (App (Val (tr @!! go.GoType.PointerType _root_.Perennial.net.http.Transport.ty @!!
          go!"CloseIdleConnections")) (Val #()))
      {{ RET #(); True }}

/-- A response body's `Close()`: some error. -/
def RespClose_spec (H : HttpNet GF) : Prop :=
  ∀ (rd : GoInterface) (ri : GoInterfaceOk) (R : HReq) (γk : GName) (st : w64) (r : List w8),
    rd = GoInterface.ok ri →
    ⊢ {{ respReader H rd R γk st r }}
        (App (Val #(methods ri.ty go!"Close" ri.v)) (Val #()))
      {{ (err : GoInterface), RET #err; True }}

/-! ### Routing (`http.ServeMux`) -/

/-- A pattern matches a path (Go's `ServeMux` for plain path patterns, as rafthttp registers):
a pattern ending in `/` matches its subtree, any other only itself. -/
def patMatches (pat path : GoString) : Bool :=
  if pat.getLast? = some (W8 47) then pat.isPrefixOf path else pat == path

/-- The pattern a path is routed to: the longest registered pattern that matches it. -/
def route (pats : List GoString) (path : GoString) : Option GoString :=
  (pats.filter (fun p => patMatches p path)).foldl
    (fun best p => match best with
      | none => some p
      | some b => if b.length < p.length then some p else some b) none

/-- **A mux being built** at `m` (exclusive): its registrations so far. -/
opaque muxOwn (m : Loc) (regs : List (GoString × GoInterface)) : IProp GF

/-- `http.NewServeMux()`: an empty mux. -/
def NewServeMux_spec : Prop :=
  ⊢ {{ (True : IProp GF) }}
      (App (Val (@! _root_.Perennial.net.http.NewServeMux)) (Val #()))
    {{ (m : Loc), RET #m; muxOwn m [] }}

/-- `m.Handle(pat, h)`: the registration appended (a pattern registered twice panics in Go; the
callers register distinct ones, which the precondition states). -/
def Handle_spec : Prop :=
  ∀ (m : Loc) (regs : List (GoString × GoInterface)) (pat : GoString) (h : GoInterface),
    ⊢ {{ muxOwn (GF := GF) m regs ∗ ⌜pat ∉ regs.map Prod.fst⌝ }}
        (App (App (Val (m @!! go.GoType.PointerType _root_.Perennial.net.http.ServeMux.ty @!!
          go!"Handle")) (Val #pat)) (Val #h))
      {{ RET #(); muxOwn m (regs ++ [(pat, h)]) }}

/-- **A handler of `a` for the requests routed to `pat`** (persistent): as `handlerOk`, for the
requests whose path `route` sends to `pat`. -/
def handlerFor (H : HttpNet GF) (a : GoString) (Rs : IProp GF) (pats : List GoString)
    (pat : GoString) (h : GoInterface) : IProp GF :=
  iprop(∃ hi : GoInterfaceOk, ⌜h = GoInterface.ok hi⌝ ∗
    □ (∀ (wi : GoInterfaceOk) (r : Loc) (R : HReq) (γk : GName) (rd : GoInterface),
      reqAt r R rd -∗ ⌜R.host = a ∧ route pats R.path = some pat⌝ -∗ □ (H.proto a).req R γk -∗
        reqTicket γk -∗ reqBody H a R γk rd -∗ respWriter H (GoInterface.ok wi) a R γk none [] -∗
        respHdrs (GoInterface.ok wi) [] -∗
        ⌜go.typeSetContains wi.ty _root_.Perennial.net.http.Flusher.ty = true⌝ -∗ Rs -∗
        WP (App (App (Val #(methods hi.ty go!"ServeHTTP" hi.v)) (Val #(GoInterface.ok wi)))
          (Val #r)) {{ v, Rs ∗ handlerDone H (GoInterface.ok wi) a R γk v }}))

/-- **A built mux is a handler of `a`** (the mux's dispatch, stated as what its `ServeHTTP` does):
each registered handler handles what is routed to it; a request routed nowhere (or redirected,
for a path not in `ServeMux`'s clean form) gets the mux's own `404`/`301` response, which the
protocol must allow (2026-10-23, rafthttp stage 6c: of those two statuses only, was of any). -/
def mux_handlerOk_spec (H : HttpNet GF) : Prop :=
  ∀ (m : Loc) (regs : List (GoString × GoInterface)) (a : GoString) (Rs : IProp GF),
    ⊢ muxOwn (GF := GF) m regs -∗
      ([∗list] reg ∈ regs, handlerFor H a Rs (regs.map Prod.fst) reg.1 reg.2) -∗
      (□ ∀ (R : HReq) (γk : GName) (w : List w8),
        ⌜route (regs.map Prod.fst) R.path = none⌝ → (H.proto a).req R γk -∗
          (H.proto a).resp R γk (W64 404) w ∗ (H.proto a).resp R γk (W64 301) w) -∗
      ⌜∀ (R : HReq) (loc : GoString), route (regs.map Prod.fst) R.path = none →
        (H.proto a).rhdr R [] ∧ (H.proto a).rhdr R (hdrSet [] go!"Location" loc)⌝ -∗
      handlerOk H a Rs (interface.mkOk (go.GoType.PointerType
        _root_.Perennial.net.http.ServeMux.ty) #m)

/-! ### URLs -/

/-- `p.String()` of a `url.URL` at `p` (`String` has a pointer receiver; 2026-10-23, stage 5e-3,
was stated of the value) with only `Scheme = "http"`, `Host` and `Path` set: `urlOf`. -/
def URLString_spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (u : _root_.Perennial.net.url.URL),
    u.Scheme' = go!"http" → u.Opaque' = "" → u.User' = null → u.Fragment' = "" →
    u.RawQuery' = "" → u.RawPath' = "" → u.RawFragment' = "" → u.ForceQuery' = false →
    u.OmitHost' = false →
    ⊢ {{ (p ↦{dq} u : IProp GF) }}
        (App (Val (p @!! go.GoType.PointerType _root_.Perennial.net.url.URL.ty @!! go!"String"))
          (Val #()))
      {{ RET #(urlOf u.Host' u.Path'); p ↦{dq} u }}

/-- `(&hm).Get(k)` on a request's header map being built (2026-10-24, rafthttp stage 6e:
`checkPostResponse` logs the request's `X-Etcd-Cluster-ID`): the map's `Get`, through the
request's `Header` field. -/
def HeaderGetOwnPtr_spec : Prop :=
  ∀ (p hm : Loc) (hs : List (GoString × GoString)) (k : GoString),
    ⊢ {{ p ↦□ hm ∗ hdrOwn (GF := GF) hm hs }}
        (App (Val (p @!! go.GoType.PointerType _root_.Perennial.net.http.Header.ty @!! go!"Get"))
          (Val #k))
      {{ RET #(hdrGet hs k); hdrOwn hm hs }}

/-- **A request's `URL` field** (2026-10-24, rafthttp stage 6e): `NewRequest` sets it to the
parsed URL and nothing writes it or the URL after (`req.URL.String()`, `checkPostResponse`'s
error message): read-only for good, a fact of the rest of a request (`reqRest`). -/
def reqURL_spec : Prop :=
  ∀ (r : Loc) (R : HReq),
    reqRest (GF := GF) r R ⊢ reqRest r R ∗
      ∃ (up : Loc) (u : _root_.Perennial.net.url.URL), reqF go!"URL" r ↦□ up ∗ up ↦□ u

/-- `http.StatusText(code)` (2026-10-24, rafthttp stage 6e: `checkPostResponse`'s error message):
some string (Go's table lookup, `""` for an unknown code). -/
def StatusText_spec : Prop :=
  ∀ (code : w64),
    ⊢ {{ (True : IProp GF) }}
        (App (Val (@! _root_.Perennial.net.http.StatusText)) (Val #code))
      {{ (s : GoString), RET #s; True }}

/-- **A byte `url.URL.String` writes unescaped in a host** (2026-10-27, D22 J-T, W8): a letter, a
digit, `.`, `-` or `:` (Go's `shouldEscape(c, encodeHost)` is false for each: alphanumerics and the
unreserved `-` `.`, and `:` among the host's allowed sub-delimiters). -/
def hostByteNoEscape (c : w8) : Prop :=
  (48 ≤ c.toNat ∧ c.toNat ≤ 57) ∨ (65 ≤ c.toNat ∧ c.toNat ≤ 90) ∨ (97 ≤ c.toNat ∧ c.toNat ≤ 122) ∨
    c.toNat = 46 ∨ c.toNat = 45 ∨ c.toNat = 58

/-- **A URL of only the scheme `http` and a host** (2026-10-27, D22 J-T, W8): what a member's
configured peer URL is (`http://host:port`, `types.parsedPeerURL`'s fields), the host non-empty and
of bytes `escape` keeps. -/
def urlRootPlain (u : _root_.Perennial.net.url.URL) : Prop :=
  u.Scheme' = go!"http" ∧ u.Opaque' = "" ∧ u.User' = null ∧ u.Fragment' = "" ∧
    u.RawQuery' = "" ∧ u.RawPath' = "" ∧ u.RawFragment' = "" ∧ u.ForceQuery' = false ∧
    u.OmitHost' = false ∧ u.Path' = "" ∧ u.Host' ≠ [] ∧ ∀ c ∈ u.Host', hostByteNoEscape c

/-- `u.String()` of any URL (2026-10-24, rafthttp stage 6e: `setPeerURLsHeader` renders the
transport's peer URLs, whatever they are): some string; it reads the URL only. Go's `URL.String`
assembles its fields with `escape` and never panics. (2026-10-27, D22 J-T, W8: restated, the
string of a URL of only the scheme `http` and a plain host is `http://` and the host: Go writes
the scheme, `:`, `//` (a host is set), `escape(host, encodeHost)` (the host itself, its bytes
unescaped: `hostByteNoEscape`), the escaped path (`""`: `Path` and `RawPath` empty), and no query
or fragment.) -/
def URLStringAny_spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (u : _root_.Perennial.net.url.URL),
    ⊢ {{ (p ↦{dq} u : IProp GF) }}
        (App (Val (p @!! go.GoType.PointerType _root_.Perennial.net.url.URL.ty @!! go!"String"))
          (Val #()))
      {{ (s : GoString), RET #s; p ↦{dq} u ∗ ⌜urlRootPlain u → s = go!"http://" ++ u.Host'⌝ }}

/-! `encoding/binary`'s `Write` and `Read` of an integer (the codecs' length prefixes) are
`Spec/encoding/binary/{WriteUint64,WriteUint8,ReadUint64}.lean`. -/

/-- A request body's reader keeps the prefix contract (`bodyRead_spec`). -/
theorem bodyReader_prefixOk (hR : bodyRead_spec (GF := GF)) (rd : GoInterface) (R : HReq)
    (e : GoInterface) (hrd : rd ≠ GoInterface.nil) :
    ⊢ prefixReaderOk (GF := GF) rd (bodyReader rd R) R.body e := by
  cases rd with
  | nil => exact absurd rfl hrd
  | ok ri =>
    unfold prefixReaderOk
    iexists ri
    isplitr
    · ipureintro; rfl
    iintro !> %r %p %xs %Φ !> ⟨Hs, Hp, #He⟩ HΦ
    iapply (hR _ ri R r p xs e rfl) $$ [$Hs $Hp $He]
    iexact HΦ

/-- A streamed request body's reader keeps the stream contract (`bodyStreamRead_spec`; D42). -/
theorem bodyStream_streamReaderOk (hR : bodyStreamRead_spec (GF := GF)) (rd : GoInterface)
    (Pre Φ : List w8 → Prop) (e : GoInterface) (hrd : rd ≠ GoInterface.nil) :
    ⊢ streamReaderOk (GF := GF) rd (bodyStream rd Pre Φ) Pre Φ e := by
  cases rd with
  | nil => exact absurd rfl hrd
  | ok ri =>
    unfold streamReaderOk
    iexists ri
    isplitr
    · ipureintro; rfl
    iintro !> %r %p %xs %Ψ !> ⟨Hs, Hp, #He⟩ HΨ
    iapply (hR _ ri Pre Φ r p xs e rfl) $$ [$Hs $Hp $He]
    iexact HΨ

end defs

/-! **The representations of `http.Request` and `http.Response`** (rafthttp stage 6f). Their
types are axiomatized (Goose translates `net/http` names-only), so their generated
`IntoValTyped` instances are `sorry -- axiomatized type`; a field access (`req.Header`, a `StructFieldRef` of the
struct type) needs only `TypeRepr`, which instance search would take from those `sorry`s
(`IntoValTyped.type_repr`). These take it from the translation's own type assumptions
(`Request.TypeAssumptions.type_repr`, in `net.http.Assumptions`) instead: no `sorry`, no axiom. -/
section typeRepr
variable [GooseExts] [GoGlobalContext] [GoLocalContext] [GoSemanticsFunctions]
variable [package_sem : _root_.Perennial.net.http.Assumptions]

instance (priority := high) Request_typeRepr :
    TypeRepr _root_.Perennial.net.http.Request.ty _root_.Perennial.net.http.Request :=
  haveI : go.IsUnderlying _root_.Perennial.net.http.Request.ty _root_.Perennial.net.http.Request.underlying :=
    ⟨(go.underlying_unfold (t := _root_.Perennial.net.http.Request.ty)).trans go.is_underlying⟩
  haveI := _root_.Perennial.net.http.Request.TypeAssumptions.type_repr
  go.type_repr_underlying (u := _root_.Perennial.net.http.Request.underlying)

/-- (The struct type itself: what a field reference `StructFieldRef` names.) -/
instance (priority := high) Request_underlying_typeRepr :
    TypeRepr _root_.Perennial.net.http.Request.underlying _root_.Perennial.net.http.Request :=
  haveI := _root_.Perennial.net.http.Request.TypeAssumptions.isUnderlying
  haveI := _root_.Perennial.net.http.Request.TypeAssumptions.type_repr
  go.type_repr_underlying (u := _root_.Perennial.net.http.Request.underlying)

instance (priority := high) Response_typeRepr :
    TypeRepr _root_.Perennial.net.http.Response.ty _root_.Perennial.net.http.Response :=
  haveI : go.IsUnderlying _root_.Perennial.net.http.Response.ty _root_.Perennial.net.http.Response.underlying :=
    ⟨(go.underlying_unfold (t := _root_.Perennial.net.http.Response.ty)).trans go.is_underlying⟩
  haveI := _root_.Perennial.net.http.Response.TypeAssumptions.type_repr
  go.type_repr_underlying (u := _root_.Perennial.net.http.Response.underlying)

/-- (The struct type itself: what a field reference `StructFieldRef` names.) -/
instance (priority := high) Response_underlying_typeRepr :
    TypeRepr _root_.Perennial.net.http.Response.underlying _root_.Perennial.net.http.Response :=
  haveI := _root_.Perennial.net.http.Response.TypeAssumptions.isUnderlying
  haveI := _root_.Perennial.net.http.Response.TypeAssumptions.type_repr
  go.type_repr_underlying (u := _root_.Perennial.net.http.Response.underlying)

end typeRepr

end http
end EtcdGrove
end Perennial
