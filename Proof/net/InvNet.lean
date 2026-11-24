/-
**The network's addresses, for a server's listener** (item 4, the server start; Lean-first, no
Rocq counterpart). Since the net swap (etcd-dist D2, 2026-11-22, `notes/etcd-dist-plan.md` §9, "D2's `net`
half"; design D, the user's decision) `net` is the part `Net/`'s translation over the net extension
`netExt` (`GooseLang/Ext/Net`), and these are definitions over its ghost state, with one axiomatized
token left:

* `addrClaim addr` (exclusive, axiomatized): the program's closed-world claim on `addr`'s requests: the
  program's own connections to `addr` carry requests of its verified or trust-boundary clients (until
  2026-11-22 part (b) of `addrsUnclaimed`, `Proof/runtime/Start.lean`, which program start turned into
  `netAddrFree`). The grpc and net/http transport axioms (`grpc.start`, `http.register`) rest on it
  until phase 7 (S2, S5) proves the transport over the net extension. Program start
  (`goose_adequacy_start`, `Proof/runtime/Start.lean`) hands it out for the addresses `As` of a
  single-process closed theorem (removed at the net swap, restored 2026-11-23,
  `notes/single-process-restore.md`); nothing else produces it; `etcd_safe`'s deployment premise is to
  give it. The same for `httpProtoFree` below (whose docstring predates the restoration: program start
  gives it again, with `addrClaim`, for the addresses `As`). Consumed by `net.Listen` (into `netListenerAt`),
  so at most one `netListenerAt` of an address exists in a run, and what consumes it (`grpc.start`, `http.register`)
  happens once per address (`grpcAddrIs_agree`). The address itself may be listened on again: after a listener's
  `Close`, `listen_au` (from the address's persistent `addrProto`) gives a second raw listener, without the claim.
* `netAddrFree addr` := `addrClaim addr ∗ addrUnset addr`: the claim, and the address unset in the net
  extension's ghost state (`addrUnset`: its pending set, empty, `addr` a valid address, `addrOk`,
  `GooseLang/Ext/Net/Impl.lean`, and the right to listen at it, `netLisTok`, all from its start
  resources; since phase 7 S2's interface, 2026-11-24, until then the listening token and validity).
* `netAddrLeft addr`: what `Listen` leaves of `addrUnset` (the pending set, the validity, the listening
  token in an invariant): what sets the address's protocols afterwards (`grpc.start'`).
* `netListenerAt l addr` := the claim and `netListenerOpen l addr`: `l` is a `*TCPListener` whose struct
  names an extension listener (`lisAt`, as Net's `isListener`; since 2026-11-24) and that listener is open at
  `addr` (`netLis`, `netLisAt`): what Net's `Listen` returns (`Net/Spec/net/Listen.lean`).
-/
module

public import Perennial.Proof.ProofPrelude
public import Net.Proof.net.Base
public import GooseLang.Ext.Net.Proto

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Net

/-- **The program's closed-world claim on the address `addr`** (exclusive; see the file header). -/
axiom addrClaim {GF : BundledGFunctors} [GooseExts] (addr : GoString) : IProp GF

/-- **The right to fix the HTTP protocol of the address `addr`** (exclusive; D39a, 2026-10-23,
rafthttp stage 6a): `http.reserve` (`Proof/net/http/Axioms.lean`) consumes it, fixing the address's
protocol before its listener exists (a raft member sends to its peers before they listen). Purely ghost:
no Go operation consumes or needs it. Program start gives it once per address of `As`, with `addrClaim`
(`goose_adequacy_start`'s `startRights`, `Proof/runtime/Start.lean`; removed at the net swap, 2026-11-22, restored
2026-11-23); nothing else produces it. -/
axiom httpProtoFree {GF : BundledGFunctors} [GooseExts] (addr : GoString) : IProp GF

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The right to listen at `addr`, with the claim on its requests** (see the file header). The
program has the net extension (`HasExt netExt`, a proposition: inside the predicate, so that its users
need no instance of it). Since phase 7 S2's interface (2026-11-24) the address unset (`addrUnset`: its
pending set, empty, its validity and its listening token), so that `Listen` can leave what sets its
protocols (`netAddrLeft`); until then only the listening token and the validity. -/
def netAddrFree (addr : GoString) : IProp GF :=
  iprop(addrClaim addr ∗ ∃ _ : HasExt netExt, addrUnset (Gg := hG.goose_globalGS) addr)

/-- **What sets `addr`'s protocols, left by `Listen`** (exclusive; phase 7 S2's interface): its pending
set, empty, its validity, and its listening token in an invariant (`lisTokInv`; the net extension's
`Listen` takes the token at its step and gives it back, so `Listen`'s proof keeps it there):
`addr_set_proto_tok`'s premises, what the single-process start (`grpc.start'`) sets a served
address's table with. -/
def netAddrLeft (addr : GoString) : IProp GF :=
  iprop(∃ _ : HasExt netExt, netPend (NG (Gg := hG.goose_globalGS)) addr ∅ ∗
    addrTok (GF := GF) addr ∗ lisTokInv (Gg := hG.goose_globalGS) addr)

/-- **The listener `l` is open at `addr`, unused** (no claim; split from `netListenerAt` at phase 7
S2's interface: what a member that its deployment's start set the address of holds, beside a server
being built, `grpcServeTok`): `l` is the `*TCPListener` `t` whose struct names the extension's listener
`lv` (`lisAt t lv x`, persistent, as Net's `isListener`), and `lv` is open at `addr` (`netLis`, `netLisAt`).

(2026-11-24) The tie `lisAt t lv x` is what makes `l` the listener at `addr`: without it the facts of the
listener at one address could be packed around the Go value of a listener at another, and the trust-boundary
axioms over `netListenerAt l a` (`http.register`, `grpc.start`, `bridge.New`) served the wrong socket (a raw
listener at an unreserved `b` registered as the HTTP listener of `a`: `examples/axiomcx/httpregfwd/`,
`notes/axiom-review/http-reserve-addrproto.md`). `net.Listen`'s proofs keep it from Net's `isListener`. -/
def netListenerOpen (l : GoInterface) (addr : GoString) : IProp GF :=
  iprop(∃ (_ : HasExt netExt) (t : Loc) (lv : w64) (x : GoInterface),
    ⌜l = interface.mkOk (go.GoType.PointerType net.TCPListener.ty) #t⌝ ∗
    _root_.Perennial.net.lisAt (hG := hG) t lv x ∗
    netLis (extLocalGS netExt (L := hG.goose_localGS)) lv addr true ∗
    netLisAt (extLocalGS netExt (L := hG.goose_localGS)) lv addr)

/-- **The listener `l` is open at `addr`, unused, with the claim on its requests** (see the file
header). -/
def netListenerAt (l : GoInterface) (addr : GoString) : IProp GF :=
  iprop(addrClaim addr ∗ netListenerOpen l addr)

end defs

/-! ### Numeric address literals (sweep repairs 1, W5) -/

/-- The pieces of `s` between the bytes `c` (`strings.Split`'s, at one byte). -/
def bytesSplit (c : w8) : List w8 → List (List w8)
  | [] => [[]]
  | b :: bs =>
    match bytesSplit c bs with
    | [] => [[b]]
    | p :: ps => if b = c then [] :: p :: ps else (b :: p) :: ps

/-- A decimal numeral without leading zeros (`"0"` itself allowed), its value. -/
def decNumeral? (s : List w8) : Option Nat :=
  if s = [] ∨ (2 ≤ s.length ∧ s.head? = some (W8 48)) then none else
  s.foldl (fun acc c => acc.bind fun n =>
    if 48 ≤ c.toNat ∧ c.toNat ≤ 57 then some (10 * n + (c.toNat - 48)) else none) (some 0)

/-- **`a` is a canonical numeric IPv4 loopback address literal `127.d.d.d:p`** (decidable; sweep
repairs 1, W5, 2026-11-07): four octets `0..255`, the first `127`, and a port `1..65535`, each
decimal without leading zeros (until 2026-11-14 any first octet but the wildcard `0.0.0.0`).
(http-boundary-fix, 2026-11-14, etcd-grove-81's decision) Loopback only: Go's `http.Transport`
with `ProxyFromEnvironment` (rafthttp's round trippers) sends a request to a non-loopback host
through the proxy `HTTP_PROXY` names, whose own answers (`502`, `407`) no protocol admits; a
loopback host is never proxied (go1.27.3 `vendor/golang.org/x/net/http/httpproxy/proxy.go:178-185`,
`useProxy`; `examples/premisefix/httpproxy`). So it has no host name (`localhost` resolves through the
hosts file or DNS, `Listen` binds the first IPv4 address, and a dial tries them in RFC 6724 order:
`notes/axiom-review/alias-tokens.md`), no empty or wildcard host (a dual-stack bind overlapping
every address), no IPv6 and so no IPv4-mapped form, and no port `0` (`Listen` would pick a port).
Distinct such strings name distinct sockets, and Go dials a literal without resolution, so a dial
of `a` reaches only a listener bound at `a`. Program start gives `netAddrFree` and `httpProtoFree`
only for such literals (`goose_adequacy_start`'s `hAsLit`). -/
def netAddrLit (a : List w8) : Bool :=
  match bytesSplit (W8 58) a with
  | [host, port] =>
    match bytesSplit (W8 46) host with
    | [o₁, o₂, o₃, o₄] =>
      let os := [o₁, o₂, o₃, o₄].map decNumeral?
      os.all (fun o => o.any (· ≤ 255)) && decNumeral? o₁ == some 127 &&
        (decNumeral? port).any (fun p => 1 ≤ p && p ≤ 65535)
    | _ => false
  | _ => false

example : netAddrLit (go!"127.0.0.1:23790" : List w8) = true := by decide
example : netAddrLit (go!"localhost:24290" : List w8) = false := by decide
example : netAddrLit (go!"0.0.0.0:2379" : List w8) = false := by decide
example : netAddrLit (go!"127.0.0.1:024290" : List w8) = false := by decide
example : netAddrLit (go!"127.1.2.3:2380" : List w8) = true := by decide
example : netAddrLit (go!"10.0.0.1:2380" : List w8) = false := by decide

end EtcdGrove
end Perennial
