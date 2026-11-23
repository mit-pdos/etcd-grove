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
  so an address is listened on at most once in a run (`grpcAddrIs_agree`).
* `netAddrFree addr` := `addrClaim addr ∗ netLisTok addr ∗ ⌜addrOk addr⌝`: the claim, the net
  extension's right to listen at `addr` (`netLisTok`, from its start resources) and `addr` a valid
  address (`addrOk`, `GooseLang/Ext/Net/Impl.lean`).
* `netListenerAt l addr` := the claim and the extension's open listener at `addr` (`netLis`, `netLisAt`),
  `l` a `*TCPListener` (what Net's `Listen` returns, `Net/Spec/net/Listen.lean`).
-/
module

public import Perennial.Proof.ProofPrelude
public import Net.Proof.net.Base

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
no Go operation consumes or needs it. Until the net swap (2026-11-22) program start gave it once per
address, with `netAddrFree`; now nothing does (net/http's S5, or `etcd_safe`'s deployment, is to). -/
axiom httpProtoFree {GF : BundledGFunctors} [GooseExts] (addr : GoString) : IProp GF

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

/-- **The right to listen at `addr`, with the claim on its requests** (see the file header). The
program has the net extension (`HasExt netExt`, a proposition: inside the predicate, so that its users
need no instance of it). -/
def netAddrFree (addr : GoString) : IProp GF :=
  iprop(addrClaim addr ∗ ∃ _ : HasExt netExt,
    netLisTok (extGlobalGS netExt (G := hG.goose_globalGS)) addr ∗ ⌜addrOk addr = true⌝)

/-- **The listener `l` is open at `addr`, unused, with the claim on its requests** (see the file
header). -/
def netListenerAt (l : GoInterface) (addr : GoString) : IProp GF :=
  iprop(addrClaim addr ∗ ∃ (_ : HasExt netExt) (t : Loc) (lv : w64),
    ⌜l = interface.mkOk (go.GoType.PointerType net.TCPListener.ty) #t⌝ ∗
    netLis (extLocalGS netExt (L := hG.goose_localGS)) lv addr true ∗
    netLisAt (extLocalGS netExt (L := hG.goose_localGS)) lv addr)

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
