/-
The vocabulary of net/http's `ServeMux` as net/rpc over HTTP uses it (`notes/library-drivers.md`;
the shared rpc-over-HTTP design, L2, with its amendments agreed with phase 7's S5): the right to
register patterns on a mux, a route it serves, and the contract of an rpc handler. **Interim**: the
specs over it, `Handle.spec` and `Serve.spec_rpc` (`Net/Spec/net/http/{Handle,Serve}.lean`), are
proved by phase 7's S5 over the real `ServeMux` (`MuxServe.lean`: both matchers, chosen by `use121`;
the lock's guard and reader-slot pool; the owner's half of the matcher's state). Until 2026-11-25
`muxOwn` was an invariant on the mux's tree alone, with the patterns and handlers in ghost state.

* `muxOwn m Ps` (exclusive): the right to register on the mux `m`, whose registered patterns are
  `Ps` (the patterns' owner: one goroutine at a time; net/rpc's `HandleHTTP` and the program's own
  `Handle`s, at the boot). From net/http's first initialization at `DefaultServeMux` (`muxOwn (globalAddr defaultServeMux) []`,
  `Net/Proof/net/http/InitFirst.lean`).
* `muxRoute m p h` (persistent): `m` sends a request for the literal path `p` to the handler `h`.
* `litPattern p`: a literal path pattern: `/`-initial, every byte one the model's request parser
  leaves alone in a path (`pathByte`, the model's `modelPathByte`: letters, digits and
  `- _ . ~ $ & + , / : ; = @`). So no method or host (no space or tab: `parsePattern` splits a
  method at either), no wildcard (`{`, `}`), no escape (`%`), no query (`?`): a request for `p` is
  routed to `p` (`/a?b` would route to `/a`), and for such patterns Go 1.22's conflict rule is
  equality, so `p ∉ Ps` is exactly what `register` needs not to panic. (Until 2026-11-24 an
  exclusion list, which admitted a tab and `?`: `notes/axiom-review/net-http-interim.md`.)
* `rpcHjHandler h W a` (persistent): the handler `h` serves net/rpc's `CONNECT` handshake on a
  connection dialed to `a` in the rpc world `W`: given the request's head and the right to hijack the
  connection (`hijackOk`, what net/http's `conn.serve` gives a handler), its `ServeHTTP` returns the
  thread token and the hijack's evidence (net/rpc's `Server.ServeHTTP.spec`).
* `muxRpc m W A p` (persistent): `m` routes `p` to a handler that is `rpcHjHandler` at every address
  `a` with `A a`.
-/
module

public import Net.Proof.net.http.ServerDefs
public import Net.Proof.net.http.RequestDefs
public import Net.Proof.net.rpc.Proto
public import Net.GeneratedProof.net.http
public import Net.Proof.net.http.MuxServe
public import Net.Proof.net.http.ServeLoopDefs
public import Net.Proof.net.http.ServerConn

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

namespace net.http

/-- A literal path pattern (see the file header). -/
def litPattern (p : GoString) : Prop :=
  p.head? = some (W8 47) ∧ ∀ b ∈ p, pathByte b = true

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : net.http.Assumptions]

/-- The right to register on `m`, its patterns `Ps` (exclusive; see the file header): the owner's half
of the state of the matcher `use121` chooses (`muxOwnS`, `MuxServe.lean`). -/
def muxOwn (m : Loc) (Ps : List GoString) : IProp GF := muxOwnS (GF := GF) (hG := hG) m Ps

/-- `m` routes `p` to `h` (persistent): `muxRouteS`, `MuxServe.lean`. -/
def muxRoute (m : Loc) (p : GoString) (h : GoInterface) : IProp GF := muxRouteS (GF := GF) (hG := hG) m p h

instance muxRoute_persistent (m : Loc) (p : GoString) (h : GoInterface) :
    Persistent (muxRoute (GF := GF) (hG := hG) m p h) := by
  unfold muxRoute; infer_instance

/-- What net/http's server reads of the package variables: `httpEnv` (its package fact), `readEnv`
(io's and internal/poll's errors, from net/http's `isPkgInit`), and what net/http's first
initialization leaves (`InitFirst.lean`): `serveEnv`, `ctxKeys`, `aLongTimeAgo`'s value, the reader and
writer pools. (Until 2026-11-25 `httpEnv` alone.) -/
def httpSrvEnv : IProp GF :=
  iprop(httpEnv ∗ readEnv ∗ serveEnv ∗ ctxKeys ∗ (∃ tm : time.Time, globalAddr net.http.aLongTimeAgo ↦□ tm) ∗
    wPools ∗ rPool)

instance httpSrvEnv_persistent : Persistent (httpSrvEnv (GF := GF)) := by
  unfold httpSrvEnv; infer_instance

variable [π : NetProtoGS]

/-- The rpc handler contract at `a` in `W` (persistent; see the file header). -/
def rpcHjHandler (h : GoInterface) (W : net.rpc.RpcWorld GF) (a : GoString) : IProp GF :=
  iprop(⌜W.hs a ≠ [] ∧ W.hsAns a = net.rpc.connectAns⌝ ∗
    ∃ e : GoInterfaceOk, ⌜h = interface.ok e⌝ ∗
    □ ∀ (cn : Nat) (rp req : Loc) (D : IProp GF) (Φ : val → IProp GF),
      (reqHead req go!"CONNECT" ∗
        hijackOk rp cn a (net.rpc.reqProto (Gg := hG.goose_globalGS) W a)
          (net.rpc.respProto (Gg := hG.goose_globalGS) W a) (W.hs a) D ∗ threadTok) -∗
      ▷ (threadTok ∗ D -∗ Φ #()) -∗
      WP (App (App (Val #(methods e.ty go!"ServeHTTP" e.v))
        (Val #(interface.mkOk (go.GoType.PointerType net.http.response.ty) #rp))) (Val #req))
        {{ Φ }})

instance rpcHjHandler_persistent (h : GoInterface) (W : net.rpc.RpcWorld GF) (a : GoString) :
    Persistent (rpcHjHandler (GF := GF) h W a) := by
  unfold rpcHjHandler; infer_instance

/-- `m` routes `p` to an rpc handler at every address with `A` (persistent). -/
def muxRpc (m : Loc) (W : net.rpc.RpcWorld GF) (A : GoString → Prop) (p : GoString) : IProp GF :=
  iprop(∃ h : GoInterface, muxRoute m p h ∗ □ ∀ a, ⌜A a⌝ → rpcHjHandler h W a)

instance muxRpc_persistent (m : Loc) (W : net.rpc.RpcWorld GF) (A : GoString → Prop)
    (p : GoString) : Persistent (muxRpc (GF := GF) m W A p) := by
  unfold muxRpc; infer_instance

end defs

end net.http
end Perennial
