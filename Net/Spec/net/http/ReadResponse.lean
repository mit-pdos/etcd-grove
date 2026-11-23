/-
`http.ReadResponse(b, req)` on a `CONNECT` answer (net/rpc's `DialHTTPPath`, the one caller here):
`b` a `*bufio.Reader` (`bufio.ownReader`, nothing delivered yet) of a stream reader `ri`
(`io.readerStream ri S E`) whose bytes are, as long as it is read, a prefix of net/rpc's answer
`connectAns` (`"HTTP/1.0 200 Connected to Go RPC\n\n"`) and that delivers nothing after an error
(the law over `E` and `S`: after an error at `r`, the stream stays at `r`; the model's
`connectReader`), `req` the request `{Method: "CONNECT"}`. It returns an error (some error, non-nil:
the stream's, `io.ErrUnexpectedEOF`, a malformed line's), or a response whose `Status` is either not
`"200 Connected to Go RPC"` or is it, and then the reader has delivered exactly `connectAns` (the
status line and the empty header block, each up to its `"\n"`: a line cut by an error does not
parse as a whole one, since nothing follows the error). The model's head parser
(`textproto_model.go`) and `readTransfer` (the answer's body, read to the connection's end, is not
read here). `httpEnv` is the package state the parse reads.
Not proved yet: `ReadResponse` calls `readTransfer`, which the translation (`Net/Code/net/http.toml`)
does not translate yet, and `*bufio.Reader`'s `ReadByte` and `Peek` (and `fill`) have no spec yet
(`notes/dsverify-net-port-plan.md`, phase 5 item 2).
-/
module

public import Net.GeneratedProof.net.http
public import Net.Proof.net.rpc.Proto
public import Proof.bufio.Defs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace net.http

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.bufio.Assumptions]

/-- The package state `ReadResponse` (and `DialHTTPPath`'s reader) reads: `bufio`'s and `io`'s
initialization. net/http's own variables the parse reads (`NoBody`, ...) are to be added as its
proof finds them, as `cliEnv` lists net/rpc's (net/http has no package initialization proof:
`notes/dsverify-net-port-plan.md`, phase 5 item 2, 5). -/
def httpEnv : IProp GF :=
  iprop(isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io)

instance httpEnv_persistent : Persistent (httpEnv (GF := GF)) := by
  unfold httpEnv; infer_instance

/-- See the file header. -/
abbrev ReadResponse.spec : Prop :=
  ∀ (b : Loc) (ri : GoInterfaceOk) (S : List w8 → IProp GF) (E : List w8 → GoInterface → IProp GF)
    (req : Loc) (rq : net.http.Request),
  {{ httpEnv ∗ EtcdGrove.io.readerStream ri S E ∗ EtcdGrove.bufio.ownReader b ri S E [] ∗
      (□ ∀ r, S r -∗ ⌜r <+: net.rpc.connectAns⌝) ∗
      (□ ∀ (r r' : List w8) (err : GoInterface), E r err -∗ S r' -∗ ⌜r <+: r' → r' = r⌝) ∗
      req ↦ rq ∗ ⌜rq.Method' = go!"CONNECT"⌝ }}
    (App (App (Val (@! net.http.ReadResponse)) (Val #b)) (Val #req))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (⌜err ≠ interface.nil⌝) ∨
      (⌜err = interface.nil⌝ ∗ ∃ rv : net.http.Response, resp ↦ rv ∗
        (⌜rv.Status' ≠ net.rpc.connectedStatus⌝ ∨
          ⌜rv.Status' = net.rpc.connectedStatus⌝ ∗
            EtcdGrove.bufio.ownReader b ri S E net.rpc.connectAns)) }}

end spec

end net.http
end Perennial
