/-
`server.readRequestHeader(codec)` (`server.go`), by the request loop of a connection served at `a`
(the model's server codec `sc` of the acceptor's end of `cn`, the reader's resources `rdrOwn`), on
a server whose registrations serve `a` (`srvServes`). It reads a request header; then:

* the read failed (or the end's reading was already dead, `rdrOwn`: then nothing is read):
  `keepReading` is `false` with an error (the reader stops);
* otherwise the header is request `k`'s (`r`, the connection's `k`-th, written by a client; its
  sequence number `k`), and the reader takes it (`rdrMid`): the right to answer it once
  (`ansPend`), and its deposit `S m r.body Φ` for its method `m` of a service registered with spec
  `S`, which accepts error answers (`errOk S`); with `keepReading` `true` and `req` holding the
  header, either `nil` and the registered service `svc` and method `mtype` (`methodTypeIs`, its
  receiver `svc`'s), or an error (with one of the server's own messages, `errSrv`: the method is
  not registered) and the deposit spent on the continuation's error answers (`errCont`).

Proved in `Net/Proof/net/rpc/Server__readRequestHeader.lean`.
-/
module

public import Net.Proof.net.rpc.ServerDefs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace net.rpc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS]

/-- See the file header. -/
abbrev Server.readRequestHeader.spec : Prop :=
  ∀ (s : Loc) (γs : GName) (C : CodecSpec GF) (W : RpcWorld GF) (a : GoString) (sc t : Loc)
    (cn : Nat) (la ra : GoInterface),
  {{ isServer s γs ∗ srvServes γs C W a ∗ srvEnv ∗ srvCodecAt sc t cn a la ra ∗
      rdrOwn W a cn }}
    (App (Val (s @!! go.GoType.PointerType net.rpc.Server.ty @!! go!"readRequestHeader"))
      (Val #(interface.mkOk (go.GoType.PointerType net.rpc.serverCodec.ty) #sc)))
  {{ (svc mt req : Loc) (keep : Bool) (err : GoInterface),
      RET (PairV (PairV (PairV (PairV #svc #mt) #req) #keep) #err);
      ⌜keep = false ∧ err ≠ interface.nil⌝ ∨
      (⌜keep = true⌝ ∗ ∃ (k : Nat) (r : RpcReq) (Φ : List w8 → GoString → IProp GF),
        req ↦ { (_root_.Perennial.zero_val net.rpc.Request) with ServiceMethod' := r.sm, Seq' := W64 k } ∗
        rdrMid W a cn k r ∗
        ansPend W a cn k r.sm Φ ∗
        ((⌜err = interface.nil⌝ ∗ ∃ (S : MethodSpec GF) (m : GoString) (rcvr : GoInterface),
            S m r.body Φ ∗ errOk S ∗ structFieldRef net.rpc.service go!"rcvr" svc ↦□ rcvr ∗
            methodTypeIs C rcvr (S m) mt) ∨
          (⌜err ≠ interface.nil⌝ ∗ errSrv err ∗ errCont Φ))) }}

end spec

end net.rpc
end Perennial
