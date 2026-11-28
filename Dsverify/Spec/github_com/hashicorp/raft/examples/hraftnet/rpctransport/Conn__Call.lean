/-
`rpctransport.Conn.Call`'s spec (the hraft kit's transport, notes/dsv-hraft.md, S4).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.rpctransport.Conn

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.rpctransport.Assumptions]
variable [π : Net.NetProtoGS] [net.rpc.Assumptions] [net.Assumptions]

open github_com.hashicorp.raft.examples.hraftnet.rpctransport

/-- `p.Call(sm, args, reply, d)`: `c.Go` of the call on the connection's client (dialed if needed) into `reply`, waiting at most `d` for it (net/rpc's `Client.Call.spec`, with a timeout): `CallOK` (0) after one run of the method at the server, the reply decoded (`Θ rep true`); `CallNotSent` (1) with nothing sent (the deposit `R`, which the encoding premise is made from, and `D`
back: a client retries elsewhere with the same deposit); `CallFailed` (2) otherwise (the reply may still be written: the caller gives it up). -/
abbrev github_com.hashicorp.raft.examples.hraftnet.rpctransport.Conn.Call.spec : Prop :=
  ∀ (p : Loc) (W : net.rpc.RpcWorld GF) (a sm svc M : GoString) (S : net.rpc.MethodSpec GF)
    (args reply : GoInterface) (Φm : List w8 → GoString → IProp GF) (Rargs D : IProp GF)
    (Θ : List w8 → Bool → IProp GF) (C : net.rpc.CodecSpec GF) (d : w64) (R : IProp GF),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.rpctransport ∗
        isConn p W a ∗ ⌜net.rpc.splitSM sm = some (svc, M) ∧ W.SS a svc = some S ∧ reply ≠ interface.nil⌝ ∗
        ⌜sm.length + 16 ≤ net.rpc.maxFrameN⌝ ∗ net.rpc.codecSet C ∗
        R ∗ (R -∗ C.enc args (fun bs => iprop(⌜bs.length ≤ net.rpc.maxFrameN⌝ ∗ S M bs Φm ∗ Rargs))) ∗
        D ∗ □ (D -∗ ∀ rep, Φm rep [] -∗ C.dec rep reply (Θ rep)) }}
      (App (App (App (App (Val (p @!! go.GoType.PointerType Conn.ty @!! go!"Call")) (Val #sm)) (Val #args))
        (Val #reply)) (Val #d))
    {{ (r : w64), RET #r; (⌜r = W64 0⌝ ∗ Rargs ∗ ∃ rep, Θ rep true) ∨
        (⌜r = W64 1⌝ ∗ R ∗ D) ∨
        ⌜r = W64 2⌝ }}

end spec

end Perennial
