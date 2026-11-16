/-
`(*raftSwap).ServeHTTP(w, r)` and `(*raftSwap).set(h)` (`examples/etcd/restartN/restartN.go`; restart3
C3, 2026-11-15, D-R3-4): a member's peer handler, which forwards each request to the current
incarnation's raft handler, and its swap at the restart. Lean-first (no Rocq counterpart). No trusted
text: the ghost state is `Swap.lean`'s.

**`ServeHTTP.spec`** (the form of `http.handlerOk`'s invocation, as rafthttp's handlers'): of a member's
peer handler (`swapOk`, at its peer address `a`), a request that `http.Serve` delivers to `a` (its
ticket, body and fresh writer, as `http.handlerOk` lends them) and a slot token (`swTok`, the resource
`http.Serve` lends each invocation): it returns, or panics as the incarnation's handler does, with the
slot token back and the writer given back (`http.handlerDone`). On the way it locks `sw.mu`, reads
the current incarnation's handler, trades the token for a copy of that incarnation's resource, unlocks,
and calls the handler, which may run after a later `set` (the stopped incarnation's run, Scope §2.2
(i)-(ii)): its copy is its own, and the slot token comes back whichever incarnation is current then.

**`set.spec`:** of a member's peer handler, a handler `h` of its peer address lending `srvServeRes γn τ`
(the new incarnation's `RaftHandler()`) and `httpProcSlots` copies of that resource (the new
incarnation's `memberPeerServeRes … false`): `h` becomes the current incarnation's.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restartN.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_restartN

open Iris Iris.BI go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver
open etcd_restart

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.restartN.Assumptions]

/-- See the file header. -/
abbrev raftSwap.ServeHTTP.spec : Prop :=
  ∀ (sw : Loc) (γS : SwNames) (γn : NetNames GF) (a : GoString) (wi : GoInterfaceOk)
    (r : Loc) (R : http.HReq) (γk : GName) (rd : GoInterface),
  ⊢ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.restartN -∗
    swapOk sw γS γn a -∗
    http.reqAt r R rd -∗ ⌜R.host = a⌝ -∗ □ ((raftHttpNet (netRh γn)).proto a).req R γk -∗
    http.reqTicketOnce R γk -∗ http.reqBody (raftHttpNet (netRh γn)) a R γk rd -∗
    http.respWriter (raftHttpNet (netRh γn)) (GoInterface.ok wi) a R γk none [] -∗
    http.respHdrs (GoInterface.ok wi) [] -∗
    ⌜go.typeSetContains wi.ty _root_.Perennial.net.http.Flusher.ty = true⌝ -∗ swTok γS -∗
    WP (App (App (Val (sw @!! go.GoType.PointerType
        github_com.mit_pdos.etcd_grove.examples.etcd.restartN.raftSwap.ty @!! go!"ServeHTTP"))
      (Val #(GoInterface.ok wi))) (Val #r))
      {{ v, swTok γS ∗ http.handlerDone (raftHttpNet (netRh γn)) (GoInterface.ok wi) a R γk v }}

/-- See the file header (`set`). -/
abbrev raftSwap.set.spec : Prop :=
  ∀ (sw : Loc) (γS : SwNames) (γn : NetNames GF) (a : GoString) (h : GoInterface)
    (τ : SrvTr GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.restartN ∗
      swapOk sw γS γn a ∗ http.handlerOk (raftHttpNet (netRh γn)) a (srvServeRes γn τ) h ∗
      [∗list] _x ∈ List.replicate http.httpProcSlots (), srvServeRes γn τ }}
    (App (Val (sw @!! go.GoType.PointerType
        github_com.mit_pdos.etcd_grove.examples.etcd.restartN.raftSwap.ty @!! go!"set")) (Val #h))
  {{ RET #(); True }}

end spec

end etcd_restartN
end EtcdGrove
end Perennial
