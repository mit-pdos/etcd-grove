/-
**Serving a member's raft handler** (D21 stage M5, 2026-10-19; the user's (A), `notes/decisions.md`,
"D21 M5"; restated over rafthttp's proved transport in rafthttp stage 6d, 2026-10-24). Lean-first
(no Rocq counterpart).
* `srvNetMember γn s id τ` (persistent): the server `s` is member `id` of the network `γn`:
  what its inbound path reads (`srvProcOk`, its member id among it) and its raft wrapper's
  transport `τ.t` with the names `τ.c` (`SrvTr`), of member `id`, started (`trState`; D22 J-T,
  2026-10-27: until then frozen, `trFrozen`, with no remote) and every other member among the ids
  its pool budgets (what `Handler` needs, D40, W8). `NewServer` gives it. (Until J8a-7,
  2026-11-01, also opened, `trOpened`: a handler may add a remote.)
* `srvTrTok γn τ`: one of the transport's lock's reader tokens (`trTok`), what `CutPeer` and
  `MendPeer` borrow (until J8a-7, 2026-11-01, also the no-remote token of every other member,
  `trNoRem`, D22 J-T: the fork's remotes now pause by a flag);
  `srvServeRes γn τ`: what each request the transport's handler serves
  borrows, a reader's token and an `R` (`Handler`, `http.Serve_spec`'s `httpProcSlots` copies).
(Until stage 6d, `raftHandlerOf γn id h`, opaque: a handler of the transport holding `id`'s slot,
which only `EtcdServer.RaftHandler`'s axiom gave and `net/http.Serve`'s axiom took.)
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvNet

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The server's transport** (stage 6d): the `*rafthttp.Transport` `t` and its names `c`. -/
structure SrvTr (GF : BundledGFunctors) where
  t : Loc
  c : TrN GF

/-- **The server `s` is member `id` of the network `γn`** (persistent; see the file header). -/
def srvNetMember (γn : NetNames GF) (s : Loc) (id : w64) (τ : SrvTr GF) : IProp GF :=
  iprop((∃ γd, srvProcOk γn s id γd) ∗ rnTransportAddr (srvRAddr s) ↦□ transportIface τ.t ∗ ⌜τ.c.lid = id⌝ ∗
    trState γn τ.t τ.c ∗
    ⌜∀ f, (netRh γn).member f → f ≠ id → f ∈ τ.c.L⌝)

instance srvNetMember_persistent (γn : NetNames GF) (s : Loc) (id : w64) (τ : SrvTr GF) :
    Persistent (srvNetMember (GF := GF) γn s id τ) := by
  unfold srvNetMember; infer_instance

/-- **The server's transport's peer control** (see the file header): one of the transport's lock's
reader tokens. -/
def srvTrTok (γn : NetNames GF) (τ : SrvTr GF) : IProp GF := trTok γn τ.t τ.c

/-- **What each request the server's raft handler serves borrows** (see the file header). -/
def srvServeRes (γn : NetNames GF) (τ : SrvTr GF) : IProp GF := iprop(τ.c.R ∗ trTok γn τ.t τ.c)

end defs

end EtcdGrove
end Perennial
