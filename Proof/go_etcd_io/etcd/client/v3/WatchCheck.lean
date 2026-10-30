/-
**A watch's check, as the client sees it** (G2, 2026-10-30; `notes/g2-watch-auth.md`): the
server's authorization of a watch's create (`v3rpc.watchAuthed`), seen through the gRPC stream the
watch joined. The watcher shares one stream among the watches whose contexts have the same stream
key (`streamKeyFromCtx`, `streamKeyOf`), so the stream's metadata is that of some context of the same
key as the watch's, not necessarily the watch's own; and each reconnection is a new gRPC stream, with
its own metadata (`getToken` re-runs). `watcher.Watch.spec`'s row for a response with events is
`watchCheckOk`; `watchCheckOk_tok` is what a client proof uses of it, with the connection's token
fact (`attemptTokOk`), which `watcher_of_clientTokAt` gives for the watcher of a client `New` built
(F-W3). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvWatch
public import Proof.go_etcd_io.etcd.client.v3.InvClientAuth
public import Proof.go_etcd_io.etcd.client.v3.StreamKey
public import Proof.go_etcd_io.etcd.client.v3.InvClientNewResult

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace client

open Iris Iris.BI Iris.ProofMode

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **A watch's check, as the client sees it** (persistent): the gRPC stream the watch's create
went on was opened with outgoing metadata `m` of the same stream key as the watch's context `ctx`;
an attempt of it on the connection `conn` delivered `md` (`clientAttemptMdOf`); and the server
`s`'s check of a create of the key `key` and the range end `rangeEnd` passed for `md`'s token at
the bound `n` (`v3rpc.watchAuthed`, over the store's names `γ`). -/
def watchCheckOk (γ : mvcc.WsNames) (s conn : Loc) (ctx : GoInterface) (n : Nat)
    (key rangeEnd : GoString) : IProp GF :=
  iprop(∃ (m md : GrpcMd),
    ⌜streamKeyOf m = streamKeyOf (metadata.outgoingOf ctx) ∧ clientAttemptMdOf conn m md⌝ ∗
    v3rpc.watchAuthed γ s (auth.mdTokenOf md) n key rangeEnd)

instance watchCheckOk_persistent (γ : mvcc.WsNames) (s conn : Loc) (ctx : GoInterface) (n : Nat)
    (key rangeEnd : GoString) : Persistent (watchCheckOk (GF := GF) γ s conn ctx n key rangeEnd) := by
  unfold watchCheckOk; infer_instance

/-- **A watch's check, with the connection's token fact**: the stream's metadata `m` has the
watch's stream key, its token is one meeting `P` or `m`'s own, and the check passed for an auth
info bound to it (with auth on) at a state no older than `n`. -/
theorem watchCheckOk_tok (γ : mvcc.WsNames) (s conn : Loc) (ctx : GoInterface) (n : Nat)
    (key rangeEnd : GoString) (P : GoString → IProp GF) :
    watchCheckOk (GF := GF) γ s conn ctx n key rangeEnd ∗ attemptTokOk conn P ⊢
      ∃ (m : GrpcMd) (tok : Option GoString) (M : auth.AuthMode)
        (info : go_etcd_io.etcd.server.v3.auth.AuthInfo),
        ⌜streamKeyOf m = streamKeyOf (metadata.outgoingOf ctx)⌝ ∗
        ((∃ t, ⌜tok = some (strings.trimPrefix t go!"Bearer ")⌝ ∗ □ P t) ∨
          ⌜tok = auth.mdTokenOf (metadata.mdNorm m)⌝) ∗
        auth.modeTag γ.tag M ∗ apply.watchClassFrom M n info key rangeEnd ∗
        □ (⌜M.isOn = true⌝ → v3rpc.infoBoundT s M tok info) := by
  iintro ⟨#Hc, #Ht⟩
  unfold watchCheckOk
  icases Hc with ⟨%m, %md, %hka, #Ha⟩
  obtain ⟨hk, ha⟩ := hka
  unfold attemptTokOk
  ihave #Htk := Ht $$ %m %md %ha
  unfold v3rpc.watchAuthed
  icases Ha with ⟨%M, %info, #Htag, #Hcl, #Hb, -⟩
  iexists m, auth.mdTokenOf md, M, info
  iframe Htag Hcl Hb Htk
  ipureintro; exact hk

/-- **The client's watcher, with its connection's token fact** (G2's F-W3, 2026-10-30;
`isNewClient_watcher` with `clientTokAt`): `New`'s client at one server has a `Watcher` field that
is a `*watcher` over the connection with the server's facts, and that connection is the one
`clientTokAt` names, so its attempts carry a token meeting `P` or the context's own
(`attemptTokOk`, what `watchCheckOk_tok` takes). -/
theorem watcher_of_clientTokAt [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    [_root_.Perennial.errors.Assumptions] [_root_.Perennial.fmt.Assumptions]
    [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]
    [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)] [ContextErrsClient (GF := GF) (hG := hG)]
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    (hAs : errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty)
    (cl : Loc) (eps : List GoString) (V : WEnv GF) (P : GoString → IProp GF)
    (hV : eps = [V.addr]) (hm : V.mem = fun _ => (V.addr, V.R)) (hn : V.nm = 1) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      isPkgInit (PROP := IProp GF) pkg_id.context ∗
      isNewClient cl eps V ∗ watchAddrFacts V ∗ clientTokAt cl eps P ⊢
      ∃ (w conn wc lg : Loc) (ics : List GoFunc),
        clientF cl go!"Watcher" ↦□ GoInterface.ok (watcherIfaceOf w) ∗
        isClientWatcher { V with conn := conn, ics := ics, wc := wc, lg := lg } w ∗
        attemptTokOk conn P := by
  iintro ⟨#P1, #P2, #P3, #Hn, #Hf, #Ht⟩
  ihave ⟨%w, %conn, %wc, %lg, %ics, #Hw, #Hcw⟩ :=
    isNewClient_watcher wp_ErrAny hAs cl eps V hV hm hn $$ [P1 P2 P3 Hn Hf]
  · iframe #
  ihave #Hc := watcherConnAt_of_watcher _ w $$ Hcw
  ihave #Hk := attemptTokOk_of_watcher cl eps P w conn $$ [Hw Hc Ht]
  · iframe #
  iexists w, conn, wc, lg, ics
  iframe #

end defs

end client
end EtcdGrove
end Perennial
