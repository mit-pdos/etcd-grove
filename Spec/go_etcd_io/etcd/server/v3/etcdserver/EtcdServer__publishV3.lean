/-
`(*EtcdServer).publishV3(timeout)` (`server.go`): translated with its body (etcd-io/etcd#22527,
branch `pr-verify/etcd-22527`: the PR waits for apply after a "too many requests" rejection,
`waitApplyWithinRequestLimit`); one of the goroutines `Start` attaches. Lean-first (the request
path's unit 4c; on `lean` it is names-only, at the trust boundary, with the spec "returns").
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvStart

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The publisher's resources** (what `publishV3` needs besides the server's persistent views;
`NewServer`'s and `start`'s, a part of the construction premise): `s.attributes` (read-only, its
`ClientURLs` slice too), `s.ctx` (a context, set by `start`), `s.readych` (an unbuffered channel no
one sends on, which only the publisher closes: a broadcast channel, pending), a reader slot of
`s.leadTimeMu`, the auth store's reader resource `E.RD` and a reader slot of `s.lgMu` (each
call's: `raftRequest`'s and `Logger()`'s, given back), the id credits (`□ |==> idCred ρ.ids 1`:
one per attempt, `raftRequest`'s `Next`), and a certified log `F` (the proposer's floor). -/
def srvPublishRes (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (rc : Loc) (γrc : ChanNames) :
    IProp GF :=
  iprop(∃ (av : go_etcd_io.etcd.server.v3.etcdserver.api.membership.Attributes)
      (urls : List GoString) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
      (F : mvcc.Log),
    srvAttrAddr s ↦□ av ∗ av.ClientURLs' ↦*□ urls ∗
    srvCtxAddr s ↦□ (GoInterface.ok ci) ∗ context.isContext ci cd ∗
    srvReadychAddr s ↦□ rc ∗ ownBroadcastChan rc γrc iprop(True) .Pending ∗
    srvLeadTimeReader s ∗ E.RD ∗ srvLgReader s ∗
    □ (|==> idCred ρ.ids 1) ∗ mvcc.idxCert E.γ.idx F)

/-- `s.publishV3(timeout)`, the publisher goroutine, at the server's proposer and reader views
(`isServerReq`, `isServerRead`, the same applier environment `E`) and its resources
(`srvPublishRes`): it returns, with `readych` closed (`Done`) or not (`Pending`). The post says no
more: in particular it does not tie `Done` to a successful publish nor `Pending` to the server's
stop (the code closes `readych` only after `raftRequest` returns no error and returns with it open
only after a receive on `stopping`; `stopping`'s content is `True`, so the latter carries no fact),
and, a partial-correctness triple, it says nothing of how often the loop retries. What the proof
does check: every attempt meets `raftRequest`'s precondition (a fresh `InternalRaftRequest` with
the member's `ClusterMemberAttrSet` and a fresh header, one id credit, the context
`WithTimeout(s.ctx)`), the logging and `readych`'s single close are safe, and a "too many
requests" rejection is followed by `waitApplyWithinRequestLimit` under its spec. -/
abbrev EtcdServer.publishV3.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (rc : Loc) (γrc : ChanNames)
    (d : _root_.Perennial.time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReq s E ρ ∗ isServerRead s E γr ∗ srvPublishRes s E ρ rc γrc }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"publishV3")) (Val #d))
  {{ RET #(); ownBroadcastChan rc γrc iprop(True) .Done ∨
      ownBroadcastChan rc γrc iprop(True) .Pending }}

end spec

end EtcdGrove
end Perennial
