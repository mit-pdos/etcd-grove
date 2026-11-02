/-
**mvcc's candidate API's watch stream, implemented** (`notes/mvcc-api-proof-plan.md`): the stream's
names, its predicate, the open token's shares, the registrar's view and the consumer's, over the
old stream (`isWatchStream` at the store's parameters `storeWatchParams`, `InvWatchStream.lean`),
its channel's invariant (`watchChanInv`) and the facts a receive gives (`watchRecvResult`,
`WatchRecv.lean`), which the consumer's view accumulates per received response.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.ApiImpl
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.WatchRecv

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

/-- **A watch stream's names**: its store's, the old stream's (`o`) and its channel's (`c`), the
channel, and the API's own: the registrar's token (`reg`), the consumer's (`rcv`), and the open
token's shares (`op`). -/
structure WsNameI where
  mv : MvccImpl
  o : WsStreamNames
  c : WatchChanNames
  ch : Loc
  reg : GName
  rcv : GName
  op : GName

/-- The open token's invariant's namespace. -/
def wsOpenN : Namespace := nroot .@ "mvccWsOpen"

/-- A response as the client sees it (no compaction: the store does not compact in the abstract
mode). -/
def respView (m : RespM) : WResp := ⟨m.id, m.evs, m.rev, W64 0⟩

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **The stream `st` of the store `γ`, named `ι`** (`isMvccWatchStream`): the old stream over the
watchable store at the store's parameters, with the API's choices of its progress fact and cancel
reason (`True`), its channel and the channel's invariant, and the open token's invariant (all of the
token or the old stream's open token). -/
def isMvccWatchStreamI (st : Loc) (γ : MvccImpl) (ι : WsNameI) : IProp GF :=
  iprop(⌜ι.mv = γ ∧ γ.watched = true ∧ ι.o.ids = ι.c.ids ∧ ι.o.prog = ι.c.prog ∧
      ι.o.sentl = ι.c.sentl ∧ ι.o.rsn = ι.c.rsn ∧ ι.o.regi = ι.c.regi ∧ 0 < sint.Z ι.c.ch.chanCap⌝ ∗
    isWatchStream st (interface.mkOk (go.GoType.PointerType watchableStore.ty) #γ.wl)
      (storeWatchParams γ.wl γ.sl γ.ws) ι.o ∗
    st.[watchStream, go!"ch"] ↦□ ι.ch ∗ isChan ι.ch ι.c.ch WatchResponse ∗
    inv watchN (watchChanInv γ.ws ι.ch ι.c) ∗
    savedPropOwn ι.o.prog DFrac.discard iprop(True) ∗
    savedPredOwn ι.o.rsn DFrac.discard (fun _ : w64 => iprop(True)) ∗
    inv wsOpenN iprop(ghostVar ι.op 1 () ∨ watchStreamOpen ι.o) ∗
    isWatchableMvccI γ.wl γ)

instance isMvccWatchStreamI_persistent (st : Loc) (γ : MvccImpl) (ι : WsNameI) :
    Persistent (isMvccWatchStreamI (GF := GF) st γ ι) := by
  unfold isMvccWatchStreamI; infer_instance

/-- A share `q` of the stream's open token (`wsOpen`). -/
def wsOpenI (ι : WsNameI) (q : Qp) : IProp GF := ghostVar ι.op q ()

/-- **A watcher of the registrar's view, named `id`** (persistent): the stream's assignment of `id`
to a watcher of the store with the view's range, filters and first revision. -/
def wInfoOk (ι : WsNameI) (id : w64) (wi : WInfo) : IProp GF :=
  iprop(∃ (w : Loc) (fcs : GoSlice), idAssigned ι.o id w ∗
    watcherIs ι.mv.ws w wi.rg fcs wi.lo ∗ filtersImpl fcs wi.fs ∗ ⌜wi.rg.id = id⌝)

instance wInfoOk_persistent (ι : WsNameI) (id : w64) (wi : WInfo) :
    Persistent (wInfoOk (GF := GF) ι id wi) := by
  unfold wInfoOk; infer_instance

/-- **The registrar's view** (`wsWatchers`): its token, and each watcher's facts. -/
def wsWatchersI (ι : WsNameI) (W : GMap w64 WInfo) : IProp GF :=
  iprop(ghostVar ι.reg 1 () ∗ □ ([∗map] id ↦ wi ∈ W, wInfoOk ι id wi))

/-- **What a received response gave** (persistent), the `j`-th after the responses `pre`: the
receive's facts (`watchRecvResult`'s, but the consumer's half). -/
def rcvFact (γ : WsNames) (γc : WatchChanNames) (pre : List RespM) (m : RespM) : IProp GF :=
  iprop(respOk m ∗ watchRecvOk γ m.w ((pre ++ [m]).filter (fun x => decide (x.w = m.w))) ∗
    chanRegFact γc m.w ∗ (⌜m.id = W64 (-1)⌝ → progFact γc.prog) ∗ respCov γ γc pre m ∗
    regsAt γc pre.length m ∗ chanSentLb γc (pre ++ [m]) ∗ ⌜m.idx = pre.length⌝)

instance rcvFact_persistent (γ : WsNames) (γc : WatchChanNames) (pre : List RespM) (m : RespM) :
    Persistent (rcvFact (GF := GF) γ γc pre m) := by
  unfold rcvFact; infer_instance

/-- **The consumer's view** (`wsRecv`): its token, the channel's consumer's half at the responses
`ms` received, whose views are `rs`, and each one's facts. -/
def wsRecvI (ι : WsNameI) (rs : List WResp) : IProp GF :=
  iprop(ghostVar ι.rcv 1 () ∗ ∃ ms : List RespM, watchConsumer ι.c ms ∗ ⌜rs = ms.map respView⌝ ∗
    □ ([∗list] j ↦ m ∈ ms, rcvFact ι.mv.ws ι.c (ms.take j) m))

end defs

end mvcc
end EtcdGrove
end Perennial
