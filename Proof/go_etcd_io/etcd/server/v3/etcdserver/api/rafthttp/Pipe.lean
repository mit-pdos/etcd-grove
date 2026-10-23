/-
**The pipeline's protocol** (rafthttp stage 4, D33b; `notes/rafthttp-plan.md`). Lean-first.

A pipeline request (`POST /raft`, `pipeline.post`) carries one marshalled message, whose bundle
cannot cross the wire. The sender deposits it per request: an invariant holding the message's
one-shot part `N.O st` or the request's ticket (`pipeDeposit`), allocated with the ticket before
`RoundTrip`; the request protocol (`pipeReq`) says the body is an encoding of `st`, addressed to
the member owning the request's host, with `□ N.P st` and that deposit. The handler, which
receives the ticket (`http.handlerOk`), withdraws `N.O st` once (`pipe_withdraw`): a second
withdrawal would need a second ticket of the same name (`http.reqTicket_excl`).

**Hosts and members** (`RaftHttp`): the member owning a host (`owner`), consistent with the
network's directory (`OwnerOk`: a member's peer URLs' hosts are its own), so that the sender's
host names the message's destination and the receiver's host its own id.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.PbMessage
public import Proof.net.http.Boundary

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

def pipeN : Namespace := nroot.@"rafthttp_pipe"

/-- **A method-set premise** (as `EtcdGrove.ErrorStringLeaf`): an `errors.New` error (a
`*errorString`, whose methods are `Error` only) is not a `writerToResponse` (no `WriteTo`): what
the pipeline handler's `errors.As(err, &writerErr)` reads of `Process`'s `ErrStopped`. -/
class ErrorStringNotWriter [GoSemanticsFunctions] : Prop where
  notIn : go.typeSetContains (go.GoType.PointerType _root_.Perennial.errors.errorString.ty)
    go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.writerToResponse.ty = false

/-- **The pipeline's deposit for the request of ticket `γk`** (persistent): the message's one-shot
part, until the ticket's holder takes it and leaves the ticket. -/
def pipeDeposit (N : NetPayload GF) (γk : GName) (st : MsgSt) : IProp GF :=
  inv pipeN iprop(N.O st ∨ http.reqTicket γk)

instance pipeDeposit_persistent (N : NetPayload GF) (γk : GName) (st : MsgSt) :
    Persistent (pipeDeposit N γk st) := by
  unfold pipeDeposit; infer_instance

/-- **The raft network over HTTP**: the network's names, the member owning each host, and
(stage 5) the streams' registry (`Stream.lean`). -/
structure RaftHttp (GF : BundledGFunctors) [FfiSyntax] where
  γn : NetNames GF
  owner : GoString → w64
  γreg : GName

/-- **A pipeline request of ticket `γk`** (persistent): its body an encoding of a message `st`,
not a snapshot (which goes by `SendSnapshot`), without responses, for the member owning the
request's host; with `□ N.P st` and its deposit. -/
def pipeReq (Rh : RaftHttp GF) (R : http.HReq) (γk : GName) : IProp GF :=
  iprop(∃ st : MsgSt, ⌜MsgWireOk st R.body ∧ st.msg.To' = Rh.owner R.host ∧
      st.msg.Type' ≠ MsgSnap ∧ st.resps = []⌝ ∗
    □ Rh.γn.N.P st ∗ pipeDeposit Rh.γn.N γk st)

instance pipeReq_persistent (Rh : RaftHttp GF) (R : http.HReq) (γk : GName) :
    Persistent (pipeReq Rh R γk) := by
  unfold pipeReq; infer_instance

end defs

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **Deposit** a message's one-shot part for a request of ticket `γk`. -/
theorem pipe_deposit (N : NetPayload GF) (γk : GName) (st : MsgSt) (E : CoPset) :
    ⊢ N.O st ={E}=∗ pipeDeposit N γk st := by
  iintro HO
  unfold pipeDeposit
  iapply inv_alloc
  inext
  ileft; iexact HO

/-- **Withdraw** a deposit with its ticket (and a later credit): the one-shot part, once. -/
theorem pipe_withdraw (N : NetPayload GF) (γk : GName) (st : MsgSt) (E : CoPset)
    (HE : ↑pipeN ⊆ E) :
    ⊢ pipeDeposit N γk st -∗ http.reqTicket γk -∗ £ 1 ={E}=∗ N.O st := by
  iintro #Hd Ht Hlc
  unfold pipeDeposit
  iinv Hd with Hc Hclose
  imod lc_fupd_elim_later $$ Hlc Hc with Hc
  icases Hc with (HO | Ht')
  · imod Hclose $$ [Ht] with -
    · inext; iright; iexact Ht
    imodintro
    iexact HO
  · iexfalso
    iapply http.reqTicket_excl γk $$ [$Ht $Ht']

end lemmas

end EtcdGrove
end Perennial
