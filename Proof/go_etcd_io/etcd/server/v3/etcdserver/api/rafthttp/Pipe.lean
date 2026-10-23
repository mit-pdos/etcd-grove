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

/-- **The pipeline's deposit for the request of ticket `γk`** (persistent): the message's one-shot
part, until the ticket's holder takes it and leaves the ticket. -/
def pipeDeposit (N : NetPayload GF) (γk : GName) (st : MsgSt) : IProp GF :=
  inv pipeN iprop(N.O st ∨ http.reqTicket γk)

instance pipeDeposit_persistent (N : NetPayload GF) (γk : GName) (st : MsgSt) :
    Persistent (pipeDeposit N γk st) := by
  unfold pipeDeposit; infer_instance

/-- **The raft network over HTTP**: the network's names and the member owning each host. -/
structure RaftHttp (GF : BundledGFunctors) [FfiSyntax] where
  γn : NetNames GF
  owner : GoString → w64

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

/-- **A raft member's address's protocol** (stage 4: the pipeline's part; the streams' is stage
5's): a `POST` to `/raft` is a pipeline request; its response is not a `403` (the status
`errMemberRemoved` is reported for, which no member of a static cluster answers). -/
def raftProto (Rh : RaftHttp GF) : http.Proto GF where
  req R γk := iprop(⌜R.meth = go!"POST" ∧ R.path = go!"/raft"⌝ → pipeReq Rh R γk)
  req_pers R γk := by infer_instance
  resp R _γk st _w := iprop(⌜R.path = go!"/raft" → st ≠ W64 403⌝)
  resp_pers R γk st w := by infer_instance

/-- The raft network's HTTP network: every address's protocol is a raft member's. -/
def raftHttpNet (Rh : RaftHttp GF) : http.HttpNet GF := ⟨fun _ => raftProto Rh⟩

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
