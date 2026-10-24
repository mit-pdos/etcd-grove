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
public import Proof.go_etcd_io.etcd.client.pkg.v3.types.IDStr

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

/-- **The raft network over HTTP**: the network's names, the member owning each host, (stage 5)
the streams' registry (`Stream.lean`) and (stage 6d) the members (a request's sender is one). -/
structure RaftHttp (GF : BundledGFunctors) [FfiSyntax] where
  γn : NetNames GF
  owner : GoString → w64
  γreg : GName
  member : w64 → Prop

/-- **The directory's hosts are distinct** (D34, stage 6a): no URL `http://h` is two members'. -/
def dirHostsDistinct (dir : w64 → List GoString) : Prop :=
  ∀ (id id' : w64) (h : GoString), go!"http://" ++ h ∈ dir id → go!"http://" ++ h ∈ dir id' →
    id = id'

open Classical in
/-- **The member owning the host `h`** in the directory `dir` (D34, stage 6a): the member one of
whose peer URLs is `http://h`, or `0` (no member: raft's ids are not `0`) if none. -/
noncomputable def netOwner (dir : w64 → List GoString) (h : GoString) : w64 :=
  if hx : ∃ id, go!"http://" ++ h ∈ dir id then Classical.choose hx else 0

/-- A host of member `id`'s URLs is owned by `id`. -/
theorem netOwner_of_mem (dir : w64 → List GoString) (hd : dirHostsDistinct dir) (id : w64)
    (h : GoString) (hm : go!"http://" ++ h ∈ dir id) : netOwner dir h = id := by
  unfold netOwner
  have hx : ∃ id, go!"http://" ++ h ∈ dir id := ⟨id, hm⟩
  rw [dif_pos hx]
  exact hd _ _ _ (Classical.choose_spec hx) hm

/-- **The network's raft-over-HTTP names** (D34, stage 6a): its owner map from the directory, its
streams' registry, (stage 6d) its members those with peer URLs in the directory. -/
noncomputable def netRh (γn : NetNames GF) : RaftHttp GF :=
  ⟨γn, netOwner γn.dir, γn.reg, fun id => γn.dir id ≠ []⟩

/-- **A request's sender, from its headers** (stage 6d; D35): `X-Server-From` holds the id of a
member other than the receiver `rid` (`addRemoteFromRequest` reads it: then `AddRemote` of a peer
does nothing). -/
def fromOkAt (Rh : RaftHttp GF) (rid : w64) (hs : List (GoString × GoString)) : Prop :=
  ∃ f : w64, http.hdrGet hs go!"X-Server-From" = types.idStr f ∧ Rh.member f ∧ f ≠ rid

/-- **A pipeline request of ticket `γk`** (persistent): its body an encoding of a message `st`,
not a snapshot (which goes by `SendSnapshot`), without responses, for the member owning the
request's host, (stage 6d) from another member (`fromOkAt`); with `□ N.P st` and its deposit. -/
def pipeReq (Rh : RaftHttp GF) (R : http.HReq) (γk : GName) : IProp GF :=
  iprop(∃ st : MsgSt, ⌜MsgWireOk st R.body ∧ st.msg.To' = Rh.owner R.host ∧
      st.msg.Type' ≠ MsgSnap ∧ st.resps = [] ∧ fromOkAt Rh (Rh.owner R.host) R.hdr⌝ ∗
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
