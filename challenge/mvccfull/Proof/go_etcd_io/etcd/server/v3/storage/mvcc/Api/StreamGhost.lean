/-
**The watch API's predicates over the stream's history, and `wsRecv_ok.law`'s entailment**
(stage 2 of the mvcc API proof, the watch chain: `notes/mvcc-api-risk.md`, M1; 2026-11-04).
Lean-first (no Rocq counterpart).

A stream's API ghost names (`WsAbs`): its store's (`st`), its history (`ev`, a monotone list of
`Api/StreamLog.lean`'s events, the authority the channel invariant's), the count of its client's
events (`ns`, a monotone count: the authority whole in `wsState`, so that a receiver's lower bound
of the history, minted with a lower bound of the count, carries no client event the client has not
made), the consumer's view (`rcv`, half the client's `wsRecv`, half the channel invariant's; `rx`,
the client's exclusive token, a count's whole authority fixed at `0`: a receive needs no update
outside the channel invariant), its channel, and the channel invariant's received prefix (`crecv`,
the store's responses, half the client's).

- `logTok ι l dec`: a lower bound `l` of the history, well formed with the filters decoded by
  `dec` (each name's saved filters), and each send's lower bounds (`evTok`: the notified log, the
  compaction revision). Persistent; every lower bound of a well-formed history is one.
- `mvccStateI a σ`: the client's part of the store's API ghost state (half the view, half the
  pending revision, half the compaction authority, the whole notified-log authority, and `σ`
  reachable).
- `wsStateI ι S`: the client's count of its events, at a lower bound of the history whose replay is
  `S` (the lower bound minted at the client's last event).
- `wsRecvI ι rs`: the consumer's view at `rs`, a prefix of a lower bound's sends.
- `wsSentLbI ι n`: a lower bound with at least `n` sends.

`wsRecv_okI`: the four give `wsRecvOk σ S rs`, a plain entailment: the two lower bounds are
comparable (`mono_list_lb_valid`); if the receiver's is the longer, its extra events are sends
only (the count's lower bound against the client's authority), so its replay's stream state is
`S`; the filters agree by their saved names (`savedFilters_agree`, no later); each send's bounds
are below the client's state (its authorities).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.StreamLog
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.Ghost
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.ApiGhost

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc
namespace api

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc sent

/-- **A watch stream's API ghost names** (see the file header). -/
structure WsAbs where
  st : AbsNames
  ev : GName
  ns : GName
  rcv : GName
  rx : GName
  ch : GoChan
  chn : ChanNames
  /-- the channel invariant's received prefix (`γc.recv`, its responses as the store sent them):
  half the consumer's, in `wsRecv` (2026-11-05, the receive law) -/
  crecv : GName
  /-- the history at the client's last event (a ghost variable of `List SEv`): half the client's,
  in `wsState`, half the stream's mutex invariant's, so that the stream, under its lock, knows the
  client's state (stage 2, the registration, 2026-11-05) -/
  cl : GName

/-- A response as the API's client sees it (`WResp`): its id, events, revision and compaction
revision. -/
def _root_.Perennial.EtcdGrove.mvcc.RespM.toW (x : RespM) : WResp :=
  ⟨x.id, x.evs, x.rev, x.compactRev⟩

/-- A send's bounds below `N` and `c` (other events: nothing). -/
def sendLbs (N : Log) (c : Int) : SEv → Prop
  | .send _ _ _ _ L c0 _ _ => L <+: N ∧ c0 ≤ c
  | _ => True

section defs
variable {GF : BundledGFunctors} [AllG GF]

/-- What a send's event carries (persistent): its bounds, below the store's state when sent. -/
def evTok (a : AbsNames) : SEv → IProp GF
  | .send _ _ _ _ L c0 _ _ => iprop(nlLb a L ∗ crevAtLeast a c0)
  | _ => iprop(True)

variable [ReceiptGS GF] in
/-- **The store's state is `σ`**: the client's part of the store's API ghost state. -/
def mvccStateI (a : AbsNames) (σ : MvccState) : IProp GF :=
  iprop(absPart a (1 : Qp).half σ.log σ.crev ∗ pndPart a (1 : Qp).half σ.pending ∗
    crevAuth a (1 : Qp).half σ.crev ∗ nlAuth a 1 σ.notifiedLog ∗ ⌜MvccReachable σ⌝ ∗
    ⧖ (logCh σ.log))

/-! ## Exclusivity -/

/-! ## The entailment -/

end defs

end api
end mvcc
end EtcdGrove
end Perennial
