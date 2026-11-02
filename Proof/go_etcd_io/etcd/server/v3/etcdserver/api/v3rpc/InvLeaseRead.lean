/-
**The gRPC Lease service's read handlers, over the server's lease reads** (the lease rows at the
gRPC level, item 6 of the lessor/auth list, 2026-11-01; `notes/lease-grpc-plan.md`). Lean-first (no
Rocq counterpart).

`lease.go`'s `LeaseServer.LeaseTimeToLive` and `LeaseServer.LeaseLeases` call the server's methods
of the same name (`ls.le`, the server `s`: `leaseServerAt`) and fill the response's header. As the
unary write handlers over `raftLessor` (`InvLease.lean`), they are over a contract, discharged from
the server's proved specs (`ServerLeaseRead.lean`, `raftLeaseRead_of_server`).

**The contract** (`raftLeaseRead s E γl S R`, persistent; `lessorTTLOk`, `lessorLeasesOk`): the
triples of `*EtcdServer`'s `LeaseTimeToLive(ctx, r)` and `LeaseLeases(ctx, r)`, called with the
per-call resources `S` and the KV's revision reader `R` (which `LeaseLeases`' `newHeader()` reads,
and the handler's `fill` after it), both given back, at any context and lower bounds `n` (the auth
store's published index) and `m` (the lessor's history `γl`); their answers are the server's
(`ttlAns`, `leasesAns`): on success the response with the key check's verdict, on an error an
`applyErrIs` error. The server meets it with `S := E.RD ∗ threadTok` and
`R := mvcc.storeReader E.s E.γ`.

**The handlers' answers** (`leaseTTLOut`, `leaseLeasesOut`): the server's response with its header
filled (`leaseHdrDone`, `leasesHdrDone`) and the server's verdicts carried through; on the
server's `ErrLeaseNotFound`, the handler's own response (TTL `-1`; an empty listing); or `nil` and
a non-nil error. The not-found response carries no verdict and not even that the request was
authenticated, though Go reaches `ErrLeaseNotFound` only after `requireAuthInfo` (and, with
`Keys`, the key check): the entry point's error post is `applyErrIs` alone (the plan's review,
finding 2; the answer reveals only that the server's lessor, or the leader's, has no such lease).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvLease
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.LeaseRead

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace v3rpc

open Iris Iris.BI go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-! ## The server's answers -/

/-- **The server's `LeaseTimeToLive` answer** to the request `v` at the context `ctx`, with the
lower bounds `n`, `m`: `nil` and a fresh response with its header (owned), the request
authenticated (`authedOutB`) and, if it asks for the keys, the key check's verdict; or `nil` and an
`applyErrIs` error (`EtcdServer.LeaseTimeToLive.spec`'s). -/
def ttlAns (s : Loc) (E : apply.AEnv GF) (γl : GName) (ctx : GoInterfaceOk) (n m : Nat)
    (v : etcdserverpb.LeaseTimeToLiveRequest) (resp : Loc) (err : GoInterface) : IProp GF :=
  iprop((⌜err = GoInterface.nil⌝ ∗
      (∃ w : etcdserverpb.LeaseTimeToLiveResponse, resp ↦ w ∗ ⌜w.Header' ≠ null⌝ ∗
        ∃ hv : etcdserverpb.ResponseHeader, w.Header' ↦ hv) ∗
      authedOutB s E.authMode (GoInterface.ok ctx) GoInterface.nil ∗
      (if v.Keys' then leaseCheckFrom s E (GoInterface.ok ctx) n
          (fun info => leaseKeysVerdictFrom E.authMode n info γl m v.ID' .read)
        else iprop(True))) ∨
    (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ applyErrIs err))

/-- **The server's `LeaseLeases` answer** at the context `ctx`, with the lower bounds `n`, `m`:
`nil` and the listing of the ids `ids` of the lessor at an index `i ≥ m` (the response owned, its
header `newHeader()`'s at the server's ids), each lease's key check's verdict; or `nil` and an
`applyErrIs` error (`EtcdServer.LeaseLeases.spec`'s). -/
def leasesAns (s : Loc) (E : apply.AEnv GF) (γl : GName) (ctx : GoInterfaceOk) (n m : Nat)
    (resp : Loc) (err : GoInterface) : IProp GF :=
  iprop((⌜err = GoInterface.nil⌝ ∗ ∃ (i : Nat) (ids : List w64) (cs ms : w64), ⌜m ≤ i⌝ ∗
      lease.leaseIdsAt γl i ids ∗ leasesRespIs E resp cs ms ids ∗
      leaseCheckFrom s E (GoInterface.ok ctx) n (fun info => iprop([∗list] id ∈ ids,
        leaseKeysVerdictFrom E.authMode n info γl i id .read))) ∨
    (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ applyErrIs err))

/-! ## The contract -/

/-- **The server's `LeaseTimeToLive`** (one conjunct of `raftLeaseRead`). -/
def lessorTTLOk (s : Loc) (E : apply.AEnv GF) (γl : GName) (S R : IProp GF) : IProp GF :=
  iprop(∀ (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (r : Loc) (dq : DFrac)
      (v : etcdserverpb.LeaseTimeToLiveRequest) (n m : Nat),
    {{ S ∗ R ∗ context.isContext ci cd ∗ auth.authPubLbM E.authMode n ∗ lease.lessorLb γl m ∗
        r ↦{dq} v }}
      (App (App (Val (srvM s go!"LeaseTimeToLive")) (Val #(GoInterface.ok ci))) (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); S ∗ R ∗ r ↦{dq} v ∗
        ttlAns s E γl ci n m v resp err }})

/-- **The server's `LeaseLeases`** (one conjunct of `raftLeaseRead`). -/
def lessorLeasesOk (s : Loc) (E : apply.AEnv GF) (γl : GName) (S R : IProp GF) : IProp GF :=
  iprop(∀ (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (r : Loc) (n m : Nat),
    {{ S ∗ R ∗ context.isContext ci cd ∗ auth.authPubLbM E.authMode n ∗ lease.lessorLb γl m }}
      (App (App (Val (srvM s go!"LeaseLeases")) (Val #(GoInterface.ok ci))) (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); S ∗ R ∗
        leasesAns s E γl ci n m resp err }})

instance lessorTTLOk_persistent (s : Loc) (E : apply.AEnv GF) (γl : GName) (S R : IProp GF) :
    Persistent (lessorTTLOk s E γl S R) := by
  unfold lessorTTLOk; infer_instance

instance lessorLeasesOk_persistent (s : Loc) (E : apply.AEnv GF) (γl : GName) (S R : IProp GF) :
    Persistent (lessorLeasesOk s E γl S R) := by
  unfold lessorLeasesOk; infer_instance

/-- **The server's lease reads** (persistent; see the file header): its `LeaseTimeToLive` and
`LeaseLeases` at the per-call resources `S` and the revision reader `R`, over the lessor `γl`. -/
def raftLeaseRead (s : Loc) (E : apply.AEnv GF) (γl : GName) (S R : IProp GF) : IProp GF :=
  iprop(lessorTTLOk s E γl S R ∗ lessorLeasesOk s E γl S R)

instance raftLeaseRead_persistent (s : Loc) (E : apply.AEnv GF) (γl : GName) (S R : IProp GF) :
    Persistent (raftLeaseRead s E γl S R) := by
  unfold raftLeaseRead; infer_instance

/-! ## The handlers' answers -/

/-- **A header the handler filled** (owned): its ids the cluster's `cid` and the member's `mid`, some
term and leader (`hdrFilled`), and some revision. Nothing is said of the revision: on every Go
path of `LeaseTimeToLive` it is the local `Rev()` (the server's header is empty, the leader's too),
which `hdrIs`'s `rev` triple does not state. The header's other fields (`state`, `sizeCache`,
`unknownFields`) are not kept. -/
def leaseHdrDone (h : Loc) (cid mid : w64) : IProp GF :=
  iprop(hdrFilled h cid mid ∗ ∃ (dq : DFrac) (r : w64),
    structFieldRef etcdserverpb.ResponseHeader go!"Revision" h ↦{dq} r)

/-- **`LeaseLeases`' header after the handler's `fill`** (owned): `leaseHdrDone`'s, its revision
`r` the last of a log the server certified (`newHeader()`'s), unless that was `0` (then the local
`Rev()`'s). -/
def leasesHdrDone (E : apply.AEnv GF) (h : Loc) (cid mid : w64) : IProp GF :=
  iprop(hdrFilled h cid mid ∗ ∃ (dq : DFrac) (r : w64) (log : mvcc.Log),
    structFieldRef etcdserverpb.ResponseHeader go!"Revision" h ↦{dq} r ∗
    mvcc.idxCert E.γ.idx log ∗
    ⌜log ≠ [] ∧ (W64 ((log.length : Int) - 1) ≠ W64 0 → r = W64 ((log.length : Int) - 1))⌝)

/-- **`LeaseServer.LeaseTimeToLive`'s answer** to the request `v` at the context `ctx`, with the
lower bounds `n`, `m`: a response (owned) with its header filled, and either the server's (`ttlAns`'s
verdict) or, on the server's `ErrLeaseNotFound`, the handler's own (`{Header, ID: v.ID, TTL: -1}`,
the rest zero: no keys); or `nil` and a non-nil error. -/
def leaseTTLOut (s : Loc) (E : apply.AEnv GF) (γl : GName) (ctx : GoInterfaceOk) (n m : Nat)
    (v : etcdserverpb.LeaseTimeToLiveRequest) (cid mid : w64) (resp : Loc) (err : GoInterface) :
    IProp GF :=
  iprop((⌜err = GoInterface.nil⌝ ∗ ∃ w : etcdserverpb.LeaseTimeToLiveResponse,
      resp ↦ w ∗ leaseHdrDone w.Header' cid mid ∗
      ((authedOutB s E.authMode (GoInterface.ok ctx) GoInterface.nil ∗
          (if v.Keys' then leaseCheckFrom s E (GoInterface.ok ctx) n
              (fun info => leaseKeysVerdictFrom E.authMode n info γl m v.ID' .read)
            else iprop(True))) ∨
        ⌜w = { (zeroValDef : etcdserverpb.LeaseTimeToLiveResponse) with
          Header' := w.Header', ID' := v.ID', TTL' := W64 (-1) }⌝)) ∨
    ⌜resp = null ∧ err ≠ GoInterface.nil⌝)

/-- **`LeaseServer.LeaseLeases`' answer** at the context `ctx`, with the lower bounds `n`, `m`: a
response (owned) with its header filled, and either the server's listing (`leasesAns`'s: the ids of
the lessor at an index `i ≥ m`, each lease's verdict; its header's revision certified) or, on the
server's `ErrLeaseNotFound` (which `LeaseLeases` never returns; the arm is Go's code), an empty
listing; or `nil` and a non-nil error. -/
def leaseLeasesOut (s : Loc) (E : apply.AEnv GF) (γl : GName) (ctx : GoInterfaceOk) (n m : Nat)
    (cid mid : w64) (resp : Loc) (err : GoInterface) : IProp GF :=
  iprop((⌜err = GoInterface.nil⌝ ∗ ∃ w : etcdserverpb.LeaseLeasesResponse, resp ↦ w ∗
      ((∃ (i : Nat) (ids : List w64), ⌜m ≤ i⌝ ∗ lease.leaseIdsAt γl i ids ∗
          leasesHdrDone E w.Header' cid mid ∗ leasesListIs w ids ∗
          leaseCheckFrom s E (GoInterface.ok ctx) n (fun info => iprop([∗list] id ∈ ids,
            leaseKeysVerdictFrom E.authMode n info γl i id .read))) ∨
        (leaseHdrDone w.Header' cid mid ∗ w.Leases' ↦* ([] : List Loc)))) ∨
    ⌜resp = null ∧ err ≠ GoInterface.nil⌝)

end defs

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

open Iris.ProofMode

/-- The lessor's `ErrLeaseNotFound` (`leaseInit`): its value, a leaf error of the server's. -/
theorem leaseNotFoundErr [_root_.Perennial.errors.Assumptions] :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ⊢
      ∃ e : GoInterfaceOk, globalAddr go_etcd_io.etcd.server.v3.lease.ErrLeaseNotFound ↦□
        GoInterface.ok e ∗ applyErrIs (GoInterface.ok e) ∗ ⌜errLeaf e⌝ := by
  iintro #Hpkg
  ihave Hli : (go_etcd_io.etcd.server.v3.lease.leaseInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hli with ⟨#Hnf, -⟩
  iunfold go_etcd_io.etcd.server.v3.lease.leaseErrVar at Hnf
  icases Hnf with ⟨%e, #He, %Hl, #Hm⟩
  iexists e; iframe He; isplitl
  · iapply applyErrIs_leaf e Hl; iunfold errMsgOk; iexact Hm
  · ipureintro; exact Hl

/-- The header's revision before `fill`: kept read-only if not `0` (the reader `R` kept), lent
with `R` if `0`. -/
theorem hdrRev_in (Em : CoPset) (R : IProp GF) (h : Loc) (r : w64) :
    structFieldRef etcdserverpb.ResponseHeader go!"Revision" h ↦ r ∗ R ⊢
      |={Em}=> v3rpc.hdrRevIn R h r ∗ ((⌜r ≠ W64 0⌝ ∗ R) ∨ ⌜r = W64 0⌝) := by
  iintro ⟨Hr, HR⟩
  by_cases h0 : r = W64 0
  · imodintro
    iunfold v3rpc.hdrRevIn
    isplitl [Hr HR]
    · iright; iframe
    iright; ipureintro; exact h0
  · ipersist Hr
    imodintro
    iunfold v3rpc.hdrRevIn
    isplitr
    · ileft; iframe #; ipureintro; exact h0
    ileft; iframe; ipureintro; exact h0

/-- The header's revision after `fill`: the reader back, the revision `r'` (`r` unless `0`). -/
theorem hdrRev_out (R : IProp GF) (h : Loc) (r r' : w64) :
    ((⌜r ≠ W64 0⌝ ∗ R) ∨ ⌜r = W64 0⌝) ∗ v3rpc.hdrRevOut R h r r' ⊢
      R ∗ ∃ dq : DFrac, structFieldRef etcdserverpb.ResponseHeader go!"Revision" h ↦{dq} r' ∗
        ⌜r ≠ W64 0 → r' = r⌝ := by
  iunfold v3rpc.hdrRevOut
  iintro ⟨(⟨%h0, HR⟩ | %h0), (⟨%Hr, #Hrev⟩ | ⟨%Hr, Hrev, HR'⟩)⟩
  · obtain ⟨_, rfl⟩ := Hr
    iframe HR
    iexists _
    iframe Hrev
    ipureintro; intro; rfl
  · iframe HR
    iexists _
    iframe Hrev
    ipureintro; exact Hr
  · exact absurd h0 Hr.1
  · iframe HR'
    iexists _
    iframe Hrev
    ipureintro; exact Hr

end lemmas

end v3rpc
end EtcdGrove
end Perennial
