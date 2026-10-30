/-
**The server's compaction mode** (M2, `notes/m2-plan.md`, phase 1, S2-S3; 2026-10-28): the
statements of a server whose auto-compactor is on (`NewServer.specCompact`), beside the compaction-
off ones, which stay as they are (a variant per statement, as the auth mode's `specOn`, until the
proofs exist: an unproved case of one statement would reach every result over it).

* `compactPropOk`: a compaction request as the server proposes it (S2: `reqPropOk`'s compaction
  form; no permit, C3 being deferred, and a latest read is never compacted at any revision).
* `irrNoDelPut`: a request whose write deletes no key it puts again in its revision (phase 0's
  decision 3, option (a) of S2: the admitted writes, in compaction mode only;
  `issues/etcd-compaction-delete-then-put.md`).
* `reqPropOkC`: what the compaction mode admits: a request `reqPropOk` admits that deletes no key it
  puts again, or a compaction.
* `apply.dispatchOkC`: `dispatchOk` without the compaction conjunct.
* `compactResultIs`: the apply thread's result of a compaction (`applierV3backend.Compaction`
  through the uber-applier): the response, or the error the request path reports.
* `srvRevLb`: a revision the store has reached (a certified log longer than it): what a compaction's
  proposer holds of its revision (review round 1, S2-3: `store.Compact` needs it), and the
  compactor's `RevLb` on the server.
* The compaction-mode view of the request path (review round 1, S2-1): `rqShapeC`/`entryShapeC`/
  `logShapeC` (a request's shape with `dispatchOkC` and, for a write, `irrNoDelPut`),
  `plainEntryC`/`plainLogC` (a plain request or a compaction), `compactClaims` (every committed
  compaction's revision reached), `kvWorkC`, `kvInvC` (the KV invariant admitting compaction
  entries), `srvReqFieldsAtC`/`isServerReqC` (`isServerReq` over `kvInvC`): a family beside the
  compaction-off one, as the auth mode's `…On` family; the compaction-off statements are unchanged.

Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvProposer

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section pure
variable [GooseExts]

/-- **A compaction request**, as `EtcdServer.Compact` proposes it (`&pb.InternalRaftRequest{
Compaction: r}`): of the kind `compaction`, at a revision `≥ 1` (M2, the storage side, 2026-10-30:
**M2's scope restriction**, the user's Q7 (a), the approval's item 35: no compaction at revision `0`,
`issues/etcd-restore-scheduled-compact-zero.md`; `EtcdServer.Compact.spec`'s premise `1 ≤ r`). -/
def compactPropOk (rq : apply.IRRModel) : Prop :=
  apply.dispatchKind rq = .compaction ∧ ∃ r : w64, rq.compaction = some r ∧ 1 ≤ sint.Z r

/-- `&pb.InternalRaftRequest{Compaction: r}`, for `r` at the revision `rev` (`EtcdServer.Compact`'s). -/
def irrCompaction (rev : w64) : apply.IRRModel := { apply.irrEmpty with compaction := some rev }

/-- `Compact`'s request at a revision `≥ 1` is a compaction in M2's scope. -/
theorem compactPropOk_irrCompaction (rev : w64) (h : 1 ≤ sint.Z rev) :
    compactPropOk (irrCompaction rev) :=
  ⟨by simp [apply.dispatchKind, irrCompaction, apply.irrEmpty], rev, rfl, h⟩

/-- **A request that deletes no key it puts again** in the revision it makes (S2, option (a)):
whatever the chain, a dispatch that appends a revision appends one with `mvcc.NoDelPutAt`, so a
later compaction at that revision keeps the key's live value
(`issues/etcd-compaction-delete-then-put.md`). -/
def irrNoDelPut (rq : apply.IRRModel) : Prop :=
  ∀ (c : apply.Chain) (log : mvcc.Log) (o : apply.Outcome),
    apply.dispatchStep c rq true log o → (o.logAfter log).length = log.length + 1 →
      mvcc.NoDelPutAt (o.logAfter log) log.length

/-- **The premise on a request's kind in compaction mode**: `dispatchOk` without its compaction
conjunct (S2). -/
def apply.dispatchOkC (on : Bool) (rq : apply.IRRModel) : Prop :=
  apply.dispatchKind rq ≠ .none ∧ (apply.dispatchKind rq = .authEnable → on = true)

/-- `dispatchOk` gives `dispatchOkC`. -/
theorem apply.dispatchOkC_of (on : Bool) (rq : apply.IRRModel) (h : apply.dispatchOk on rq) :
    apply.dispatchOkC on rq := ⟨h.2.1, h.2.2⟩


/-- **A request's shape in compaction mode** (`rqShape` with `dispatchOkC`; a request that deletes
no key it puts again: option (a) of S2, on the admitted writes). -/
def rqShapeC (rq : apply.IRRModel) : Prop :=
  (∀ on, apply.dispatchOkC on rq) ∧ (∀ log, rqSmall log rq → apply.rqOk log rq) ∧ irrNoDelPut rq

/-- `entryShape` over `rqShapeC`. -/
def entryShapeC (m : EntryModel) : Prop :=
  (m.typ = W32 0 → m.data = [] ∨ ∃ rq, apply.irrDecode m.data = some rq ∧
      (∃ id, apply.irrId rq = some id) ∧ rqShapeC rq) ∧
    (m.typ ≠ W32 0 → ccIdOf m.data = W64 0)

/-- Every entry of a log of a good shape, in compaction mode. -/
def logShapeC (L : List EntryModel) : Prop := ∀ m ∈ L, entryShapeC m

/-- **A plain entry in compaction mode**: a plain request, or a compaction. -/
def plainEntryC (m : EntryModel) : Prop :=
  m.typ = W32 0 → m.data ≠ [] → ∀ rq, apply.irrDecode m.data = some rq →
    plainReq rq ∨ compactPropOk rq

/-- Every entry plain, in compaction mode. -/
def plainLogC (A : List EntryModel) : Prop := ∀ m ∈ A, plainEntryC m

/-- **Every committed compaction is past revision `0`** (M2's scope restriction, item 35; the log
invariant's content): a committed entry decoding to a compaction request at `r` has `1 ≤ r` (a
plain request is not a compaction: `putgetKind`). -/
theorem plainLogC_compaction_pos (L : List EntryModel) (hL : plainLogC L) (m : EntryModel)
    (hm : m ∈ L) (ht : m.typ = W32 0) (hd : m.data ≠ []) (rq : apply.IRRModel)
    (hrq : apply.irrDecode m.data = some rq) (hk : apply.dispatchKind rq = .compaction) (r : w64)
    (hr : rq.compaction = some r) : 1 ≤ sint.Z r := by
  rcases hL m hm ht hd rq hrq with hp | ⟨-, r', hr', h1⟩
  · exfalso
    have := hp.2
    rw [hk] at this
    simp [putgetKind] at this
  · rw [hr] at hr'; cases hr'; exact h1

/-- A plain entry is one in compaction mode. -/
theorem plainEntryC_of (m : EntryModel) (h : plainEntry m) : plainEntryC m :=
  fun h1 h2 rq h3 => Or.inl (h h1 h2 rq h3)

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **A revision the store has reached** (persistent): a certificate of a log longer than it. -/
def srvRevLb (γ : mvcc.StoreNames) (n : Int) : IProp GF :=
  iprop(∃ log : mvcc.Log, mvcc.idxCert γ.idx log ∗ ⌜n < log.length⌝)

instance srvRevLb_persistent (γ : mvcc.StoreNames) (n : Int) :
    Persistent (srvRevLb (GF := GF) γ n) := by
  unfold srvRevLb; infer_instance

/-- A revision below one the store has reached is reached. -/
theorem srvRevLb_mono (γ : mvcc.StoreNames) (n m : Int) (h : n ≤ m) :
    srvRevLb (GF := GF) γ m ⊢ srvRevLb γ n := by
  iintro H
  iunfold srvRevLb at H
  icases H with ⟨%log, #Hc, %Hl⟩
  iunfold srvRevLb
  iexists log
  iframe Hc
  ipureintro; omega

/-- **Every committed compaction's revision reached** (persistent, store `γs`): the apply's
`store.Compact` call needs its certificate (`store.Compact.spec`'s `rev < log.length`). -/
def compactClaims (γs : mvcc.StoreNames) (L : List EntryModel) : IProp GF :=
  iprop([∗list] m ∈ L, □ ∀ (rq : apply.IRRModel) (r : w64),
    ⌜m.typ = W32 0 ∧ apply.irrDecode m.data = some rq ∧ rq.compaction = some r⌝ -∗
      srvRevLb γs (sint.Z r))

instance compactClaims_persistent (γs : mvcc.StoreNames) (L : List EntryModel) :
    Persistent (compactClaims (GF := GF) γs L) := by
  unfold compactClaims; infer_instance

/-- `kvWork` in compaction mode (`logShapeC`; the compactions' revisions reached). -/
def kvWorkC (cfg : SrvRaft) (γk : KVNames) (γs : mvcc.StoreNames) (L : List EntryModel) :
    IProp GF :=
  iprop(⌜logShapeC L ∧ ccLogOk cfg L⌝ ∗ ([∗list] m ∈ L, entryClaim γk.ids m) ∗ compactClaims γs L)

instance kvWorkC_persistent (cfg : SrvRaft) (γk : KVNames) (γs : mvcc.StoreNames)
    (L : List EntryModel) : Persistent (kvWorkC (GF := GF) cfg γk γs L) := by
  unfold kvWorkC; infer_instance

/-- **The KV invariant in compaction mode** (`kvInv`'s, over `plainLogC` and `kvWorkC`: compaction
entries admitted; a compaction changes no value, `apply.dispatchStep` leaving the log as it is). -/
def kvInvC (γ : ServerRaftNames) (γk : KVNames) (γs : mvcc.StoreNames) : IProp GF :=
  inv kvN iprop(∃ L : List EntryModel,
    srvRLog γ L ∗ ghostVar γk.st (1 : Qp).half (kvModelSt γk L) ∗
    ⌜plainLogC L ∧ srvIdxOkW γ.ai0 L ∧ uint.Z γk.c0 ≤ uint.Z γ.ai0 ∧
      γk.ch0 = apply.alarmChain false false false ∧ γk.log0 ≠ []⌝ ∗ kvWorkC γ.raft γk γs L)

instance kvInvC_persistent (γ : ServerRaftNames) (γk : KVNames) (γs : mvcc.StoreNames) :
    Persistent (kvInvC (GF := GF) γ γk γs) := by
  unfold kvInvC; infer_instance

/-- **The server as a compaction-mode proposer sees it** (`srvReqFieldsAt` over `kvInvC`). -/
def srvReqFieldsAtC (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (v : ReqFields) : IProp GF :=
  iprop(structFieldRef EtcdServer go!"reqIDGen" s ↦□ v.gen ∗ idGen ρ.ids v.gen (srvFloorFact E) ∗
    structFieldRef EtcdServer go!"w" s ↦□ v.w ∗ waitInv v.w ρ E ∗
    srvRaftNode s ρ.raft ∗
    srvCfgFieldAddr s go!"MaxRequestBytes" ↦□ v.maxReq ∗
    srvCfgFieldAddr s go!"ServerFeatureGate" ↦□ v.fg ∗ isFeatureGate v.fg ∗
    srvCfgFieldAddr s go!"ClientCertAuthEnabled" ↦□ v.cca ∗
    srvCfgFieldAddr s go!"ElectionTicks" ↦□ v.electionTicks ∗
    srvCfgFieldAddr s go!"TickMs" ↦□ v.tickMs ∗
    structFieldRef EtcdServer go!"authStore" s ↦□ v.auth ∗ isReqAuth v.auth E.RD ∗
    structFieldRef EtcdServer go!"done" s ↦□ v.done ∗ srvDoneChan v.done ∗
    structFieldRef EtcdServer go!"memberID" s ↦□ v.memberID ∗
    srvAtomicU64 (structFieldRef EtcdServer go!"lead" s) ∗
    structFieldRef EtcdServer go!"cluster" s ↦□ v.cluster ∗
    structFieldRef raftNodeConfig go!"transport"
      (structFieldRef raftNode go!"raftNodeConfig" (structFieldRef EtcdServer go!"r" s)) ↦□ v.tr ∗
    srvPeersOk v.cluster v.cid v.tr ∗
    srvIndexInvs s E ∗
    srvMintInv ρ ∗ kvInvC ρ.raft ρ.kv E.γ ∗ ⌜structFieldRef EtcdServer go!"Cfg" s ≠ null⌝)

instance srvReqFieldsAtC_persistent (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (v : ReqFields) :
    Persistent (srvReqFieldsAtC s E ρ v) := by
  unfold srvReqFieldsAtC; infer_instance

/-- **The server, as a compaction-mode proposer sees it** (persistent; `isServerReq` in
compaction mode). -/
def isServerReqC (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) : IProp GF :=
  iprop(∃ v : ReqFields, srvReqFieldsAtC s E ρ v)

instance isServerReqC_persistent (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) :
    Persistent (isServerReqC s E ρ) := by
  unfold isServerReqC; infer_instance

/-- **What the compaction mode admits** (S2, `reqPropOk`'s compaction form): a request
`reqPropOk` admits whose write deletes no key it puts again, or a compaction (its result
predicate trivial). -/
def reqPropOkC (γk : KVNames) (rq : apply.IRRModel) (Qr : List EntryModel → IProp GF) :
    IProp GF :=
  iprop((reqPropOk γk rq Qr ∗ ⌜irrNoDelPut rq⌝) ∨
    ⌜compactPropOk rq ∧ Qr = fun _ => iprop(True)⌝)

/-- **The result of a compaction** (S2-S3): the apply thread's `*apply.Result`, read-only, with
its trace, if any, owned (`apply.traceRes`: `Compact` uses `result.Trace` before it checks
`result.Err`; on success the applier's trace, on an error a nil one, `apply/backend.go`), and the compaction's response (`*pb.CompactionResponse`, its header if any, owned:
`Compact` writes the revision into it) or the error the request path reports (`applyErrIs`: the
store's `ErrCompacted`; `store.Compact`'s spec excludes its `ErrFutureRev`, M2's item 18). -/
def compactResultIs (res : Loc) : IProp GF :=
  iprop(⌜res ≠ null⌝ ∗ ∃ v : go_etcd_io.etcd.server.v3.etcdserver.apply.Result, res ↦□ v ∗
    apply.traceRes v.Trace' ∗
    ((⌜v.Err' = GoInterface.nil⌝ ∗ ∃ rp : Loc,
        ⌜v.Resp' = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.api.v3.etcdserverpb.CompactionResponse.ty) #rp⌝ ∗
        (⌜rp = null⌝ ∨ ∃ cv : go_etcd_io.etcd.api.v3.etcdserverpb.CompactionResponse, rp ↦ cv ∗
          (⌜cv.Header' = null⌝ ∨ ∃ hv : go_etcd_io.etcd.api.v3.etcdserverpb.ResponseHeader, cv.Header' ↦ hv))) ∨
      (⌜v.Err' ≠ GoInterface.nil⌝ ∗ applyErrIs v.Err')))

end defs

end EtcdGrove
end Perennial
