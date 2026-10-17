/-
**The publish loop** (`publishV3`, `server.go`) and its snapshot check (`hasPublishedAttributes`),
as changed by etcd-io/etcd#22525 (verified on branch `pr-verify/etcd-22525`): the shared
vocabulary of their specs. Lean-first (no Rocq counterpart).

`publishV3` proposes the member's attributes (`ClusterMemberAttrSet`) through `raftRequest` until
an attempt succeeds or the server stops; on success it closes `s.readych` (the readiness
`ReadyNotify` returns). The PR adds, per attempt, a goroutine that waits for `s.snapshotApplied`
(notified by `applySnapshot`) and, after each snapshot, checks the applied membership
(`hasPublishedAttributes`); when that holds the member's current attributes, it sets
`publishedBySnapshot` and cancels the attempt's context, and the attempt counts as published even
though its `raftRequest` failed.

* **What "published" means** (`pubDone`, pure): either the apply thread dispatched this member's
  own request (`raftRequest`'s success: the request's wire form `rq'` went through `applyStep`), or
  the cluster's membership held the member's attributes (`membership.attrsHeld`, the trust boundary
  of `RaftCluster.Member`). `s.readych` is a broadcast channel whose closing carries `pubDone`
  (`srvReady`): `publishV3` closes it only with that evidence.
* **What `publishV3` reads** (`srvPubFields`, persistent): the member id, the cluster (`Member`,
  `ID`), the attributes and their URL slice (read-only: `NewServer` sets them), the logger, the
  server's context and `stopping` channel, the snapshot notifier, a certified log (for
  `raftRequest`), the id budget.
* **The snapshot check's goroutines and the notifier's reader slots.** Each attempt starts a
  goroutine that calls `Receive` on `s.snapshotApplied` (a read lock of the notifier's `RWMutex`,
  whose reader slots Perennial bounds: `notifyReader`). The goroutines are not joined: an attempt's
  goroutine exits once its context is done, but the next attempt may start before. So the slots
  are kept in a pool (`pubPoolInv`), which a goroutine draws from by depositing its thread token
  and gives back when it exits (`wp_fork_tok`): with fewer live threads than slots
  (`threadBound GF < actualMaxReaders`, a premise of the server's start, `isServerBuilt`), the
  pool is never empty when a goroutine draws.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRun
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRead
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Defs
public import Perennial.Golang.Theory.Chan.Idioms.Broadcast

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section addrs
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

/-- The address of `s.attributes` (a `membership.Attributes`). -/
abbrev srvAttrsAddr (s : Loc) : Loc := structFieldRef EtcdServer go!"attributes" s
/-- The address of `s.readych`. -/
abbrev srvReadychAddr (s : Loc) : Loc := structFieldRef EtcdServer go!"readych" s
/-- The address of `s.snapshotApplied` (etcd-io/etcd#22525: `start` sets it, `applySnapshot`
notifies it, `publishV3`'s snapshot check receives from it). -/
abbrev srvSnapAppliedAddr (s : Loc) : Loc := structFieldRef EtcdServer go!"snapshotApplied" s

end addrs

/-! ## The request and what "published" means -/

/-- `&pb.InternalRaftRequest{ClusterMemberAttrSet: req}` for `req` holding `m`. -/
def irrMemberAttrSet (m : apply.MemberAttrModel) : apply.IRRModel :=
  { apply.irrEmpty with clusterMemberAttrSet := some m }

section pure
variable [ext : FfiSyntax] [go_gctx : GoGlobalContext]

/-- `publishV3`'s request for the member `id` with the attributes `a` (whose client URLs hold
`cus`). -/
def pubReq (id : w64) (a : go_etcd_io.etcd.server.v3.etcdserver.api.membership.Attributes)
    (cus : List GoString) : apply.IRRModel :=
  irrMemberAttrSet ⟨id, a.Name', cus⟩

/-- **The member `id`'s attributes `a` (URLs `cus`) are published in the cluster `c`**: the apply
thread dispatched the member's own request (its wire form, with some header), or `c`'s membership
held the attributes (`membership.attrsHeld`). -/
def pubDone (c : Loc) (id : w64) (a : go_etcd_io.etcd.server.v3.etcdserver.api.membership.Attributes)
    (cus : List GoString) : Prop :=
  membership.attrsHeld c id a.Name' cus ∨
  ∃ (hm : apply.HeaderModel) (rq' : apply.IRRModel) (x x' : apply.ApplyKV) (o : apply.Outcome)
    (skip : Bool),
    irrWireOf (apply.withHeader (pubReq id a cus) hm) rq' ∧
      apply.applyStep rq' true x x' (.dispatched o skip)

end pure

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`s.readych` at the state `st`** (Perennial's broadcast idiom): its closing carries `Q`. The
closer (`publishV3`) holds it `.Pending`; closed, `.Done`. -/
def srvReady (s : Loc) (Q : IProp GF) (st : Broadcast) : IProp GF :=
  iprop(∃ (rch : Loc) (γ : ChanNames), srvReadychAddr s ↦□ rch ∗ ownBroadcastChan rch γ Q st)

/-- **The member's identity and attributes as the server holds them** (persistent): the member
id `id`, the cluster `c` (its members' mutex, `isRaftCluster`), the attributes `a` with their
client URLs' slice holding `cus`, all read-only. -/
def srvMemberAttrs (s c : Loc) (id : w64)
    (a : go_etcd_io.etcd.server.v3.etcdserver.api.membership.Attributes) (cus : List GoString) :
    IProp GF :=
  iprop(srvMemberIDAddr s ↦□ id ∗ srvClusterAddr s ↦□ c ∗ membership.isRaftCluster c ∗
    srvAttrsAddr s ↦□ a ∗ a.ClientURLs' ↦*□ cus)

instance srvMemberAttrs_persistent (s c : Loc) (id : w64)
    (a : go_etcd_io.etcd.server.v3.etcdserver.api.membership.Attributes) (cus : List GoString) :
    Persistent (srvMemberAttrs (GF := GF) s c id a cus) := by
  unfold srvMemberAttrs; infer_instance

/-- **What `publishV3` reads of the server** (persistent; see the file header), with the snapshot
notifier `n`. -/
def srvPubFields (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (c : Loc) (id : w64)
    (a : go_etcd_io.etcd.server.v3.etcdserver.api.membership.Attributes) (cus : List GoString)
    (n : Loc) : IProp GF :=
  iprop(srvMemberAttrs s c id a cus ∗ (∃ cid : w64, membership.clusterCid c cid) ∗
    (∃ l : Loc, srvLgAddr s ↦□ l ∗ ⌜l ≠ null⌝) ∗
    (∃ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
      srvCtxAddr s ↦□ (GoInterface.ok ctx) ∗ context.isContext ctx cd) ∗
    (∃ st : Loc, srvStoppingAddr s ↦□ st ∗ stopChan st) ∗
    srvSnapAppliedAddr s ↦□ n ∗
    (∃ F : mvcc.Log, mvcc.idxCert E.γ.idx F) ∗
    □ (|==> idCred ρ.ids 1) ∗
    ⌜threadBound GF < Int.toNat sync.rwmutex.actualMaxReaders⌝)

instance srvPubFields_persistent (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (c : Loc) (id : w64)
    (a : go_etcd_io.etcd.server.v3.etcdserver.api.membership.Attributes) (cus : List GoString)
    (n : Loc) : Persistent (srvPubFields s E ρ c id a cus n) := by
  unfold srvPubFields; infer_instance

/-- The pool's namespace. -/
def pubPoolN : Namespace := nroot.@"srvPublishPool"

/-- **The reader-slot pool of the snapshot check's goroutines** (see the file header): `k` slots
of `n`'s mutex out, against `k` deposited thread tokens (and `k` receipts, `ownToks γ 1` each,
with the drawers), `K - k` slots in. -/
def pubPoolInv (n : Loc) (γ : GName) (K : Nat) : IProp GF :=
  iprop(∃ k : Nat, ⌜k ≤ K⌝ ∗ threadToks k ∗ ownTokAuth γ k ∗
    [∗list] _x ∈ List.replicate (K - k) (), notifyReader n)

/-- The flag `publishedBySnapshot`'s namespace. -/
def pubFlagN : Namespace := nroot.@"srvPublishFlag"

/-- **The attempt's flag `publishedBySnapshot`** (`atomic.Bool` at `f`): set only with the
evidence that the membership holds the attributes. -/
def pubFlagInv (f c : Loc) (id : w64)
    (a : go_etcd_io.etcd.server.v3.etcdserver.api.membership.Attributes) (cus : List GoString) :
    IProp GF :=
  iprop(∃ b : Bool, sync.atomic.ownBool f (DFrac.own 1) b ∗
    ⌜b = true → membership.attrsHeld c id a.Name' cus⌝)

/-- **The construction premise's part for `publishV3`** (`isServerBuilt`'s `Hpub`): the
member's identity and attributes as `NewServer` set them, and the right to close `s.readych`
(a fresh channel, never closed but by `publishV3`). -/
def srvPubBuilt (s : Loc) : IProp GF :=
  iprop(∃ (c : Loc) (id : w64) (a : go_etcd_io.etcd.server.v3.etcdserver.api.membership.Attributes)
      (cus : List GoString),
    srvMemberAttrs s c id a cus ∗ srvReady s iprop(⌜pubDone c id a cus⌝) .Pending)

end defs


end EtcdGrove
end Perennial
