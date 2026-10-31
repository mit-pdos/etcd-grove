/-
**The clients' `KV` contracts of a real `*kv` over a connection to etcd's server: the shared
part** (the vertical slice's unit V2b, 2026-10-14; `notes/decisions.md`, "The client contracts
derived: certified floors; the restrictions"). Lean-first, no Rocq counterpart.

The clients state their `KV` contracts (`isEtcdKVTodo`, `isEtcdPutKVTodo`, ...,
`cache/v3/InvEtcdTxn.lean`) over the clients' model `EtcdModel GF`; the server's instance is
`v3rpc.etcdModelOfServer E`. A `*kv` (`kvObjAt api addr`, what `NewKV` returns over a connection
to the server at `addr`, whose KV methods are registered with etcd's specs: `etcd_kv_served`)
meets them at that instance (`ServerKVPut.lean`, `ServerKVGet.lean`, `ServerKVTxn.lean`). What they
share:

* `kvIfaceOf api`: the `clientv3.KV` interface value of the `*kv` `api`; its methods are `kv`'s.
* **The floor of a revision the caller knows etcd has reached** (unit W-M3): in the server's
  model `etcdReached lo` is a log the server certified (`certOk`: the KV model of a committed raft
  prefix) longer than `lo` (`certOk_of_reached`). The caller's update (`kvAnyAu`, from `etcdKV` in
  its own invariant with the state's revision as a monotone counter, `kvAnyAu_of_inv`) turns it
  into a result at the state the request linearizes at, at least that log (`kv_client_floor`):
  a write's at the state of the log it met, a linearizable read's at the state of the log read,
  so the answer's revision is at least `lo` (linearizability). The specs' mvcc floor `F` (a
  committed log every answer's log extends, the serializable reads' guarantee) is the read side's
  first certificate (`floor0_of_read`).
* **`context.TODO()`** (`todo_ctx`): a quiet context (`ctxQuiet`: `Err()` is `nil`, the
  `emptyCtx`'s, from Perennial's model of `context`) and `ctxErrClient` at a descriptor whose
  closed flag is `false` for good (`todoCd`), given that `errors.As` can take
  `*rpctypes.EtcdError` as a target (`errors.AsTarget`, a method-set fact `clientErr` carries).
* **Premises** (persistent): `ctxErrClientAll` (every context's `Err()` returns client errors:
  what the contracts at a context need; not derivable from `isContext`, whose `Err()` may return
  any error) and `clientErrsIs` (`clientErrIs` of a client error: what the recipes' `errors.Is`
  needs; not derivable: `errors.isLeafError` says nothing of an `Is` method, gRPC's
  `*status.Error` has one).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.Results
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ClientModel
public import Perennial.Ghost.DGhostVar

@[expose] public section

set_option pp.fullNames true
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace client

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

section defs
variable [GooseExts] [go_gctx : GoGlobalContext]

/-- **The `clientv3.KV` interface value of the `*kv` `api`** (what `NewKV` returns). -/
abbrev kvIfaceOf (api : Loc) : GoInterfaceOk :=
  interface.mk (go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty) #api

end defs

section prem
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **The client's errors are client errors as `errors.Is` sees them** (a premise, persistent; see
the file header). -/
def clientErrsIs : IProp GF :=
  iprop(□ ∀ err : GoInterface, ⌜clientErr err⌝ -∗ clientErrIs err)

instance clientErrsIs_persistent : Persistent (clientErrsIs (GF := GF)) := by
  unfold clientErrsIs; infer_instance

end prem

section todo
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- A descriptor of `context.TODO()` (never done): any names whose closed flag is `false` for
good. -/
abbrev todoCd (γ : context.ContextNames) : context.ContextDesc (IProp GF) :=
  ⟨∅, none, γ, iprop(True)⟩

/-- **`context.TODO()` is quiet**: its `Err()` (the embedded `emptyCtx`'s) returns `nil`. -/
theorem ctxQuiet_todo : ⊢ ctxQuiet (GF := GF) todoCtxVal := by
  unfold ctxQuiet
  iintro !> %Φ HΦ
  wp_method_call
  wp_auto
  wp_method_call
  wp_auto
  iexact HΦ

/-- **`context.TODO()`'s `Err()` returns client errors** (`nil`, always), at a descriptor whose
closed flag is `false` for good. -/
theorem ctxErrClient_todo (hAs : errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty)
    (γ : context.ContextNames) :
    dghostVar (GF := GF) γ.closedGn DFrac.discard false ⊢ ctxErrClient todoCtxVal (todoCd γ) := by
  iintro #Hf
  unfold ctxErrClient
  imodintro
  iintro %cl %Φ Hcl HΦ
  wp_method_call
  wp_auto
  wp_method_call
  wp_auto
  cases cl with
  | Done =>
    iunfold context.ContextClosed at Hcl
    ihave %Hag := dghostVar_agree _ _ _ _ _ $$ Hf Hcl
    simp at Hag
  | _ =>
    iapply HΦ
    · simp only [↓reduceIte]; itrivial
    · ipureintro
      exact ⟨hAs, fun ii h => by cases h⟩
    · iapply go_etcd_io.etcd.cache.v3.statusErrOk_nil
    · iapply go_etcd_io.etcd.cache.v3.errCellOk_nil

/-- **A descriptor for `context.TODO()`** (see the file header): quiet, with `ctxErrClient`. -/
theorem todo_ctx (hAs : errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty) :
    ⊢ |==> ∃ cd : context.ContextDesc (IProp GF),
      ctxOk todoCtxVal cd ∗ ctxErrClient todoCtxVal cd := by
  iintro
  imod dghostVar_alloc (GF := GF) false with ⟨%γc, Hc⟩
  imod dghostVar_persist γc 1 false $$ Hc with #Hc
  imodintro
  iexists (todoCd ⟨γc, γc⟩)
  isplitl []
  · unfold ctxOk
    iright
    iapply ctxQuiet_todo
  iapply ctxErrClient_todo hAs ⟨γc, γc⟩
  iexact Hc

/-- **`context.Background()` is quiet** (item 9, stage 2, 2026-10-18: the adequacy example's
context): its `Err()` (the embedded `emptyCtx`'s) returns `nil`. -/
theorem ctxQuiet_background : ⊢ ctxQuiet (GF := GF) context.backgroundCtxVal := by
  unfold ctxQuiet
  iintro !> %Φ HΦ
  wp_method_call
  wp_auto
  wp_method_call
  wp_auto
  iexact HΦ

/-- **`context.Background()`'s `Err()` returns client errors** (`nil`, always), at a descriptor
whose closed flag is `false` for good (as `ctxErrClient_todo`). -/
theorem ctxErrClient_background
    (hAs : errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty)
    (γ : context.ContextNames) :
    dghostVar (GF := GF) γ.closedGn DFrac.discard false ⊢
      ctxErrClient context.backgroundCtxVal (todoCd γ) := by
  iintro #Hf
  unfold ctxErrClient
  imodintro
  iintro %cl %Φ Hcl HΦ
  wp_method_call
  wp_auto
  wp_method_call
  wp_auto
  cases cl with
  | Done =>
    iunfold context.ContextClosed at Hcl
    ihave %Hag := dghostVar_agree _ _ _ _ _ $$ Hf Hcl
    simp at Hag
  | _ =>
    iapply HΦ
    · simp only [↓reduceIte]; itrivial
    · ipureintro
      exact ⟨hAs, fun ii h => by cases h⟩
    · iapply go_etcd_io.etcd.cache.v3.statusErrOk_nil
    · iapply go_etcd_io.etcd.cache.v3.errCellOk_nil

/-- **A descriptor for `context.Background()`** (as `todo_ctx`): quiet, with `ctxErrClient`. -/
theorem background_ctx (hAs : errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty) :
    ⊢ |==> ∃ cd : context.ContextDesc (IProp GF),
      ctxOk context.backgroundCtxVal cd ∗ ctxErrClient context.backgroundCtxVal cd := by
  iintro
  imod dghostVar_alloc (GF := GF) false with ⟨%γc, Hc⟩
  imod dghostVar_persist γc 1 false $$ Hc with #Hc
  imodintro
  iexists (todoCd ⟨γc, γc⟩)
  isplitl []
  · unfold ctxOk
    iright
    iapply ctxQuiet_background
  iapply ctxErrClient_background hAs ⟨γc, γc⟩
  iexact Hc

end todo

/-! ## A client that does not track the abstract state (2026-10-15, unit T2) -/

section anyAu
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **A step never lowers the state's revision** (a step commits one revision or none). -/
theorem commit_rev (σ : KVState) (cs : List mvcc.Change) : σ.rev ≤ (σ.commit cs).rev := by
  unfold KVState.commit; split <;> simp [KVState.rev]

theorem kvOpStep_rev (op : KVOp) (σ : KVState) : σ.rev ≤ (kvOpStep op σ).rev := by
  cases op <;> simp only [kvOpStep] <;> (repeat' split) <;>
    (first | exact Nat.le_refl _ | exact commit_rev _ _)

/-- **Any operation's update, with the floor of a certified log** (persistent; 2026-10-15, unit
T2; unit W-M3: the floor): what a client that does not track etcd's abstract state hands the
server's specs. For every operation and every log `l` the server certified (`certOk`: the KV
model of a committed raft prefix; `etcdReached`'s logs), the client gets, now, an update whose
result is that the state it linearized at is at least `l` (`l.length ≤ σ.rev + 1`): the committed
KV state extends every certified log, and the state only grows. It has it from `etcdKV` in an
invariant of its own, with the state's revision as a monotone counter (`kvAnyAu_of_inv`). -/
def kvAnyAu (E : apply.AEnv GF) (γ : ReadNames) : IProp GF :=
  iprop(□ ∀ (op : KVOp) (l : mvcc.Log), mvcc.certOk E.γ l ={⊤}=∗
    kvOpAu γ.kv op (fun σ => iprop(⌜l.length ≤ σ.rev + 1⌝)))

/-- A range's update is a read update (a range does not step the state). -/
theorem kvOpAu_range (γk : KVNames) (o : OpFull) (Q : KVState → IProp GF) :
    kvOpAu γk (.range o) Q ⊢ kvReadAu γk Q := by
  have h : kvOpStep (KVOp.range o) = fun σ => σ := by funext σ; rfl
  unfold kvOpAu kvReadAu
  rw [h]

instance kvAnyAu_persistent (E : apply.AEnv GF) (γ : ReadNames) :
    Persistent (kvAnyAu (GF := GF) E γ) := by
  unfold kvAnyAu; infer_instance

/-- The namespace of a client's invariant holding `etcdKV`. -/
def kvClientN : Namespace := nroot .@ "kv_client"

theorem kvClientN_mask : (↑kvClientN : CoPset) ⊆ (⊤ \ ↑srvRaftN) \ ↑kvN :=
  Perennial.mask_ndot_ne2 nroot _ _ _ (by decide) (by decide)

/-- **A client's invariant holding the abstract state** (unit W-M3: with its revision as a
monotone counter at `γm`, so a revision the client saw is a lower bound of every later state). -/
def kvClientInv (γ : ReadNames) (γm : GName) : IProp GF :=
  inv kvClientN iprop(∃ σ : KVState, etcdKV γ.kv σ ∗ monoNatAuthOwn γm 1 σ.rev)

instance kvClientInv_persistent (γ : ReadNames) (γm : GName) :
    Persistent (kvClientInv (GF := GF) γ γm) := by
  unfold kvClientInv; infer_instance

/-- **A client's invariant, allocated** from `etcdKV`. -/
theorem kvClientInv_alloc (γ : ReadNames) (σ : KVState) (Em : CoPset) :
    etcdKV (GF := GF) γ.kv σ ⊢ |={Em}=> ∃ γm : GName, kvClientInv γ γm := by
  iintro Hσ
  imod (mono_nat_own_alloc (GF := GF) σ.rev) with ⟨%γm, Hm, -⟩
  imod inv_alloc kvClientN Em (iprop(∃ σ : KVState, etcdKV γ.kv σ ∗ monoNatAuthOwn γm 1 σ.rev))
    $$ [Hσ Hm] with #Hinv
  · inext; iexists σ; iframe Hσ Hm
  imodintro
  iexists γm
  iunfold kvClientInv
  iexact Hinv

/-- **The floor of a certified log, in the client's counter**: the client's state (in its
invariant) is the committed one, at least the certified log (`kv_cert_floor`); its revision is a
lower bound from now on. -/
theorem kv_client_floor (E : apply.AEnv GF) (γ : ReadNames) (γm : GName) (l : mvcc.Log) :
    ⊢ srvKVInvs (GF := GF) E γ -∗ kvClientInv γ γm -∗ mvcc.certOk E.γ l ={⊤}=∗
      ∃ n : Nat, monoNatLbOwn γm n ∗ ⌜l.length ≤ n + 1⌝ := by
  iintro #Hinvs #Hinv #Hc
  iunfold srvKVInvs at Hinvs
  icases Hinvs with ⟨#HkI, #HcI, #HrI, %Hcok⟩
  iunfold kvClientInv at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%σ, Hσ, Hm⟩
  unfold kvClientN
  imod kv_cert_floor γ.raft γ.kv E.γ Hcok "kv_client" (by decide) (by decide) (by decide) l σ
    $$ HkI HcI HrI Hc Hσ with ⟨Hσ, %Hle⟩
  ihave #Hlb := monoNatLbOwn_get γm 1 σ.rev $$ Hm
  imod Hclose $$ [Hσ Hm] with -
  · inext; iexists σ; iframe Hσ Hm
  imodintro
  iexists σ.rev
  iframe Hlb
  ipureintro; exact Hle

/-- **A range's update, with the floor of a certified log** (persistent; 2026-10-20, cachekv):
`kvAnyAu` at the ranges only, what a get needs (`kv_get_server_r`), which a client has from
`etcdKV` in its invariant (`kvRangeAu_of_inv`). -/
def kvRangeAu (E : apply.AEnv GF) (γ : ReadNames) : IProp GF :=
  iprop(□ ∀ (o : OpFull) (l : mvcc.Log), mvcc.certOk E.γ l ={⊤}=∗
    kvOpAu γ.kv (.range o) (fun σ => iprop(⌜l.length ≤ σ.rev + 1⌝)))

instance kvRangeAu_persistent (E : apply.AEnv GF) (γ : ReadNames) :
    Persistent (kvRangeAu (GF := GF) E γ) := by
  unfold kvRangeAu; infer_instance

/-- `kvAnyAu` gives the ranges' updates. -/
theorem kvAnyAu_range (E : apply.AEnv GF) (γ : ReadNames) :
    kvAnyAu (GF := GF) E γ ⊢ kvRangeAu E γ := by
  iintro #H
  iunfold kvAnyAu at H
  iunfold kvRangeAu
  iintro !> %o %l #Hc
  iapply H $$ %(KVOp.range o) %l Hc

/-- **`kvRangeAu` from `etcdKV` in the client's invariant** (`kvAnyAu_of_inv` at the ranges). -/
theorem kvRangeAu_of_inv (E : apply.AEnv GF) (γ : ReadNames) (γm : GName) :
    srvKVInvs E γ ∗ kvClientInv γ γm ⊢ kvRangeAu (GF := GF) E γ := by
  have Hm := kvClientN_mask
  iintro ⟨#Hinvs, #Hinv⟩
  iunfold kvRangeAu
  iintro !> %o %l #Hc
  imod kv_client_floor E γ γm l $$ Hinvs Hinv Hc with ⟨%n, #Hlb, %Hn⟩
  imodintro
  iunfold kvOpAu
  iunfold kvAu
  iintro !>
  iauintro
  unfold atomic_acc
  iunfold kvClientInv at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%σ, Hσ, Hmn⟩
  ihave %Hv := monoNatLbOwn_valid γm 1 σ.rev n $$ Hmn Hlb
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  iexists σ
  iframe Hσ
  isplit
  · iintro Hσ
    imod Hmask with -
    imod Hclose $$ [Hσ Hmn] with -
    · inext; iexists σ; iframe Hσ Hmn
    imodintro
    itrivial
  · iintro Hσ
    imod Hmask with -
    imod (mono_nat_own_update (GF := GF) (γ := γm) (kvOpStep (.range o) σ).rev
      (kvOpStep_rev (.range o) σ)) $$ Hmn with ⟨Hmn, -⟩
    imod Hclose $$ [Hσ Hmn] with -
    · inext; iexists (kvOpStep (.range o) σ); iframe Hσ Hmn
    imodintro
    iintro !>
    ipureintro
    omega

end anyAu

section floor
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **A certified log for a revision etcd has reached** (unit W-M3; see the file header): in the
server's model `etcdReached lo` is a log the server certified (`certOk`) longer than `lo`, or
`lo ≤ 0`, when `NewStore`'s two revisions (certified for free: `certOk`'s first case) will do. -/
theorem certOk_of_reached (E : apply.AEnv GF) (lo : w64) :
    etcdReached (EM := v3rpc.etcdModelOfServer E) lo ⊢
      ∃ l : mvcc.Log, mvcc.certOk E.γ l ∗ ⌜sint.Z lo < l.length⌝ := by
  iintro #Hr
  unfold etcdReached
  icases Hr with (%Hle | ⟨%r', %Hle, #Hat⟩)
  · iexists [[], []]
    isplitl
    · unfold mvcc.certOk; ileft; ipureintro; simp
    · ipureintro; simp; omega
  · rw [v3rpc.etcdModelOfServer_etcdReachedAt]
    iunfold v3rpc.srvReachedAt at Hat
    icases Hat with ⟨%l, #Hc, %Hlt⟩
    iexists l
    iframe Hc
    ipureintro; omega

/-- **The read side's first certificate** (`isServerRead`'s: `NewStore`'s two revisions, a
committed log every request may take as its floor `F`; unit W-M3: the clients' floors come from
their updates, `kvAnyAu`, so the specs' mvcc floor is this one). -/
theorem floor0_of_read (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) :
    isServerRead (GF := GF) s E γr ⊢ ∃ F : mvcc.Log, mvcc.idxCert E.γ.idx F ∗ ⌜2 ≤ F.length⌝ := by
  iintro #Hsrd
  iunfold isServerRead at Hsrd
  icases Hsrd with ⟨%v, Hsrd⟩
  iunfold srvReadFieldsAt at Hsrd
  icases Hsrd with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨%F0, #HF0, %HF02⟩, -⟩
  iexists F0
  iframe HF0
  ipureintro; exact HF02.1

end floor

end client
end EtcdGrove
end Perennial
