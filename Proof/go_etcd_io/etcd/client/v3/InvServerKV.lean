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
* **The floor of a revision the caller knows etcd has reached** (`floor_of_reached`): in the
  server's model `etcdReached lo` is a certified log of revision `lo` at least (or `lo ≤ 0`, when
  the server's first certificate, `NewStore`'s two revisions, will do). The caller hands it to the
  request (`etcdPutSpec`'s `∃ F`, ...): every answer's log extends it, so its revision is at least
  `lo` (linearizability).
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
variable [ext : FfiSyntax] [go_gctx : GoGlobalContext]

/-- **The `clientv3.KV` interface value of the `*kv` `api`** (what `NewKV` returns). -/
abbrev kvIfaceOf (api : Loc) : GoInterfaceOk :=
  interface.mk (go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty) #api

end defs

section prem
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **Every context's `Err()` returns client errors** (a premise, persistent; see the file
header): `ctxErrClient` for every `isContext`. -/
def ctxErrClientAll : IProp GF :=
  iprop(□ ∀ (ctx : GoInterfaceOk) (cs : context.ContextDesc (IProp GF)),
    context.isContext ctx cs -∗ ctxErrClient ctx cs)

instance ctxErrClientAll_persistent : Persistent (ctxErrClientAll (GF := GF)) := by
  unfold ctxErrClientAll; infer_instance

/-- **The client's errors are client errors as `errors.Is` sees them** (a premise, persistent; see
the file header). -/
def clientErrsIs : IProp GF :=
  iprop(□ ∀ err : GoInterface, ⌜clientErr err⌝ -∗ clientErrIs err)

instance clientErrsIs_persistent : Persistent (clientErrsIs (GF := GF)) := by
  unfold clientErrsIs; infer_instance

end prem

section todo
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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

end todo

/-! ## A client that does not track the abstract state (2026-10-15, unit T2) -/

section anyAu
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **Any operation's update, with no result** (persistent): what a client that does not track
etcd's abstract state hands the server's specs (`kvOpAu op` with `Q` trivial, for every
operation). It has it from `etcdKV` in an invariant of its own (`kvAnyAu_of_inv`). -/
def kvAnyAu (γ : ReadNames) : IProp GF :=
  iprop(□ ∀ op : KVOp, kvOpAu γ.kv op (fun _ => iprop(True)))

instance kvAnyAu_persistent (γ : ReadNames) : Persistent (kvAnyAu (GF := GF) γ) := by
  unfold kvAnyAu; infer_instance

/-- The namespace of a client's invariant holding `etcdKV`. -/
def kvClientN : Namespace := nroot .@ "kv_client"

theorem kvClientN_mask : (↑kvClientN : CoPset) ⊆ (⊤ \ ↑srvRaftN) \ ↑kvN := by
  intro p hp
  rw [Iris.Std.LawfulSet.mem_diff, Iris.Std.LawfulSet.mem_diff]
  exact ⟨⟨CoPset.mem_full, fun h' => ndot_ne_disjoint nroot (by decide) p ⟨hp, h'⟩⟩,
    fun h' => ndot_ne_disjoint nroot (by decide) p ⟨hp, h'⟩⟩

/-- **`kvAnyAu` from `etcdKV` in an invariant**: every update opens the invariant, hands the
state over and takes the stepped state back. -/
theorem kvAnyAu_of_inv (γ : ReadNames) :
    inv kvClientN iprop(∃ σ : KVState, etcdKV γ.kv σ) ⊢ kvAnyAu (GF := GF) γ := by
  have Hm := kvClientN_mask
  iintro #Hinv
  iunfold kvAnyAu
  iintro !> %op
  iunfold kvOpAu
  iunfold kvAu
  iintro !>
  iauintro
  unfold atomic_acc
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%σ, Hσ⟩
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  iexists σ
  iframe Hσ
  isplit
  · iintro Hσ
    imod Hmask with -
    imod Hclose $$ [Hσ] with -
    · inext; iexists σ; iexact Hσ
    imodintro
    itrivial
  · iintro Hσ
    imod Hmask with -
    imod Hclose $$ [Hσ] with -
    · inext; iexists (kvOpStep op σ); iexact Hσ
    imodintro
    iintro !>
    itrivial

end anyAu

section floor
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **The floor of a revision etcd has reached** (see the file header): in the server's model,
`etcdReached lo` gives a certified log `F` longer than `lo`, of `NewStore`'s two revisions at least
(for `lo ≤ 0`, the server's first certificate). -/
theorem floor_of_reached (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) (lo : w64) :
    isServerRead s E γr ∗ etcdReached (EM := v3rpc.etcdModelOfServer E) lo ⊢
      ∃ F : mvcc.Log, mvcc.idxCert E.γ.idx F ∗ ⌜sint.Z lo < F.length ∧ 2 ≤ F.length⌝ := by
  iintro ⟨#Hsrd, #Hr⟩
  iunfold isServerRead at Hsrd
  icases Hsrd with ⟨%v, Hsrd⟩
  iunfold srvReadFieldsAt at Hsrd
  icases Hsrd with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨%F0, #HF0, %HF02⟩, -⟩
  unfold etcdReached
  icases Hr with (%Hle | ⟨%r', %Hle, #Hat⟩)
  · iexists F0
    iframe HF0
    ipureintro; omega
  · rw [v3rpc.etcdModelOfServer_etcdReachedAt]
    iunfold v3rpc.srvReachedAt at Hat
    icases Hat with ⟨%F, #HF, %Hlt⟩
    ihave %Hp := mvcc.idxCert_prefix E.γ.idx F F0 $$ [$HF $HF0]
    rcases Hp with h | h
    · iexists F0
      iframe HF0
      ipureintro; have := h.length_le; omega
    · iexists F
      iframe HF
      ipureintro; have := h.length_le; omega

/-- The store's size premise of the read path (`storeSmall`, the server's). -/
theorem storeSmall_of_read (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) :
    isServerRead (GF := GF) s E γr ⊢ storeSmall E.γ := by
  iintro #Hsrd
  iunfold isServerRead at Hsrd
  icases Hsrd with ⟨%v, Hsrd⟩
  iunfold srvReadFieldsAt at Hsrd
  icases Hsrd with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hsm, -⟩
  iexact Hsm

/-- **The state a read linearized at, in the clients' model** (2026-10-15, unit T2: how the
abstract state `σ` meets the vertical slice's `EtcdModel` instance): a linearizable range's reply
gives `□ Q σ` at the state `σ` of a certified log (`kvStateOf`), and that log's state at its last
revision, restricted to any prefix, is etcd's state at `σ.rev` in the server's model
(`etcdState_of_cert_last`): `etcdState (W64 σ.rev) pfx (txn.underPfx pfx σ.kvs)`, persistent and well
formed. -/
theorem rangeReply_etcdState (E : apply.AEnv GF) (γr : ReadNames) (c cid mid : w64) (o : OpFull)
    (F : mvcc.Log) (Q : KVState → IProp GF) (m : RangeRespM) (pfx : GoString)
    (hser : o.base.serializable = false) :
    storeSmall E.γ ∗ rangeReplyOk E γr c F o cid mid Q m ⊢
      ∃ σ : KVState, □ Q σ ∗
        □ etcdState (self := v3rpc.etcdModelOfServer E) (W64 (σ.rev : Int)) pfx
          (txn.underPfx pfx σ.kvs) ∗ ⌜EtcdStateWf pfx (txn.underPfx pfx σ.kvs)⌝ := by
  iintro ⟨#Hsm, #H⟩
  iunfold rangeReplyOk at H
  simp only [hser, Bool.false_eq_true, ↓reduceIte]
  icases H with ⟨%l, #Hcert, %Hl, -, #HQ⟩
  obtain ⟨hlen, hlen', -⟩ := Hl
  ihave ⟨#Hst, %Hwf⟩ := v3rpc.etcdState_of_cert_last E l pfx hlen hlen' $$ [$Hsm $Hcert]
  iexists kvStateOf l
  iframe HQ
  have hr : W64 ((l.length : Int) - 1) = W64 (((kvStateOf l).rev : Nat) : Int) := by
    unfold kvStateOf; simp only; congr 1; omega
  rw [← hr, show (kvStateOf l).kvs = mvcc.stateAfter l from rfl]
  iframe Hst
  ipureintro; exact Hwf

end floor

end client
end EtcdGrove
end Perennial
