/-
**The writers' vocabulary** (D23, 2026-10-20). Lean-first (no Rocq counterpart).

* `wkKV γr`: the client's half of the KV ghost state (`etcdKV`), in an invariant of the program's,
  so that each writer's update (`kvOpAu1` of its put, `put_au`) can fire at the server's apply;
  the workload lets the client deposit every put of the plan (`putOk`).
* `okFact E p`: what the program knows of a successful Put it logged, `p` (its reply's header
  revision, key and value): the revision is at least `2` and is the put of the key and value
  (`revAt`), from the reply (`okFact_of_reply`: `putReplied`'s certificate of the log after, whose
  last revision is the put's change, `client.put_applied_log`).
* `wsInv w E`: the lock invariant of the log `w`: its slice of successful Puts, each with
  `okFact`.
* `client_Put_rev`: `cli.Put(ctx, key, val)` by `New`'s client configured for one attempt
  (`client_put_end_to_end` through the `KV` field, as linkv's `client_Put_once`), with the
  reply's message and `putReplied`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.watchkv.Defs
public import Proof.go_etcd_io.etcd.client.v3.CacheClient
public import Proof.go_etcd_io.etcd.client.v3.Results

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace watchkv

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver
open github_com.mit_pdos.etcd_grove.examples.watchkv

/-- The program's KV invariant's namespace. -/
def wkN : Namespace := nroot .@ "watchkv_kv"

theorem wkN_mask : (↑wkN : CoPset) ⊆ (⊤ \ ↑(nroot.@"raft_commit")) \ ↑(nroot.@"server_kv") := by
  intro p hp
  rw [Iris.Std.LawfulSet.mem_diff, Iris.Std.LawfulSet.mem_diff]
  exact ⟨⟨CoPset.mem_full, fun h' => ndot_ne_disjoint nroot (by decide) p ⟨hp, h'⟩⟩,
    fun h' => ndot_ne_disjoint nroot (by decide) p ⟨hp, h'⟩⟩

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- The client's `etcdKV`, in the program's invariant. -/
def wkKV (γr : ReadNames) : IProp GF := inv wkN (∃ σ : KVState, etcdKV γr.kv σ)

instance wkKV_persistent (γr : ReadNames) : Persistent (wkKV (GF := GF) γr) := by
  unfold wkKV; infer_instance

/-- The plan's put of `k ↦ v` as the client sends it. -/
theorem putOk_putKeyOp (P : List (GoString × GoString)) (k v : GoString) (h : (k, v) ∈ P) :
    putOk P (client.putKeyOp k v) := by
  unfold putOk client.putKeyOp txn.putOpOf
  simp [h]

/-- **A writer's update** for the put of `k ↦ v` (fired at most once): it steps the state. -/
theorem put_au (γr : ReadNames) (P : List (GoString × GoString)) (hwl : γr.kv.wl = workload P)
    (k v : GoString) (h : (k, v) ∈ P) :
    wkKV (GF := GF) γr ⊢ kvOpAu1 γr.kv (.put (client.putKeyOp k v)) (fun _ => iprop(True)) := by
  have Hm := wkN_mask
  iintro #Hinv
  unfold kvOpAu1 kvAu1
  isplitr
  · ipureintro; rw [hwl]; exact Or.inl ⟨_, rfl, putOk_putKeyOp P k v h⟩
  iauintro
  unfold atomic_acc
  iunfold wkKV at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%σ, Hσ⟩
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ((⊤ \ ↑srvRaftN) \ ↑kvN) \ ↑wkN from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists σ
  iframe Hσ
  isplit
  · iintro Hσ
    imod Hclose2 with -
    imod Hclose $$ [Hσ] with -
    · inext; iexists σ; iexact Hσ
    imodintro; itrivial
  · iintro Hσ
    imod Hclose2 with -
    imod Hclose $$ [Hσ] with -
    · inext; iexists _; iexact Hσ
    imodintro; itrivial

/-- **What the program knows of a successful Put it logged** (persistent; see the file header). -/
def okFact (E : apply.AEnv GF) (p : wrec) : IProp GF :=
  iprop(⌜2 ≤ sint.Z p.rev'⌝ ∗ revAt E (sint.Z p.rev').toNat p.key' p.val')

instance okFact_persistent (E : apply.AEnv GF) (p : wrec) : Persistent (okFact (GF := GF) E p) := by
  unfold okFact; infer_instance

/-- **A successful Put's reply gives `okFact`** of its revision, key and value. -/
theorem okFact_of_reply (E : apply.AEnv GF) (γr : ReadNames) (F : mvcc.Log) (k v : GoString)
    (Q : KVState → IProp GF) (cid mid : w64) (m : PutRespM) :
    client.putReplied E γr F (client.putKeyOp k v) Q cid mid m ⊢
      okFact E ⟨m.hdr.revision, k, v⟩ := by
  iintro H
  unfold client.putReplied
  icases H with ⟨%hm, %x, %x', %l, %skip, %Hp, #Hc, -, -, -, -⟩
  obtain ⟨hstep, hrev, -, -, -, -, h2, h4⟩ := Hp
  have hlog := client.put_applied_log _ hm x x' l skip hstep
  unfold okFact revAt
  simp only
  rw [hrev]
  have hz : sint.Z (W64 (x.log.length : Int)) = x.log.length := by word
  isplitr
  · ipureintro; rw [hz]; omega
  iexists x'.log
  isplitr
  · iapply mvcc.idxCert_sealed; iexact Hc
  ipureintro
  rw [hz, hlog]
  simp [client.putKeyOp, txn.putOpOf, txn.putChangeOf, txn.putValOf, txn.putLeaseOf]

/-- **The log's lock invariant** (see the file header). -/
def wsInv (w : Loc) (E : apply.AEnv GF) : IProp GF :=
  iprop(∃ (sl : GoSlice) (oks : List wrec),
    structFieldRef github_com.mit_pdos.etcd_grove.examples.watchkv.writes go!"ok" w ↦ sl ∗ sl ↦* oks ∗ ownSliceCap wrec sl (DFrac.own 1) ∗
    □ [∗list] p ∈ oks, okFact E p)

end defs

section put
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- `cli.Put(ctx, key, val)` by `New`'s client configured for one attempt, with an update fired at
most once (see the file header): `nil`, the reply's message and `putReplied`; or an error. -/
theorem client_Put_rev [go_etcd_io.etcd.cache.v3.Assumptions] (cl : Loc) (ep : GoString)
    (V : client.WEnv GF) (E : apply.AEnv GF) (γr : ReadNames) (cid mid : w64) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (key val : GoString) (sl : GoSlice)
    (Q : KVState → IProp GF) (F : mvcc.Log) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isNewClient cl [ep] V ∗
        clientKVOnce cl [ep] ∗
        isGrpcRpc ep go!"/etcdserverpb.KV/Put" (client.etcdPutSpec E γr cid mid) ∗
        ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAt sl [] ∗
        kvOpAu1 γr.kv (.put (client.putKeyOp key val)) Q ∗ mvcc.idxCert E.γ.idx F }}
      (App (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
          go!"Put")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #val)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (⌜err = GoInterface.nil⌝ ∗ ∃ m : PutRespM, putRespMsg resp m ∗
          client.putReplied E γr F (client.putKeyOp key val) Q cid mid m) ∨
          ⌜err ≠ GoInterface.nil⌝ }} := by
  iintro %Φ ⟨#Pc, #Hcl, #Hone, #Hrpc, #Hctx, #Hce, #Hopts, Hau, #HF⟩ HΦ
  iunfold isNewClient at Hcl
  icases Hcl with ⟨-, -, ⟨%api, #Hkvf, #Hkv⟩, -⟩
  iunfold clientKVOnce at Hone
  icases Hone with ⟨%api', #Hkvf', #Honce⟩
  icombine Hkvf Hkvf' gives %Heq
  have Heq' : api = api' := by
    unfold interface.mkOk at Heq
    simp only [GoInterface.ok.injEq, GoInterfaceOk.mk.injEq, _root_.true_and] at Heq
    exact go.intoVal_inj Heq
  subst Heq'
  rw [go_etcd_io.etcd.client.v3.Client.TypeAssumptions.ptr_Put_unfold.method_unfold]
  wp_pures
  wp_auto
  wp_apply (client.client_put_end_to_end api [ep] E γr cid mid ci cd key val sl Q F) $$ [Hau]
    as %resp %err Hout
  · iframe #
    iunfold client.putAuOk
    iright
    iframe Hau
    iexact Honce
  iapply HΦ
  icases Hout with (⟨%Herr, %m, #Hm, Hr⟩ | ⟨%Herr, -⟩)
  · ileft
    isplitl []
    · ipureintro; exact Herr
    iexists m
    iframe Hm Hr
  · iright
    ipureintro; exact Herr

end put

end watchkv
end EtcdGrove
end Perennial
