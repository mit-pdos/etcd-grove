/-
Lean-first (no Rocq counterpart).

# linkvtxn: `call`'s client calls (linkv-txn stage F)

`call`'s calls through `New`'s client (its `KV` field, as `linkv/Apply.lean`'s), each stated with
the state `σ` its update fired at and the reply's fields as functions of `σ` (what
`Reply.lean`'s outputs take):

- `client_Get_st`, `client_List_st`: a linearizable get of one key, a list of `[listFrom,
  listTo)`, with a read update or none: `□ Q σ`, the reply's key-values the state's of the key
  (of the range), its header revision `σ`'s (`rangeReply_state'`);
- `client_Put_st`, `client_Delete_st`: a put, a delete, with an update fired at most once on the
  one-attempt client: `Q σ`, the reply's header revision (and count) the step's at `σ`;
- `client_Txn_st` (`cli.Txn(ctx)`: the builder, made from the client's `*kv`), and
  `txn_Commit_st`: a transaction the builder holds as the model's (`clientTxn`), with an update
  fired at most once (writing) or a read update or none (read-only): the reply's verdict, its
  responses and revision the server's run at `σ` (`client.client_txn_value`,
  `client.client_txn_value_ro`).

Each also bounds `σ`'s revision below `2^63` (the replies' logs are below it).
`callUpd`/`callRes`: the update a call of the model input `i` takes, and the result it gives.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkvtxn.Reply
public import Proof.go_etcd_io.etcd.client.v3.ClientPutGet
public import Proof.go_etcd_io.etcd.client.v3.Link

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkvtxn

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open go_etcd_io.etcd.server.v3.etcdserver mvcc

/-! ## Pure part -/

section pure
variable [ext : FfiSyntax]

/-- A list as `cli.Get(ctx, listFrom, WithRange(listTo))` sends it. -/
theorem rangeWireOf_list :
    rangeWireOf (opGetModel listFrom [withRangeM listTo]) = linkv.listOp listFrom listTo := rfl

/-- **A list selects the state's key-values of its range** (pure): no `More`. -/
theorem srvRangeOk_list (s kvs : List EtcdKv) (more : Bool)
    (h : txn.srvRangeOk (linkv.listOp listFrom listTo) s kvs more) :
    kvs = s.filter (fun v => inRange listFrom listTo v.key) ∧ more = false := by
  obtain ⟨L, hsort, hmore, hkvs⟩ := h
  have hpre : txn.srvPre (linkv.listOp listFrom listTo) s =
      s.filter (fun v => inRange listFrom listTo v.key) := by
    have hr : txn.kvRead false = id := by funext v; simp [txn.kvRead]
    unfold txn.srvPre
    simp [txn.rangeLimitOf, txn.hasRevFilters, mvcc.limitOf, mvcc.takeLimit, txn.fastKeysOnly,
      rangeIn, hr]
    apply List.filter_congr
    intro v _
    simp [kvFilterOk]
  have hord : (linkv.listOp listFrom listTo).effSortOrder = W64 0 := by
    simp [OpFull.effSortOrder]
  have hL : L = txn.srvPre (linkv.listOp listFrom listTo) s := by
    obtain ⟨-, -, -, h4⟩ := hsort
    exact h4 (by rw [hord]; decide) (by rw [hord]; decide)
  have hm : txn.srvMore (linkv.listOp listFrom listTo) L = false := by
    simp [txn.srvMore]
  refine ⟨?_, by rw [hmore, hm]⟩
  rw [hkvs]
  unfold txn.srvTrunc
  rw [hm, hL, hpre]
  have hid : txn.respKv (linkv.listOp listFrom listTo) = id := by funext v; simp [txn.respKv]
  simp [hid]

theorem txnNoZeroEnd_txnOf (cs : List (linkv.MCmp GoString GoString))
    (t e : List (linkv.MOp GoString GoString)) : txnNoZeroEnd (linkv.txnOf cs t e) := by
  have hops : ∀ ops : List (linkv.MOp GoString GoString), txnOpsNoZeroEnd (ops.map linkv.tOpOf) := by
    intro ops
    induction ops with
    | nil => simp [txnOpsNoZeroEnd]
    | cons op ops ih =>
      simp only [List.map_cons, txnOpsNoZeroEnd]
      refine ⟨?_, ih⟩
      cases op <;> simp [linkv.tOpOf, txnOpNoZeroEnd, txn.rangeOpOf, txn.deleteOpOf, OpFull.newOp,
        OpModel.zero]
  refine ⟨?_, hops t, hops e⟩
  intro c hc
  simp only [linkv.txnOf, List.mem_map] at hc
  obtain ⟨c', -, rfl⟩ := hc
  cases c' <;> simp [linkv.cmpOf]

theorem irrNoZeroEnd_txnOf (cs : List (linkv.MCmp GoString GoString))
    (t e : List (linkv.MOp GoString GoString)) : irrNoZeroEnd (irrTxn (linkv.txnOf cs t e)) := by
  refine ⟨fun o h => by simp [irrTxn, apply.irrEmpty] at h,
    fun o h => by simp [irrTxn, apply.irrEmpty] at h, fun t' h => ?_⟩
  simp only [irrTxn, Option.some.injEq] at h
  subst h
  exact txnNoZeroEnd_txnOf cs t e

theorem txnReadonly_txnOf (cs : List (linkv.MCmp GoString GoString))
    (t e : List (linkv.MOp GoString GoString)) :
    txn.txnReadonly (linkv.txnOf cs t e) = !(linkv.MIn.txn cs t e).isWrite := by
  have h : ∀ ops : List (linkv.MOp GoString GoString),
      (ops.map linkv.tOpOf).all txn.opIsGet = !ops.any linkv.MOp.isWrite := by
    intro ops
    induction ops with
    | nil => rfl
    | cons op ops ih =>
      simp only [List.map_cons, List.all_cons, List.any_cons, ih, Bool.not_or]
      cases op <;> rfl
  simp only [txn.txnReadonly, linkv.txnOf, List.all_append, h, linkv.MIn.isWrite, Bool.not_or]

theorem clientTxn_plain (cs : List (linkv.MCmp GoString GoString))
    (t e : List (linkv.MOp GoString GoString)) : client.TxnModel.plain (clientTxn cs t e) := by
  refine ⟨fun op hop => ?_, fun op hop => ?_⟩ <;>
  · simp only [clientTxn, List.mem_map] at hop
    obtain ⟨m, -, rfl⟩ := hop
    cases m <;> trivial

theorem txnModelIn_txnOf (cs : List (linkv.MCmp GoString GoString))
    (t e : List (linkv.MOp GoString GoString)) : client.txnModelIn (linkv.txnOf cs t e) := by
  intro o ho
  simp only [linkv.txnOf, List.mem_append, List.mem_map] at ho
  rcases ho with ⟨m, -, hm⟩ | ⟨m, -, hm⟩ <;>
  · cases m <;> simp only [linkv.tOpOf, reduceCtorEq, TxnOp.get.injEq] at hm
    subst hm
    refine ⟨rfl, ?_⟩
    simp [txn.cutEarly, OpFull.effSortOrder, txn.rangeOpOf, OpFull.newOp, OpModel.zero]

/-- **An input `Gen` may return** (`ValidIn`), its transactions not empty: a transaction with no
operations is served without a linearizable read (`issues/etcd-txn-empty-serializable.md`). -/
def GenIn (x : github_com.mit_pdos.etcd_grove.examples.linkvtxn.Input) : Prop :=
  ValidIn x ∧ ∀ cs t e, decIn x = some (.txn cs t e) → t ++ e ≠ []

theorem txnSerializable_txnOf (cs : List (linkv.MCmp GoString GoString))
    (t e : List (linkv.MOp GoString GoString)) (hne : t ++ e ≠ []) :
    txn.txnSerializable (linkv.txnOf cs t e) = false := by
  have h : ∀ ops : List (linkv.MOp GoString GoString), ops ≠ [] →
      (ops.map linkv.tOpOf).all txn.opIsSerGet = false := by
    intro ops hops
    cases ops with
    | nil => exact absurd rfl hops
    | cons op ops =>
      simp only [List.map_cons, List.all_cons, Bool.and_eq_false_iff]
      left
      cases op <;> simp [linkv.tOpOf, txn.opIsSerGet, txn.rangeOpOf, OpFull.newOp, OpModel.zero]
  simp only [txn.txnSerializable, linkv.txnOf, List.all_append, Bool.and_eq_false_iff]
  cases t with
  | nil =>
    right
    exact h e (by simpa using hne)
  | cons a l => left; exact h _ (by simp)

theorem kvOpStep_txnOf_eq (cs : List (linkv.MCmp GoString GoString))
    (t e : List (linkv.MOp GoString GoString)) (σ : KVState) :
    kvOpStep (opIn (.txn cs t e)) σ =
      σ.commit (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs (linkv.txnOf cs t e)).2.1 := by
  simp only [opIn, linkv.opOf, kvOpStep]
  rw [if_pos (by rw [linkv.txnOf_branch]; exact linkv.pathsIgnOk_tOpOf σ.kvs _)]

/-- What a transaction's input decodes. -/
theorem decIn_txn (x : github_com.mit_pdos.etcd_grove.examples.linkvtxn.Input)
    (cs : List (linkv.MCmp GoString GoString)) (t e : List (linkv.MOp GoString GoString))
    (h : decIn x = some (.txn cs t e)) :
    0 ≤ sint.Z x.NCmps' ∧ decAll decCmp (cmpsOfL x) = some cs ∧
      decAll decTOp (thenOfL x) = some t ∧ decAll decTOp (elseOfL x) = some e := by
  rcases decIn_cases x _ h with ⟨-, h'⟩ | ⟨-, h'⟩ | ⟨-, h'⟩ | ⟨-, h'⟩ |
    ⟨-, cs', t', e', h', h1, h2, h3⟩
  all_goals try (cases h')
  refine ⟨?_, h1, h2, h3⟩
  unfold decIn at h
  repeat (split at h; · simp at h)
  split at h
  · rename_i hk; exact hk.2.1
  · cases h

theorem txnOf_branch' (cs : List (linkv.MCmp GoString GoString))
    (t e : List (linkv.MOp GoString GoString)) (b : Bool) :
    (linkv.txnOf cs t e).branch b = (if b then t else e).map linkv.tOpOf := by
  unfold linkv.txnOf TxnModel.branch
  cases b <;> rfl

end pure

/-! ## The updates -/

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The update a call of `i` takes** (see the file header): a write's, fired at most once; a
read's read update, or none. -/
def callUpd (γk : KVNames) (i : MI) (Q : KVState → IProp GF) : IProp GF :=
  if i.isWrite then kvOpAu1 γk (opIn i) Q
  else iprop(⌜Q = fun _ => iprop(True)⌝ ∨ kvReadAu γk Q)

/-- **The result a call of `i` gives** at the state `σ` its update fired at. -/
def callRes (i : MI) (Q : KVState → IProp GF) (σ : KVState) : IProp GF :=
  if i.isWrite then Q σ else iprop(□ Q σ)

/-- **`Apply`'s input** (`lintest`'s `inOk`): a boxed `Input` `Gen` may return (`GenIn`). -/
abbrev linkvInOk (i : GoInterface) : IProp GF :=
  iprop(⌜∃ x : github_com.mit_pdos.etcd_grove.examples.linkvtxn.Input, i = boxIn x ∧ GenIn x⌝)

end defs

/-! ## The calls -/

section proofs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkvtxn.Assumptions]

/-- **What a linearizable range's reply says** (`linkv/Apply.lean`'s `getReply_state`, for any
range at the latest revision): the client's read update fired at a state `σ` (`□ Q σ`) whose
key-values give the reply's (`srvRangeOk`), whose revision is the reply's header revision, and
which is below `2 ^ 63`. -/
theorem rangeReply_state' (E : apply.AEnv GF) (γr : ReadNames) (c cid mid : w64) (o : OpFull)
    (F : mvcc.Log) (Q : KVState → IProp GF) (m : RangeRespM) (hs : o.base.serializable = false)
    (hr : o.base.rev = W64 0) :
    client.rangeReplyOk E γr c F o cid mid Q m ⊢
      ∃ σ : KVState, □ Q σ ∗ ⌜txn.srvRangeOk o σ.kvs m.kvs m.more ∧
        m.hdr.revision = W64 (σ.rev : Int) ∧ σ.rev + 3 < 2 ^ 63⌝ := by
  iintro #H
  iunfold client.rangeReplyOk at H
  icases H with ⟨%l, -, -, %Hl, -, #HQ⟩
  simp only [hs, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨hlen, hlen', hrev, -, -, -, -, hsel, -⟩ := Hl
  have hst : mvcc.stateAt l (sint.nat (mvcc.rangeRev m.hdr.revision o.base.rev)) =
      mvcc.stateAfter l := by
    have h1 : mvcc.rangeRev m.hdr.revision o.base.rev = m.hdr.revision := by
      simp [mvcc.rangeRev, hr]
    rw [h1, hrev]
    have h2 : sint.nat (W64 ((l.length : Int) - 1)) = l.length - 1 := by
      unfold sint.nat; word
    rw [h2, mvcc.stateAt_last]
  rw [hst] at hsel
  iexists kvStateOf l
  iframe HQ
  ipureintro
  refine ⟨hsel, ?_, ?_⟩
  · rw [hrev]
    unfold kvStateOf
    simp only
    congr 1
    omega
  · unfold kvStateOf
    simp only
    omega

/-- `cli.Get(ctx, key)` by `New`'s client, with a read update or none (see the file header). -/
theorem client_Get_st [go_etcd_io.etcd.cache.v3.Assumptions] (cl : Loc) (ep : GoString)
    (V : client.WEnv GF) (E : apply.AEnv GF) (γr : ReadNames) (cid mid : w64) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (key : GoString) (sl : GoSlice) (F : mvcc.Log)
    (Q : KVState → IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isNewClient cl [ep] V ∗
        isGrpcRpc ep go!"/etcdserverpb.KV/Range" (client.etcdRangeSpec E γr cid mid) ∗
        ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAt sl [] ∗ committedAtLeast γr (W64 0) ∗
        (⌜Q = fun _ => iprop(True)⌝ ∨ kvReadAu γr.kv Q) ∗ mvcc.idxCert E.γ.idx F }}
      (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
          go!"Get")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (⌜err = GoInterface.nil⌝ ∗ ∃ (m : RangeRespM) (σ : KVState), rangeRespMsg resp m ∗
          □ Q σ ∗ ⌜m.kvs = σ.kvs.filter (fun v => decide (v.key = key)) ∧
            m.hdr.revision = W64 (σ.rev : Int) ∧ σ.rev + 3 < 2 ^ 63⌝) ∨
          ⌜err ≠ GoInterface.nil⌝ }} := by
  iintro %Φ ⟨#Pc, #Hcl, #Hrpc, #Hctx, #Hce, #Hopts, #Hc, Hau, #HF⟩ HΦ
  iunfold isNewClient at Hcl
  icases Hcl with ⟨-, -, ⟨%api, #Hkvf, #Hkv⟩, -⟩
  rw [go_etcd_io.etcd.client.v3.Client.TypeAssumptions.ptr_Get_unfold.method_unfold]
  wp_pures
  wp_auto
  wp_apply (client.client_get_end_to_end api [ep] E γr (W64 0) cid mid ci cd key sl Q F) $$ [Hau]
    as %resp %err Hout
  · iframe #
    iexact Hau
  iapply HΦ
  icases Hout with (⟨%Herr, %m, #Hm, #Hq⟩ | ⟨%Herr, -⟩)
  · ileft
    isplitl []
    · ipureintro; exact Herr
    ihave Hs := rangeReply_state' E γr (W64 0) cid mid _ F Q m rfl rfl $$ Hq
    icases Hs with ⟨%σ, #HQ, %Hσ⟩
    obtain ⟨hsel, hrev, hb⟩ := Hσ
    iexists m, σ
    iframe Hm HQ
    ipureintro
    exact ⟨(client.srvRangeOk_getKey key _ _ _ hsel).1, hrev, hb⟩
  · iright
    ipureintro; exact Herr

/-- `cli.Get(ctx, listFrom, WithRange(listTo))` by `New`'s client, with a read update or none
(see the file header). -/
theorem client_List_st [go_etcd_io.etcd.cache.v3.Assumptions] (cl : Loc) (ep : GoString)
    (V : client.WEnv GF) (E : apply.AEnv GF) (γr : ReadNames) (cid mid : w64) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (sl : GoSlice) (F : mvcc.Log)
    (Q : KVState → IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isNewClient cl [ep] V ∗
        isGrpcRpc ep go!"/etcdserverpb.KV/Range" (client.etcdRangeSpec E γr cid mid) ∗
        ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAt sl [withRangeM listTo] ∗
        committedAtLeast γr (W64 0) ∗
        (⌜Q = fun _ => iprop(True)⌝ ∨ kvReadAu γr.kv Q) ∗ mvcc.idxCert E.γ.idx F }}
      (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
          go!"Get")) (Val #(GoInterface.ok ci))) (Val #listFrom)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (⌜err = GoInterface.nil⌝ ∗ ∃ (m : RangeRespM) (σ : KVState), rangeRespMsg resp m ∗
          □ Q σ ∗ ⌜m.kvs = σ.kvs.filter (fun v => inRange listFrom listTo v.key) ∧
            m.hdr.revision = W64 (σ.rev : Int) ∧ σ.rev + 3 < 2 ^ 63⌝) ∨
          ⌜err ≠ GoInterface.nil⌝ }} := by
  iintro %Φ ⟨#Pc, #Hcl, #Hrpc, #Hctx, #Hce, #Hopts, #Hc, Hau, #HF⟩ HΦ
  iunfold isNewClient at Hcl
  icases Hcl with ⟨-, -, ⟨%api, #Hkvf, #Hkv⟩, -⟩
  ihave #Hopts' := optsAt_res sl [withRangeM listTo] iprop(True) $$ Hopts
  rw [go_etcd_io.etcd.client.v3.Client.TypeAssumptions.ptr_Get_unfold.method_unfold]
  wp_pures
  wp_auto
  wp_apply (client.client_range_end_to_end api [ep] E γr (W64 0) cid mid ci cd listFrom sl
      [withRangeM listTo] iprop(True) Q F) $$ [Hau] as %resp %err ⟨-, Hout⟩
  · iframe #
    isplitl []
    · rw [show (opGetModel listFrom [withRangeM listTo]).base.sortSet = false from rfl]
      iapply sortNamesIf_false
    isplitl []
    · ipureintro
      refine ⟨?_, rfl⟩
      simp [opGetPanics, opFold, OpFull.newOp, withRangeM]
    icases Hau with (%Hq | #Hau)
    · ileft; ipureintro; exact Hq
    · iright; iframe Hau; ipureintro; rfl
  iapply HΦ
  icases Hout with (⟨%Herr, %m, #Hm, #Hq⟩ | ⟨%Herr, -⟩)
  · ileft
    isplitl []
    · ipureintro; exact Herr
    ihave Hs := rangeReply_state' E γr (W64 0) cid mid _ F Q m rfl rfl $$ Hq
    icases Hs with ⟨%σ, #HQ, %Hσ⟩
    obtain ⟨hsel, hrev, hb⟩ := Hσ
    iexists m, σ
    iframe Hm HQ
    ipureintro
    exact ⟨(srvRangeOk_list _ _ _ hsel).1, hrev, hb⟩
  · iright
    ipureintro; exact Herr

/-- `cli.Put(ctx, key, val)` by `New`'s client configured for one attempt, with an update fired
at most once (see the file header). -/
theorem client_Put_st [go_etcd_io.etcd.cache.v3.Assumptions] (cl : Loc) (ep : GoString)
    (V : client.WEnv GF) (E : apply.AEnv GF) (γr : ReadNames) (cid mid : w64) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (key val : GoString) (sl : GoSlice)
    (Q : KVState → IProp GF) (F : mvcc.Log) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isNewClient cl [ep] V ∗
        clientKVOnce cl [ep] ∗
        isGrpcRpc ep go!"/etcdserverpb.KV/Put" (client.etcdPutSpec E γr cid mid) ∗
        ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAt sl [] ∗
        kvOpAu1 γr.kv (.put (linkv.putOp key val)) Q ∗ mvcc.idxCert E.γ.idx F }}
      (App (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
          go!"Put")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #val)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (⌜err = GoInterface.nil⌝ ∗ ∃ (m : PutRespM) (σ : KVState), putRespMsg resp m ∗ Q σ ∗
          ⌜m.hdr.revision = W64 ((σ.rev + 1 : Nat) : Int) ∧ σ.rev + 4 < 2 ^ 63⌝) ∨
          ⌜err ≠ GoInterface.nil⌝ }} := by
  iintro %Φ ⟨#Pc, #Hcl, #Hone, #Hrpc, #Hctx, #Hce, #Hopts, Hau, #HF⟩ HΦ
  iunfold isNewClient at Hcl
  icases Hcl with ⟨-, -, ⟨%api, #Hkvf, #Hkv⟩, -⟩
  iunfold clientKVOnce at Hone
  icases Hone with ⟨%api', #Hkvf', #Honce⟩
  icombine Hkvf Hkvf' gives %Heq
  have Heq' : api = api' := by
    unfold interface.mkOk at Heq
    simp only [GoInterface.ok.injEq, GoInterfaceOk.mk.injEq, true_and] at Heq
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
    iunfold client.putReplied at Hr
    icases Hr with ⟨%hm, %x, %x', %l, %skip, %Hp, -, -, -, -, HQ⟩
    obtain ⟨-, hrev, -, -, -, -, hlen, hb⟩ := Hp
    iexists m, kvStateOf x.log
    iframe Hm HQ
    ipureintro
    refine ⟨?_, ?_⟩
    · rw [hrev, client.kvStateOf_rev_succ _ hlen]
    · unfold kvStateOf; simp only; omega
  · iright
    ipureintro; exact Herr

/-- `cli.Delete(ctx, key)` by `New`'s client configured for one attempt, with an update fired at
most once (see the file header). -/
theorem client_Delete_st [go_etcd_io.etcd.cache.v3.Assumptions] (cl : Loc) (ep : GoString)
    (V : client.WEnv GF) (E : apply.AEnv GF) (γr : ReadNames) (cid mid : w64) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (key : GoString) (sl : GoSlice)
    (Q : KVState → IProp GF) (F : mvcc.Log) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isNewClient cl [ep] V ∗
        clientKVOnce cl [ep] ∗
        isGrpcRpc ep go!"/etcdserverpb.KV/DeleteRange" (client.etcdDeleteSpec E γr cid mid) ∗
        ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAt sl [] ∗
        kvOpAu1 γr.kv (.deleteRange (linkv.delOp key)) Q ∗ mvcc.idxCert E.γ.idx F }}
      (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
          go!"Delete")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #sl))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (⌜err = GoInterface.nil⌝ ∗ ∃ (m : DelRespM) (σ : KVState), delRespMsg resp m ∗ Q σ ∗
          ⌜m.deleted = W64 ((rangeIn σ.kvs (linkv.delOp key)).length : Int) ∧
            m.hdr.revision = W64 ((kvOpStep (.deleteRange (linkv.delOp key)) σ).rev : Int) ∧
            σ.rev + 4 < 2 ^ 63⌝) ∨
          ⌜err ≠ GoInterface.nil⌝ }} := by
  iintro %Φ ⟨#Pc, #Hcl, #Hone, #Hrpc, #Hctx, #Hce, #Hopts, Hau, #HF⟩ HΦ
  iunfold isNewClient at Hcl
  icases Hcl with ⟨-, -, ⟨%api, #Hkvf, #Hkv⟩, -⟩
  iunfold clientKVOnce at Hone
  icases Hone with ⟨%api', #Hkvf', #Honce⟩
  icombine Hkvf Hkvf' gives %Heq
  have Heq' : api = api' := by
    unfold interface.mkOk at Heq
    simp only [GoInterface.ok.injEq, GoInterfaceOk.mk.injEq, true_and] at Heq
    exact go.intoVal_inj Heq
  subst Heq'
  rw [go_etcd_io.etcd.client.v3.Client.TypeAssumptions.ptr_Delete_unfold.method_unfold]
  wp_pures
  wp_auto
  wp_apply (client.client_delete_end_to_end api [ep] E γr cid mid ci cd key sl Q F) $$ [Hau]
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
    iunfold client.deleteReplied at Hr
    icases Hr with ⟨%hm, %rq', %op', %x, %x', %l, %skip, %Hp, -, -, -, -, HQ⟩
    obtain ⟨-, -, Hz, -, hrev, -, -, hdel, -, -, hlen, hb⟩ := Hp
    have hnz : irrNoZeroEnd (irrDeleteRange (linkv.delOp key)) := by
      refine ⟨fun o' h => by simp [irrDeleteRange, apply.irrEmpty] at h, fun o' h => ?_,
        fun t h => by simp [irrDeleteRange, apply.irrEmpty] at h⟩
      simp only [irrDeleteRange, Option.some.injEq] at h
      subst h
      simp [txn.deleteOpOf, OpFull.newOp, OpModel.zero]
    have hop : op' = linkv.delOp key := Hz hnz
    subst hop
    iexists m, kvStateOf x.log
    iframe Hm HQ
    ipureintro
    refine ⟨hdel, ?_, ?_⟩
    · rw [hrev]
      unfold kvOpStep
      rw [client.kvStateOf_commit_rev _ _ hlen]
      rfl
    · unfold kvStateOf; simp only; omega
  · iright
    ipureintro; exact Herr

/-- `cli.Txn(ctx)` by `New`'s client: the builder, empty, made from the client's `*kv` (which,
configured for one attempt, fires its update at most once). -/
theorem client_Txn_st [go_etcd_io.etcd.cache.v3.Assumptions] (cl : Loc) (ep : GoString)
    (V : client.WEnv GF) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isNewClient cl [ep] V ∗
        clientKVOnce cl [ep] ∗ ctxOk ci cd ∗ ctxErrClient ci cd }}
      (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
          go!"Txn")) (Val #(GoInterface.ok ci)))
    {{ (t : GoInterface), RET #t; ∃ tp : Loc,
        ⌜t = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty) #tp⌝ ∗
        txnObjAt tp [ep] ci cd TxnBuild.empty ∗ ∃ api : Loc, txnKvIs tp api ∗ kvOnce api [ep] }} := by
  iintro %Φ ⟨#Pc, #Hcl, #Hone, #Hctx, #Hce⟩ HΦ
  iunfold isNewClient at Hcl
  icases Hcl with ⟨-, -, ⟨%api, #Hkvf, #Hkv⟩, -⟩
  iunfold clientKVOnce at Hone
  icases Hone with ⟨%api', #Hkvf', #Honce⟩
  icombine Hkvf Hkvf' gives %Heq
  have Heq' : api = api' := by
    unfold interface.mkOk at Heq
    simp only [GoInterface.ok.injEq, GoInterfaceOk.mk.injEq, true_and] at Heq
    exact go.intoVal_inj Heq
  subst Heq'
  rw [go_etcd_io.etcd.client.v3.Client.TypeAssumptions.ptr_Txn_unfold.method_unfold]
  wp_pures
  wp_auto
  wp_apply (client.v3.kv.wp_Txn api [ep] ci cd) as %t ⟨%tp, %Ht, Hobj, #Hkt⟩
  · iframe #
  iapply HΦ
  iexists tp
  iframe Hobj
  isplitr
  · ipureintro; exact Ht
  iexists api
  iframe #

/-- **`Commit()` of the model's transaction** (see the file header): its update by its kind. -/
theorem txn_Commit_st [go_etcd_io.etcd.cache.v3.Assumptions] (tp : Loc) (ep : GoString) (E : apply.AEnv GF) (γr : ReadNames)
    (cid mid : w64) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (b : TxnBuild)
    (F : mvcc.Log) (Q : KVState → IProp GF) (cs : List (linkv.MCmp GoString GoString))
    (t e : List (linkv.MOp GoString GoString)) (hb : b.model = clientTxn cs t e)
    (hne : t ++ e ≠ []) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ txnObjAt tp [ep] ci cd b ∗
        isGrpcRpc ep go!"/etcdserverpb.KV/Txn" (client.etcdTxnSpec E γr γr cid mid) ∗
        committedAtLeast γr (W64 0) ∗ mvcc.idxCert E.γ.idx F ∗
        (∃ api : Loc, txnKvIs tp api ∗ kvOnce api [ep]) ∗ callUpd γr.kv (.txn cs t e) Q }}
      (App (Val (tp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty @!! go!"Commit"))
        (Val #()))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (⌜err = GoInterface.nil⌝ ∗ ∃ (m : TxnRespM) (σ : KVState), txnRespMsg resp m ∗
          callRes (.txn cs t e) Q σ ∗
          ⌜m.succeeded = (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs
              (linkv.txnOf cs t e)).1 ∧
            client.opRespsRel false ((linkv.txnOf cs t e).branch m.succeeded)
              (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs (linkv.txnOf cs t e)).2.2
              m.resps ∧
            m.hdr.revision = W64 ((if (linkv.MIn.txn cs t e).isWrite then
              (kvOpStep (opIn (.txn cs t e)) σ).rev else σ.rev : Nat) : Int) ∧
            σ.rev + 3 < 2 ^ 63⌝) ∨
          ⌜err ≠ GoInterface.nil⌝ }} := by
  iintro %Φ ⟨#Pc, Hobj, #Hrpc, #Hc0, #HF, Hone, Hau⟩ HΦ
  have hw : txnWireOf b.model = linkv.txnOf cs t e := by rw [hb, txnWireOf_clientTxn]
  have hp : client.TxnModel.plain b.model := by rw [hb]; exact clientTxn_plain cs t e
  have hin : client.txnModelIn (txnWireOf b.model) := by rw [hw]; exact txnModelIn_txnOf cs t e
  have hro := txnReadonly_txnOf cs t e
  unfold callUpd callRes
  cases hwr : (linkv.MIn.txn cs t e).isWrite
  · -- read-only
    simp only [Bool.false_eq_true, ↓reduceIte]
    simp only [hwr, Bool.not_false] at hro
    have hser := txnSerializable_txnOf cs t e hne
    wp_apply (client.client_txn_end_to_end tp [ep] E γr γr (W64 0) cid mid ci cd b F Q hp hin)
      $$ [Hobj Hau] as %resp %err Hout
    · iframe Hobj
      iframe #
      icases Hau with (%Hq | #Hau)
      · ileft; ipureintro; rw [hw]; exact ⟨hro, Hq⟩
      · iright; ileft; iframe Hau; ipureintro; rw [hw]; exact ⟨hro, hser⟩
    iapply HΦ
    icases Hout with (⟨%Herr, %m, #Hm, Hr⟩ | ⟨%Herr, -⟩)
    · ileft
      isplitl []
      · ipureintro; exact Herr
      rw [hw]
      unfold client.txnReplied
      simp only [hro, hser, Bool.false_eq_true, ↓reduceIte]
      icases Hr with ⟨%log, -, -, %Hp, -, #HQ⟩
      obtain ⟨hlen, hb3, -, hrev, -, -, hok, hrel⟩ := Hp
      have hr : ((kvStateOf log).rev + 1 : Nat) = log.length := client.kvStateOf_rev_succ _ hlen
      have hs : (kvStateOf log).kvs = mvcc.stateAfter log := rfl
      iexists m, kvStateOf log
      iframe Hm HQ
      ipureintro
      rw [hr, hs]
      refine ⟨hok, hrel, ?_, ?_⟩
      · rw [hrev]
        (try simp only [Bool.false_eq_true, ↓reduceIte])
        unfold kvStateOf
        simp only
        congr 1
        omega
      · unfold kvStateOf; simp only; omega
    · iright
      ipureintro; exact Herr
  · -- writing
    simp only [↓reduceIte]
    simp only [hwr, Bool.not_true] at hro
    wp_apply (client.client_txn_end_to_end tp [ep] E γr γr (W64 0) cid mid ci cd b F Q hp hin)
      $$ [Hobj Hau Hone] as %resp %err Hout
    · iframe Hobj
      iframe #
      iright; iright
      isplitr
      · ipureintro
        rw [hw]
        exact ⟨hro, linkv.txnPlain_txnOf cs t e, txnNoZeroEnd_txnOf cs t e⟩
      unfold client.txnAuOk
      iright
      iframe Hone
      rw [hw]
      iExactEq Hau; rfl
    iapply HΦ
    icases Hout with (⟨%Herr, %m, #Hm, Hr⟩ | ⟨%Herr, -⟩)
    · ileft
      isplitl []
      · ipureintro; exact Herr
      rw [hw]
      unfold client.txnReplied
      simp only [hro, Bool.false_eq_true, ↓reduceIte]
      icases Hr with ⟨%hm, %rq', %t', %x, %x', %l, %skip, %Hp, -, -, -, -, HQ⟩
      obtain ⟨-, -, Hz, -, hrev, -, -, -, hlen, hb4, hok, hrel, hsk⟩ := Hp
      have ht : t' = linkv.txnOf cs t e := Hz (irrNoZeroEnd_txnOf cs t e)
      subst ht hsk
      have hr : ((kvStateOf x.log).rev + 1 : Nat) = x.log.length := client.kvStateOf_rev_succ _ hlen
      have hs : (kvStateOf x.log).kvs = mvcc.stateAfter x.log := rfl
      iexists m, kvStateOf x.log
      iframe Hm HQ
      ipureintro
      rw [hr, hs]
      refine ⟨hok, hrel, ?_, ?_⟩
      · (try simp only [↓reduceIte])
        rw [kvOpStep_txnOf_eq, hrev, ← hs, client.kvStateOf_commit_rev _ _ hlen, hs, hr]
      · unfold kvStateOf; simp only; omega
    · iright
      ipureintro; exact Herr

/-- `opRespsMsg` element by element. -/
theorem opRespsMsg_getElem (ps : List Loc) (ms : List OpRespM) :
    opRespsMsg (GF := GF) ps ms ⊢
      ⌜ps.length = ms.length⌝ ∗ □ ∀ (k : Nat) (p : Loc) (m : OpRespM), ⌜ps[k]? = some p⌝ -∗
        ⌜ms[k]? = some m⌝ -∗ opRespMsg p m := by
  induction ps generalizing ms with
  | nil =>
    cases ms with
    | nil =>
      iintro -
      isplitr
      · ipureintro; rfl
      imodintro
      iintro %k %p %m %Hp
      simp at Hp
    | cons m ms =>
      unfold opRespsMsg
      iintro %H
      exact H.elim
  | cons p ps ih =>
    cases ms with
    | nil =>
      unfold opRespsMsg
      iintro %H
      exact H.elim
    | cons m ms =>
      show opRespMsg p m ∗ opRespsMsg ps ms ⊢ _
      iintro ⟨#Hp, Hr⟩
      ihave ⟨%Hl, #Hall⟩ := ih ms $$ Hr
      isplitr
      · ipureintro; simp [Hl]
      imodintro
      iintro %k %p' %m' %Hp' %Hm'
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at Hp' Hm'
        subst Hp' Hm'
        iexact Hp
      | succ k =>
        simp only [List.getElem?_cons_succ] at Hp' Hm'
        iapply Hall $$ %k %p' %m' %Hp' %Hm'

end proofs

end linkvtxn
end EtcdGrove
end Perennial
