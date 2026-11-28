/-
Lean-first (no Rocq counterpart).

# linkvtxn: `call`'s client calls (linkv-txn stage F)

`call`'s calls through `New`'s client of the members `ms` (since 2026-10-21, failover, D27: each
attempt to one of them; `client/v3/Results.lean`'s `_any` results; the updates one per member, `[∧ list]`) are
the client package's (`client/v3/ClientPutGet.lean`, since 2026-10-22, D31: `client_Get_st`,
`client_Put_st`, `client_Delete_st`, `client_Txn_st`). This file has the two that speak of the
model's operations, each stated with the state `σ` its update fired at and the reply's fields as
functions of `σ` (what `Reply.lean`'s outputs take):

- `client_List_st`: a list of `[listFrom, listTo)`, with a read update or none: `□ Q σ`, the
  reply's key-values the state's of the range, its header revision `σ`'s;
- `txn_Commit_st`: a transaction the builder holds as the model's (`clientTxn`), with an update
  fired at most once (writing) or a read update or none (read-only): the reply's verdict, its
  responses and revision the server's run at `σ` (from `txnReplied`).

Each also bounds `σ`'s revision below `2^63` (the replies' logs are below it).
`callUpd`/`callRes`: the update a call of the model input `i` takes, and the result it gives.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.txnwork.Reply
public import Proof.go_etcd_io.etcd.client.v3.ReadUpds
public import Proof.go_etcd_io.etcd.client.v3.PerTypeKVRest
public import Proof.go_etcd_io.etcd.client.v3.PerTypeLease
public import Proof.go_etcd_io.etcd.client.v3.ServerWatcher
public import Proof.go_etcd_io.etcd.client.v3.LeaseClient
public import Proof.go_etcd_io.etcd.client.v3.PerTypeAuth
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.PerTypeWatch
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.NewServerRFacts
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.NewServerR
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Append
public import Spec.go_etcd_io.raft.v3.MemoryStorage__SetHardState
public import Spec.go_etcd_io.raft.v3.MemoryStorage__ApplySnapshot
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Compact
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Lemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.NetErr
public import Spec.sort.SortAnyLess
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReadServer
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReadRaft
public import Proof.go_etcd_io.etcd.pkg.v3.wait.TimeListIfc
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.LessorOk
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.LessorDerive
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.NewServerAllocOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AdminEntryOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ApplyAllSnapLemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.RunAdapt
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.WatchStep
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.WatchClass
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthService
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.QuotaLemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ServerLeaseRead
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ServerLeaseRevoke
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.QuotaLeaseLemmas
public import Proof.go_etcd_io.etcd.client.v3.KVServiceOn
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_txnlin

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open go_etcd_io.etcd.server.v3.etcdserver mvcc
open client (srvStart srvStart_both kvRegs_range kvRegs_txn)

/-! ## Pure part -/

section pure
variable [GooseExts]

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
      cases op <;> simp [linkv.tOpOf, txnOpNoZeroEnd, txn.rangeOpOf, txn.deleteOpOf, op_simps]
  refine ⟨?_, hops t, hops e⟩
  intro c hc
  simp only [linkv.txnOf, List.mem_map] at hc
  obtain ⟨c', -, rfl⟩ := hc
  cases c' <;> simp [linkv.cmpOf]

theorem irrNoZeroEnd_txnOf (cs : List (linkv.MCmp GoString GoString))
    (t e : List (linkv.MOp GoString GoString)) (tw : txn.TxnModelW)
    (htw : tw.toModel = linkv.txnOf cs t e) : irrNoZeroEnd (irrTxn tw) := by
  refine ⟨fun o h => by simp [irrTxn, apply.irrEmpty] at h,
    fun o h => by simp [irrTxn, apply.irrEmpty] at h, fun t' h => ?_⟩
  simp only [irrTxn_txn, Option.some.injEq] at h
  subst h
  rw [htw]
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
    simp [txn.cutEarly, OpFull.effSortOrder, txn.rangeOpOf, op_simps]

/-! ## The inputs' sizes (2026-10-31, `notes/invoke-size.md`, pass 4) -/

/-- The longest key or value of an input `Gen` returns (its strings are the workload's keys and
one-byte values): every request it makes fits a gRPC message. -/
abbrev inMax : Nat := 2 ^ 20

/-- A model operation's strings at most `N` bytes. -/
def mopBytesLe (N : Nat) : linkv.MOp GoString GoString → Prop
  | .get k => k.length ≤ N
  | .put k v => k.length ≤ N ∧ v.length ≤ N
  | .del k => k.length ≤ N

/-- A model comparison's strings at most `N` bytes. -/
def mcmpBytesLe (N : Nat) : linkv.MCmp GoString GoString → Prop
  | .val k v => k.length ≤ N ∧ v.length ≤ N
  | .ver k _ => k.length ≤ N
  | .mod k _ => k.length ≤ N

/-- A model input's strings at most `N` bytes. -/
def minBytesLe (N : Nat) : linkv.MIn GoString GoString → Prop
  | .get k => k.length ≤ N
  | .list => True
  | .put k v => k.length ≤ N ∧ v.length ≤ N
  | .del k => k.length ≤ N
  | .txn cs t e => (∀ c ∈ cs, mcmpBytesLe N c) ∧ ∀ o ∈ t ++ e, mopBytesLe N o

/-- **An input `Gen` may return** (`ValidIn`), its transactions not empty: a transaction with no
operations is served without a linearizable read (`issues/etcd-txn-empty-serializable.md`); its
strings at most `inMax` bytes (its requests fit a gRPC message). -/
def GenIn (x : github_com.mit_pdos.etcd_grove.examples.lib.txnwork.Input) : Prop :=
  ValidIn x ∧ (∀ cs t e, decIn x = some (.txn cs t e) → t ++ e ≠ []) ∧
    ∀ i, decIn x = some i → minBytesLe inMax i

theorem nodes_tOpOf : ∀ l : List (linkv.MOp GoString GoString),
    (l.map fun o => (linkv.tOpOf o).nodes).sum = l.length
  | [] => rfl
  | o :: l => by
    rw [List.map_cons, List.sum_cons, nodes_tOpOf l, List.length_cons]
    cases o <;> simp [linkv.tOpOf, TxnOp.nodes] <;> omega

/-- **A transaction input's request fits**: at most five comparisons and operations, its strings
at most `inMax` bytes. -/
theorem txnSizeOk_txnOf (cs : List (linkv.MCmp GoString GoString))
    (t e : List (linkv.MOp GoString GoString)) (hl : cs.length + t.length + e.length ≤ 5)
    (hb : minBytesLe inMax (.txn cs t e)) : txnSizeOk (linkv.txnOf cs t e) := by
  obtain ⟨hc, ho⟩ := hb
  refine txnSizeOk_of_bounds (N := inMax) (M := 5) ⟨?_, ?_, ?_⟩ ?_ (by decide)
  · intro c hc'
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hc'
    have := hc m hm
    cases m <;> simp_all [mcmpBytesLe, linkv.cmpOf, CmpModel.bytesLe]
  · intro o ho'
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 ho'
    have := ho m (List.mem_append_left _ hm)
    cases m <;> simp_all [mopBytesLe, linkv.tOpOf, TxnOp.bytesLe, txn.rangeOpOf, txn.deleteOpOf,
      op_simps]
  · intro o ho'
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 ho'
    have := ho m (List.mem_append_right _ hm)
    cases m <;> simp_all [mopBytesLe, linkv.tOpOf, TxnOp.bytesLe, txn.rangeOpOf, txn.deleteOpOf,
      op_simps]
  · simp only [TxnModel.nodes, linkv.txnOf, List.length_map, List.map_map]
    have h1 := nodes_tOpOf t
    have h2 := nodes_tOpOf e
    simp only [Function.comp_def] at h1 h2 ⊢
    omega

theorem cmpsOfL_length (x : github_com.mit_pdos.etcd_grove.examples.lib.txnwork.Input) :
    (cmpsOfL x).length ≤ 1 := by
  unfold cmpsOfL; split <;> simp

theorem elseOfL_length1 (x : github_com.mit_pdos.etcd_grove.examples.lib.txnwork.Input) :
    (elseOfL x).length ≤ 1 := by
  unfold elseOfL; split <;> simp

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
      cases op <;> simp [linkv.tOpOf, txn.opIsSerGet, txn.rangeOpOf, op_simps]
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
  rw [if_pos ⟨by rw [linkv.txnOf_branch]; exact linkv.pathsIgnOk_tOpOf σ.kvs _,
    by rw [linkv.txnOf_branch]; exact txn.pathsLeaseOk_plain _ _ _ (linkv.opsPlain_tOpOf _)⟩]

/-- What a transaction's input decodes. -/
theorem decIn_txn (x : github_com.mit_pdos.etcd_grove.examples.lib.txnwork.Input)
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

/-- A transaction input has at most five comparisons and operations. -/
theorem decIn_txn_length (x : github_com.mit_pdos.etcd_grove.examples.lib.txnwork.Input)
    (cs : List (linkv.MCmp GoString GoString)) (t e : List (linkv.MOp GoString GoString))
    (h : decIn x = some (.txn cs t e)) : cs.length + t.length + e.length ≤ 5 := by
  obtain ⟨-, hc, ht, he⟩ := decIn_txn x cs t e h
  rw [decAll_length _ _ _ hc, decAll_length _ _ _ ht, decAll_length _ _ _ he]
  have := cmpsOfL_length x; have := thenOfL_length x; have := elseOfL_length1 x
  omega

theorem txnOf_branch' (cs : List (linkv.MCmp GoString GoString))
    (t e : List (linkv.MOp GoString GoString)) (b : Bool) :
    (linkv.txnOf cs t e).branch b = (if b then t else e).map linkv.tOpOf := by
  unfold linkv.txnOf TxnModel.branch
  cases b <;> rfl

end pure

/-! ## The updates -/

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
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
  iprop(⌜∃ x : github_com.mit_pdos.etcd_grove.examples.lib.txnwork.Input, i = boxIn x ∧ GenIn x⌝)

end defs

/-! ## The calls -/

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
-- (2026-10-22) the client's and the server's package assumptions, not linkvtxn's: any caller of
-- `New`'s client uses these calls (also `client/v3/kubernetes`)
variable [go_etcd_io.etcd.client.v3.Assumptions]
variable [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

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

end etcd_txnlin
end EtcdGrove
end Perennial
