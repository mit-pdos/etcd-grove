/-
**etcd's specs of the KV service with auth on** (the auth plan's E3zb, 2026-10-28;
`KVService.lean`'s, for a member started with auth on): metadata-indexed gRPC specs
(`GrpcSpecMd`), whose replies carry what the server's answers with auth on add
(`v3rpc.srvKVAnsOn`) at the token of the metadata the handler sees (`auth.mdTokenOf`, what
`AuthInfoFromCtx` reads of its context, `auth.ctxToken`):
- a write (`Put`, `DeleteRange`, a writing `Txn`): its grant (`v3rpc.writeGrantOn`: the request with
  the header the server stamped was granted at the committed log before its entry, the header's user
  the empty one or the one the token was issued to, and the entry committed);
- a read (`Range`, a read-only `Txn`), at a lower bound `n` of the auth store's published index the
  caller gives (`auth.authPubLbM`; `0` is free): its check's class (`v3rpc.rangeAuthed`,
  `v3rpc.txnAuthed`: the permissions it saw granted at states recorded at an index at least `n`,
  for an auth info that is the caller's).
The requests the permission cache decides: a delete's key and range end, a writing transaction's
every permission (`auth.reqShape`, `kvShapeAll`). Otherwise as auth off: the replies are
`putReplied`, `rangeReplyOk`, `deleteReplied`, `txnReplied` (the mode-`on` model's state is the
state of the log read, `kvStM true`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.KVService
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ServerKVOn

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

namespace client

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

end defs

section defsHF
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF] [GoLocalContext]
variable [sem : go.Semantics]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **etcd's `Put` with auth on**: `etcdPutSpec`'s, the caller's update told the put's grant at
the token of the attempt's metadata when it fires (`v3rpc.kvOpAuOn`, 5a), the reply also with the
grant. A put's lease `0`, or any lease at the revocable lease mode (the server's `putPermitOn`,
auth-lease S3b; a missing lease is the server's `ErrLeaseNotFound`, an error). (DRAFT, k8s etcd3 7c-1b, HS-4: the caller's error outcome at every description, `□ ∀ d, Ψe d`: no information on an error) -/
def etcdPutSpecOnW (T : IProp GF) (E : apply.AEnv GF) (ρ : ReqNames) (cid mid : w64) :
    GrpcMd → OpFull → (PutRespM → IProp GF) → (GoString → IProp GF) → IProp GF :=
  fun md (o : OpFull) (Φ : PutRespM → IProp GF) (Ψe : GoString → IProp GF) =>
    iprop((□ ∀ d, Ψe d) ∗ ∃ F : mvcc.Log, srvApi.kvLogLb E.γs F ∗
      ∃ Q : KVState → IProp GF, ⌜o.leaseID = W64 0 ∨ ρ.kv.lm = .revocable⌝ ∗
        v3rpc.kvOpAuOn T E ρ (auth.mdTokenOf md) (.put o) Q ∗
        ∀ m : PutRespM, putReplied E ρ.rd F o Q cid mid m -∗
          v3rpc.writeGrantOn T E ρ (auth.mdTokenOf md) (irrPut o) -∗ Φ m)

end defsHF

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]


/-- **`etcdPutSpecOnW` at the messages' models** (S2, heap-free vocabulary, 2026-11-23: the spec is
`etcdPutSpecOnW`, over the models alone, what a service table holds; this is its form at the message
types). -/
def etcdPutSpecOn (T : IProp GF) (E : apply.AEnv GF) (ρ : ReqNames) (cid mid : w64) :
    GrpcSpecMd (GF := GF) pbPutRequest pbPutResponse :=
  etcdPutSpecOnW T E ρ cid mid

end defs

section defsHF
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF] [GoLocalContext]
variable [sem : go.Semantics]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **etcd's `DeleteRange` with auth on**: `etcdDeleteSpec`'s, for a key and range end of the
shape the permission cache decides, the caller's update told the delete's grant (`v3rpc.kvOpAuOn`),
the reply also with the grant. (DRAFT, k8s etcd3 7c-1b, HS-4: the caller's error outcome at every description, `□ ∀ d, Ψe d`: no information on an error) -/
def etcdDeleteSpecOnW (T : IProp GF) (E : apply.AEnv GF) (ρ : ReqNames) (cid mid : w64) :
    GrpcMd → OpFull → (DelRespM → IProp GF) → (GoString → IProp GF) → IProp GF :=
  fun md (o : OpFull) (Φ : DelRespM → IProp GF) (Ψe : GoString → IProp GF) =>
    iprop((□ ∀ d, Ψe d) ∗ ⌜auth.reqShape o.key o.base.rangeEnd⌝ ∗ ∃ F : mvcc.Log, srvApi.kvLogLb E.γs F ∗
      ∃ Q : KVState → IProp GF, ⌜o.base.rangeEnd ≠ [W8 0]⌝ ∗
        v3rpc.kvOpAuOn T E ρ (auth.mdTokenOf md) (.deleteRange o) Q ∗
        ∀ m : DelRespM, deleteReplied E ρ.rd F o Q cid mid m -∗
          v3rpc.writeGrantOn T E ρ (auth.mdTokenOf md) (irrDeleteRange o) -∗ Φ m)

end defsHF

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]


/-- **`etcdDeleteSpecOnW` at the messages' models** (S2, heap-free vocabulary, 2026-11-23: the spec
is `etcdDeleteSpecOnW`, over the models alone, what a service table holds; this is its form at the
message types). -/
def etcdDeleteSpecOn (T : IProp GF) (E : apply.AEnv GF) (ρ : ReqNames) (cid mid : w64) :
    GrpcSpecMd (GF := GF) pbDeleteRangeRequest pbDeleteRangeResponse :=
  etcdDeleteSpecOnW T E ρ cid mid

end defs

section defsHF
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF] [GoLocalContext]
variable [sem : go.Semantics]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **etcd's `Range` with auth on**: `etcdRangeSpec`'s, with a lower bound `n` of the published
auth index, the reply also with the read's check (`rangeAuthed`). (DRAFT, k8s etcd3 7c-2 part 2,
S6: the caller's error outcome at every description, `□ ∀ d, Ψe d`: no information on an error) -/
def etcdRangeSpecOnW (T : IProp GF) (E : apply.AEnv GF) (γr : ReadNames) (cid mid : w64) :
    GrpcMd → OpFull → (RangeRespM → IProp GF) → (GoString → IProp GF) → IProp GF :=
  fun md (o : OpFull) (Φ : RangeRespM → IProp GF) (Ψe : GoString → IProp GF) =>
    iprop((□ ∀ d, Ψe d) ∗ ∃ (c : w64) (F : mvcc.Log) (Q : KVState → IProp GF) (n : Nat), committedAtLeast γr c ∗
      srvApi.kvLogLb E.γs F ∗ auth.authPubLbM E.authMode n ∗
      (⌜Q = fun _ => iprop(True)⌝ ∨ (⌜o.base.serializable = false⌝ ∗ kvReadAu γr.kv Q)) ∗
      ∀ m : RangeRespM, rangeReplyOk E γr c F o cid mid Q m -∗
        v3rpc.rangeAuthed T E γr c n (auth.mdTokenOf md) o -∗ Φ m)

end defsHF

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]


/-- **`etcdRangeSpecOnW` at the messages' models** (S2, heap-free vocabulary, 2026-11-23: the spec
is `etcdRangeSpecOnW`, over the models alone, what a service table holds; this is its form at the
message types). -/
def etcdRangeSpecOn (T : IProp GF) (E : apply.AEnv GF) (γr : ReadNames) (cid mid : w64) :
    GrpcSpecMd (GF := GF) pbRangeRequest pbRangeResponse :=
  etcdRangeSpecOnW T E γr cid mid

/-! ### Nested transactions' shape (`notes/txn-nested.md`, N2-N4) -/

mutual
/-- The keys an operation puts, at any depth, both branches. -/
def opPutKeys : TxnOp → List GoString
  | .put k _ _ => [k]
  | .putKeep k _ => [k]
  | .putIgnVal k _ => [k]
  | .txn _ ts es => opsPutKeys ts ++ opsPutKeys es
  | _ => []

/-- The keys a list of operations puts, at any depth. -/
def opsPutKeys : List TxnOp → List GoString
  | [] => []
  | op :: ops => opPutKeys op ++ opsPutKeys ops
end

mutual
/-- The deletes of an operation, at any depth, both branches. -/
def opDelOps : TxnOp → List OpFull
  | .delete o => [o]
  | .txn _ ts es => opsDelOps ts ++ opsDelOps es
  | _ => []

/-- The deletes of a list of operations, at any depth. -/
def opsDelOps : List TxnOp → List OpFull
  | [] => []
  | op :: ops => opDelOps op ++ opsDelOps ops
end

/-- A nested transaction `u` puts no key (at any depth) that a delete of `v` (at any depth)
covers, in the model's sense of a range (`inRange`: the key alone, from the key on for `[0]`,
`[key, rangeEnd)` otherwise). Constrains nothing unless `u` is a nested transaction. -/
def sibOkT (u v : TxnOp) : Prop :=
  match u with
  | .txn _ _ _ => ∀ k ∈ opPutKeys u, ∀ o ∈ opDelOps v, inRange o.key o.base.rangeEnd k = false
  | _ => True

mutual
/-- **No nested transaction puts a key a later sibling deletes**, at every level (the model's
reading of the server's `ReqOp.siblingSafe`; `issues/etcd-txn-check-intervals-sibling.md`: the case
`checkIntervals` does not check). -/
def txnSibSafe : TxnOp → Prop
  | .txn _ ts es => txnSibSafeL ts ∧ txnSibSafeL es
  | _ => True

/-- `txnSibSafe` of each operation, and `sibOkT` of each with every later sibling. -/
def txnSibSafeL : List TxnOp → Prop
  | [] => True
  | u :: us => (∀ v ∈ us, sibOkT u v) ∧ txnSibSafe u ∧ txnSibSafeL us
end

/-- **A writing transaction's nested shape** (a premise; what the server's handler needs of a
writing transaction beyond `txn.txnPlain` and `txnNoZeroEnd`, inherited from its `kvDepPre`, D19c):
no get at any depth a sort cut early by a limit (`txn.OpsNoCut`,
`issues/etcd-range-sort-none-limit.md`), and no nested transaction putting a key a later sibling
deletes (`txnSibSafeL`). A transaction of plain operations within the model has it
(`txnNestOk_of_plain`). -/
def txnNestOk (t : TxnModel) : Prop :=
  txn.OpsNoCut t.thenOps ∧ txn.OpsNoCut t.elseOps ∧ txnSibSafeL t.thenOps ∧ txnSibSafeL t.elseOps

/-- **A transaction of plain operations within the model has the nested shape** (L8). This is the
one place a writing transaction's caller still meets `txnModelIn`: the source of `OpsNoCut` for a
plain transaction. -/
theorem txnNestOk_of_plain (t : TxnModel) (hp : TxnModel.plain t) (hin : txnModelIn t) :
    txnNestOk t := by
  have hnc : ∀ ops : List TxnOp, (∀ op ∈ ops, TxnOp.plain op) →
      (∀ o : OpFull, TxnOp.get o ∈ ops → ¬ txn.cutEarly o) → txn.OpsNoCut ops := by
    intro ops hp hc
    induction ops with
    | nil => trivial
    | cons op ops ih =>
      refine ⟨?_, ih (fun op' h => hp op' (List.mem_cons_of_mem _ h))
        (fun o h => hc o (List.mem_cons_of_mem _ h))⟩
      cases op with
      | get o => exact hc o List.mem_cons_self
      | txn _ _ _ => exact (hp _ List.mem_cons_self).elim
      | _ => trivial
  have hss : ∀ ops : List TxnOp, (∀ op ∈ ops, TxnOp.plain op) → txnSibSafeL ops := by
    intro ops hp
    induction ops with
    | nil => trivial
    | cons op ops ih =>
      have h0 := hp op List.mem_cons_self
      refine ⟨fun v _ => ?_, ?_, ih (fun op' h => hp op' (List.mem_cons_of_mem _ h))⟩
      · cases op with
        | txn _ _ _ => exact h0.elim
        | _ => trivial
      · cases op with
        | txn _ _ _ => exact h0.elim
        | _ => trivial
  exact ⟨hnc _ hp.1 (fun o h => (hin o (List.mem_append_left _ h)).2),
    hnc _ hp.2 (fun o h => (hin o (List.mem_append_right _ h)).2), hss _ hp.1, hss _ hp.2⟩

theorem opDelOps_nil_of_mem : ∀ (us : List TxnOp), opsDelOps us = [] → ∀ v ∈ us, opDelOps v = []
  | [], _, v, hv => by cases hv
  | u :: us, h, v, hv => by
    simp only [opsDelOps, List.append_eq_nil_iff] at h
    rcases List.mem_cons.mp hv with rfl | hv
    · exact h.1
    · exact opDelOps_nil_of_mem us h.2 v hv

mutual
theorem txnSibSafe_noDel_aux : ∀ op : TxnOp, opDelOps op = [] → txnSibSafe op
  | .txn _ ts es, h => by
    simp only [opDelOps, List.append_eq_nil_iff] at h
    exact ⟨txnSibSafeL_noDel_aux ts h.1, txnSibSafeL_noDel_aux es h.2⟩
  | .get _, _ => trivial
  | .put _ _ _, _ => trivial
  | .delete _, _ => trivial
  | .putKeep _ _, _ => trivial
  | .putIgnVal _ _, _ => trivial

theorem txnSibSafeL_noDel_aux : ∀ ops : List TxnOp, opsDelOps ops = [] → txnSibSafeL ops
  | [], _ => trivial
  | u :: us, h => by
    simp only [opsDelOps, List.append_eq_nil_iff] at h
    refine ⟨fun v hv => ?_, txnSibSafe_noDel_aux u h.1, txnSibSafeL_noDel_aux us h.2⟩
    have hv' := opDelOps_nil_of_mem us h.2 v hv
    cases u with
    | txn _ _ _ => intro k _ o ho; rw [hv'] at ho; cases ho
    | _ => trivial
end

/-- **Operations with no delete at any depth are sibling-safe** (L8). -/
theorem txnSibSafeL_of_noDel (ops : List TxnOp) (h : opsDelOps ops = []) : txnSibSafeL ops := by
  exact txnSibSafeL_noDel_aux ops h

end defs

section defsHF
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF] [GoLocalContext]
variable [sem : go.Semantics]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **A transaction's auth facts, as its reply carries them** (persistent): a read-only one's
check (`txnAuthed`), a writing one's grant. -/
def txnAuthOn (T : IProp GF) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (c : w64) (n : Nat)
    (tok : Option GoString) (t : TxnModel) : IProp GF :=
  if txn.txnReadonly t then v3rpc.txnAuthed T E γr c n tok t
  else iprop(∃ tw : txn.TxnModelW, ⌜tw.toModel = t⌝ ∗ v3rpc.writeGrantOn T E ρ tok (irrTxn tw))

instance txnAuthOn_persistent (T : IProp GF) [Persistent T] (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (c : w64) (n : Nat) (tok : Option GoString) (t : TxnModel) :
    Persistent (txnAuthOn (GF := GF) T E ρ γr c n tok t) := by
  unfold txnAuthOn; split <;> infer_instance

end defsHF

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]


/-- A writing transaction's auth facts are its grant (L13). -/
theorem txnAuthOn_write (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (c : w64)
    (n : Nat) (tok : Option GoString) (t : TxnModel) (h : txn.txnReadonly t = false) :
    txnAuthOn (GF := GF) (srvTLSId s) E ρ γr c n tok t ⊣⊢
      ∃ tw : txn.TxnModelW, ⌜tw.toModel = t⌝ ∗ v3rpc.writeGrantOn (srvTLSId s) E ρ tok (irrTxn tw) := by
  unfold txnAuthOn
  rw [h]
  simp only [Bool.false_eq_true, ↓reduceIte]
  exact .rfl

theorem opsPutKeys_append : ∀ (a b : List TxnOp), opsPutKeys (a ++ b) = opsPutKeys a ++ opsPutKeys b
  | [], b => by simp [opsPutKeys]
  | x :: a, b => by simp [opsPutKeys, opsPutKeys_append a b, List.append_assoc]

theorem mem_opsPutKeys_of_mem : ∀ (ops : List TxnOp) (op : TxnOp), op ∈ ops →
    ∀ k ∈ opPutKeys op, k ∈ opsPutKeys ops
  | [], _, h, _, _ => by cases h
  | x :: ops, op, h, k, hk => by
    simp only [opsPutKeys, List.mem_append]
    rcases List.mem_cons.mp h with rfl | h
    · exact Or.inl hk
    · exact Or.inr (mem_opsPutKeys_of_mem ops op h k hk)

mutual
theorem opPerms_put : ∀ (w : txn.TxnOpW) (k : GoString), k ∈ opPutKeys w.toOp →
    ((k, [], .write) : apply.Perm3) ∈ opPerms w
  | .get _, k, h => by simp [txn.TxnOpW.toOp, opPutKeys] at h
  | .put o, k, h => by
    have hk : k = o.key := by
      simp only [txn.TxnOpW.toOp, txn.putTxnOp] at h
      by_cases h1 : o.ignoreValue = true <;> by_cases h2 : o.ignoreLease = true <;>
        simp_all [opPutKeys]
    subst hk; simp [opPerms, apply.putPerms]
  | .delete _, k, h => by simp [txn.TxnOpW.toOp, opPutKeys] at h
  | .txn cs ts es, k, h => by
    simp only [txn.TxnOpW.toOp, opPutKeys, List.mem_append] at h
    simp only [opPerms, List.mem_append]
    rcases h with h | h
    · exact Or.inl (Or.inr (opsPerms_put ts k h))
    · exact Or.inr (opsPerms_put es k h)

theorem opsPerms_put : ∀ (ws : List txn.TxnOpW) (k : GoString),
    k ∈ opsPutKeys (txn.TxnOpW.toOps ws) → ((k, [], .write) : apply.Perm3) ∈ opsPerms ws
  | [], k, h => by simp [txn.TxnOpW.toOps, opsPutKeys] at h
  | w :: ws, k, h => by
    simp only [txn.TxnOpW.toOps, opsPutKeys, List.mem_append] at h
    simp only [opsPerms, List.mem_append]
    rcases h with h | h
    · exact Or.inl (opPerms_put w k h)
    · exact Or.inr (opsPerms_put ws k h)
end

/-- **A put at any depth of a transaction needs the write permission on its key** (L10). -/
theorem reqPerms_irrTxn_put (tw : txn.TxnModelW) (k : GoString)
    (h : k ∈ opsPutKeys (tw.toModel.thenOps ++ tw.toModel.elseOps)) :
    ((k, [], .write) : apply.Perm3) ∈ reqPerms (irrTxn tw) := by
  have hd : apply.dispatchKind (irrTxn tw) = .txn := by
    simp [apply.dispatchKind, irrTxn, apply.irrEmpty, apply.IRRModel.txn]
  unfold reqPerms
  rw [hd]
  simp only [irrTxn]
  simp only [txn.TxnModelW.toModel, opsPutKeys_append, List.mem_append] at h
  simp only [List.mem_append]
  rcases h with h | h
  · exact Or.inl (Or.inr (opsPerms_put _ k h))
  · exact Or.inr (opsPerms_put _ k h)

/-- `reqPerms_irrTxn_put` at a put one level down in the then-branch (L10). -/
theorem reqPerms_irrTxn_nestedPut (tw : txn.TxnModelW) (cs : List CmpModel) (ts es : List TxnOp)
    (k v : GoString) (l : w64) (hm : TxnOp.txn cs ts es ∈ tw.toModel.thenOps)
    (hp : TxnOp.put k v l ∈ ts) :
    ((k, [], .write) : apply.Perm3) ∈ reqPerms (irrTxn tw) := by
  apply reqPerms_irrTxn_put tw k
  rw [opsPutKeys_append, List.mem_append]
  left
  refine mem_opsPutKeys_of_mem _ _ hm k ?_
  simp only [opPutKeys, List.mem_append]
  exact Or.inl (mem_opsPutKeys_of_mem _ _ hp k (by simp [opPutKeys]))

end defs

section defsHF
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF] [GoLocalContext]
variable [sem : go.Semantics]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **etcd's `Txn` with auth on**: `etcdTxnSpec`'s (a writing transaction may nest transactions: plain, `txn.txnPlain`, at every
depth; `txnNestOk`), a writing transaction's every permission of the
shape the permission cache decides, with a lower bound `n` of the published auth index, the reply
also with the transaction's auth facts (`txnAuthOn`), a writing one's update told its grant
(`v3rpc.kvOpAuOn`). (DRAFT, k8s etcd3 7c-1b, HS-4: the caller's error outcome at every description, `□ ∀ d, Ψe d`: no information on an error) -/
def etcdTxnSpecOnW (T : IProp GF) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (cid mid : w64) :
    GrpcMd → TxnModel → (TxnRespM → IProp GF) → (GoString → IProp GF) → IProp GF :=
  fun md (t : TxnModel) (Φ : TxnRespM → IProp GF) (Ψe : GoString → IProp GF) =>
    iprop((□ ∀ d, Ψe d) ∗ ⌜(txn.txnReadonly t = true → txnModelIn t) ∧ (txn.txnReadonly t = false →
        ∀ tw : txn.TxnModelW, tw.toModel = t → kvShapeAll (irrTxn tw))⌝ ∗
      ∃ Q : KVState → IProp GF,
      (⌜txn.txnReadonly t = true ∧ Q = fun _ => iprop(True)⌝ ∨
        (⌜txn.txnReadonly t = true ∧ txn.txnSerializable t = false⌝ ∗ kvReadAu γr.kv Q) ∨
        (⌜txn.txnReadonly t = false ∧ (txn.txnPlain t ∨ (ρ.kv.lm = .revocable ∧ txnPlainL t)) ∧
            txnNoZeroEnd t ∧ txnNestOk t⌝ ∗
          v3rpc.kvOpAuOn T E ρ (auth.mdTokenOf md) (.txn t) Q)) ∗
      ∃ (c : w64) (F : mvcc.Log) (n : Nat), committedAtLeast γr c ∗
      srvApi.kvLogLb E.γs F ∗ auth.authPubLbM E.authMode n ∗
      ∀ m : TxnRespM, txnReplied E ρ.rd γr c F t Q cid mid m -∗
        txnAuthOn T E ρ γr c n (auth.mdTokenOf md) t -∗ Φ m)

end defsHF

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]


/-- **`etcdTxnSpecOnW` at the messages' models** (S2, heap-free vocabulary, 2026-11-23: the spec is
`etcdTxnSpecOnW`, over the models alone, what a service table holds; this is its form at the message
types). -/
def etcdTxnSpecOn (T : IProp GF) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (cid mid : w64) :
    GrpcSpecMd (GF := GF) pbTxnRequest pbTxnResponse :=
  etcdTxnSpecOnW T E ρ γr cid mid

/-! ### The KV methods' specs in the auth mode `on` (the auth component's stage 5)

One spec per method over the mode, as the server's rows (`v3rpc.kvOpAuM`): with auth on the facts
of the `…SpecOn` texts, with auth off those of `etcd…Spec` (`KVService.lean`), each gated by the mode
(`⌜on = true⌝ → …`, `⌜on = false⌝ → …`). The two texts stay, as its views (`etcdPutSpecM_true`,
`etcdPutSpecM_false`, ...). -/

end defs

section defsHF
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF] [GoLocalContext]
variable [sem : go.Semantics]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **etcd's `Put` in the auth mode `on`**: the update by `v3rpc.kvOpAuM`; the reply with the
revision's lower bound with auth off, with the put's grant with auth on. (DRAFT, k8s etcd3 7c-1b, HS-4: the caller's error outcome at every description, `□ ∀ d, Ψe d`: no information on an error) -/
def etcdPutSpecMW (on : Bool) (T : IProp GF) (E : apply.AEnv GF) (ρ : ReqNames) (cid mid : w64) :
    GrpcMd → OpFull → (PutRespM → IProp GF) → (GoString → IProp GF) → IProp GF :=
  fun md (o : OpFull) (Φ : PutRespM → IProp GF) (Ψe : GoString → IProp GF) =>
    iprop((□ ∀ d, Ψe d) ∗ ∃ F : mvcc.Log, srvApi.kvLogLb E.γs F ∗
      ∃ Q : KVState → IProp GF, ⌜o.leaseID = W64 0 ∨ (on = true ∧ ρ.kv.lm = .revocable)⌝ ∗
        v3rpc.kvOpAuM on T E ρ (auth.mdTokenOf md) (.put o) Q ∗
        ∀ m : PutRespM, putReplied E ρ.rd F o Q cid mid m -∗
          (⌜on = false⌝ → kvRevLb ρ.rd.kv m.hdr.revision) -∗
          (⌜on = true⌝ → v3rpc.writeGrantOn T E ρ (auth.mdTokenOf md) (irrPut o)) -∗ Φ m)

end defsHF

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]


/-- **`etcdPutSpecMW` at the messages' models** (S2, heap-free vocabulary, 2026-11-23: the spec is
`etcdPutSpecMW`, over the models alone, what a service table holds; this is its form at the message
types). -/
def etcdPutSpecM (on : Bool) (T : IProp GF) (E : apply.AEnv GF) (ρ : ReqNames) (cid mid : w64) :
    GrpcSpecMd (GF := GF) pbPutRequest pbPutResponse :=
  etcdPutSpecMW on T E ρ cid mid

end defs

section defsHF
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF] [GoLocalContext]
variable [sem : go.Semantics]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **etcd's `DeleteRange` in the auth mode `on`**: with auth on, for a key and range end of the
shape the permission cache decides; the update by `v3rpc.kvOpAuM`; the reply with the delete's
grant with auth on. (DRAFT, k8s etcd3 7c-1b, HS-4: the caller's error outcome at every description, `□ ∀ d, Ψe d`: no information on an error) -/
def etcdDeleteSpecMW (on : Bool) (T : IProp GF) (E : apply.AEnv GF) (ρ : ReqNames) (cid mid : w64) :
    GrpcMd → OpFull → (DelRespM → IProp GF) → (GoString → IProp GF) → IProp GF :=
  fun md (o : OpFull) (Φ : DelRespM → IProp GF) (Ψe : GoString → IProp GF) =>
    iprop((□ ∀ d, Ψe d) ∗ ⌜on = true → auth.reqShape o.key o.base.rangeEnd⌝ ∗ ∃ F : mvcc.Log, srvApi.kvLogLb E.γs F ∗
      ∃ Q : KVState → IProp GF, ⌜o.base.rangeEnd ≠ [W8 0]⌝ ∗
        v3rpc.kvOpAuM on T E ρ (auth.mdTokenOf md) (.deleteRange o) Q ∗
        ∀ m : DelRespM, deleteReplied E ρ.rd F o Q cid mid m -∗
          (⌜on = true⌝ → v3rpc.writeGrantOn T E ρ (auth.mdTokenOf md) (irrDeleteRange o)) -∗ Φ m)

end defsHF

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]


/-- **`etcdDeleteSpecMW` at the messages' models** (S2, heap-free vocabulary, 2026-11-23: the spec
is `etcdDeleteSpecMW`, over the models alone, what a service table holds; this is its form at the
message types). -/
def etcdDeleteSpecM (on : Bool) (T : IProp GF) (E : apply.AEnv GF) (ρ : ReqNames) (cid mid : w64) :
    GrpcSpecMd (GF := GF) pbDeleteRangeRequest pbDeleteRangeResponse :=
  etcdDeleteSpecMW on T E ρ cid mid

end defs

section defsHF
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF] [GoLocalContext]
variable [sem : go.Semantics]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **etcd's `Range` in the auth mode `on`**: with a lower bound `n` of the published auth index,
the reply with the read's check with auth on. (DRAFT, k8s etcd3 7c-2 part 2, S6: the error
outcome at every description when the request's check refuses it, `v3rpc.rangeCheck`; at the
future revision's and the compacted one's descriptions, from the read's facts at the error,
`rangeErrReply`) -/
def etcdRangeSpecMW (on : Bool) (T : IProp GF) (E : apply.AEnv GF) (γr : ReadNames) (cid mid : w64) :
    GrpcMd → OpFull → (RangeRespM → IProp GF) → (GoString → IProp GF) → IProp GF :=
  fun md (o : OpFull) (Φ : RangeRespM → IProp GF) (Ψe : GoString → IProp GF) =>
    iprop(∃ (c : w64) (F : mvcc.Log) (Q : KVState → IProp GF) (n : Nat), committedAtLeast γr c ∗
      srvApi.kvLogLb E.γs F ∗ auth.authPubLbM E.authMode n ∗
      (⌜Q = fun _ => iprop(True)⌝ ∨ (⌜o.base.serializable = false⌝ ∗ kvReadAu γr.kv Q)) ∗
      (⌜v3rpc.rangeCheck o ≠ none⌝ -∗ □ ∀ d, Ψe d) ∗
      ((rangeErrReply E γr c F o Q (rangeFutureAt o) -∗ Ψe go_etcd_io.etcd.cache.v3.futureRevDesc) ∧
        (rangeErrReply E γr c F o Q (rangeCompactedAt o) -∗
          Ψe go_etcd_io.etcd.cache.v3.compactedDesc)) ∗
      ∀ m : RangeRespM, rangeReplyOk E γr c F o cid mid Q m -∗
        (⌜on = true⌝ → v3rpc.rangeAuthed T E γr c n (auth.mdTokenOf md) o) -∗ Φ m)

end defsHF

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]


/-- **`etcdRangeSpecMW` at the messages' models** (S2, heap-free vocabulary, 2026-11-23: the spec is
`etcdRangeSpecMW`, over the models alone, what a service table holds; this is its form at the
message types). -/
def etcdRangeSpecM (on : Bool) (T : IProp GF) (E : apply.AEnv GF) (γr : ReadNames) (cid mid : w64) :
    GrpcSpecMd (GF := GF) pbRangeRequest pbRangeResponse :=
  etcdRangeSpecMW on T E γr cid mid

end defs

section defsHF
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF] [GoLocalContext]
variable [sem : go.Semantics]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **etcd's `Txn` in the auth mode `on`**: with auth on, a writing transaction's every permission
of the shape the permission cache decides; a writing one's update by `v3rpc.kvOpAuM`; the reply with
the revision's lower bound with auth off, with the transaction's auth facts with auth on. (DRAFT, k8s etcd3 7c-1b, HS-4: the caller's error outcome at every description, `□ ∀ d, Ψe d`: no information on an error) -/
def etcdTxnSpecMW (on : Bool) (T : IProp GF) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (cid mid : w64) : GrpcMd → TxnModel → (TxnRespM → IProp GF) → (GoString → IProp GF) → IProp GF :=
  fun md (t : TxnModel) (Φ : TxnRespM → IProp GF) (Ψe : GoString → IProp GF) =>
    iprop((□ ∀ d, Ψe d) ∗ ⌜(txn.txnReadonly t = true → txnModelIn t) ∧ (on = true → txn.txnReadonly t = false →
        ∀ tw : txn.TxnModelW, tw.toModel = t → kvShapeAll (irrTxn tw))⌝ ∗
      ∃ Q : KVState → IProp GF,
      (⌜txn.txnReadonly t = true ∧ Q = fun _ => iprop(True)⌝ ∨
        (⌜txn.txnReadonly t = true ∧ txn.txnSerializable t = false⌝ ∗ kvReadAu γr.kv Q) ∨
        (⌜txn.txnReadonly t = false ∧
            (txn.txnPlain t ∨ (on = true ∧ ρ.kv.lm = .revocable ∧ txnPlainL t)) ∧
            txnNoZeroEnd t ∧ txnNestOk t⌝ ∗
          v3rpc.kvOpAuM on T E ρ (auth.mdTokenOf md) (.txn t) Q)) ∗
      ∃ (c : w64) (F : mvcc.Log) (n : Nat), committedAtLeast γr c ∗
      srvApi.kvLogLb E.γs F ∗ auth.authPubLbM E.authMode n ∗
      ∀ m : TxnRespM, txnReplied E ρ.rd γr c F t Q cid mid m -∗
        (⌜on = false⌝ → txnRevLb ρ.rd.kv t m) -∗
        (⌜on = true⌝ → txnAuthOn T E ρ γr c n (auth.mdTokenOf md) t) -∗ Φ m)

end defsHF

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]


/-- **`etcdTxnSpecMW` at the messages' models** (S2, heap-free vocabulary, 2026-11-23: the spec is
`etcdTxnSpecMW`, over the models alone, what a service table holds; this is its form at the message
types). -/
def etcdTxnSpecM (on : Bool) (T : IProp GF) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (cid mid : w64) :
    GrpcSpecMd (GF := GF) pbTxnRequest pbTxnResponse :=
  etcdTxnSpecMW on T E ρ γr cid mid

end defs

section defsHF
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF] [GoLocalContext]
variable [sem : go.Semantics]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **etcd's `Compact` in the auth mode `on`**: specified with auth off only. With auth on Go's
`kvServer.Compact` first checks that the caller is admin (`key.go:139–142`, `isPermitted`), which no
spec here covers, so the spec is then vacuous (`etcdCompactSpec`'s with `⌜on = false⌝`). -/
def etcdCompactSpecMW (on : Bool) (E : apply.AEnv GF) (ρ : ReqNames) (cid mid : w64) :
    CompactReqM → (CompactRespM → IProp GF) → IProp GF :=
  fun o Φ => iprop(⌜on = false⌝ ∗ etcdCompactSpecW E ρ.rd cid mid o Φ)

end defsHF

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]


/-- **`etcdCompactSpecMW` at the messages' models** (S2, heap-free vocabulary, 2026-11-23: the spec
is `etcdCompactSpecMW`, over the models alone, what a service table holds; this is its form at the
message types). -/
def etcdCompactSpecM (on : Bool) (E : apply.AEnv GF) (ρ : ReqNames) (cid mid : w64) :
    GrpcSpec (GF := GF) pbCompactionRequest pbCompactionResponse :=
  etcdCompactSpecMW on E ρ cid mid

/-! ### The KV methods' specs: the off and on texts as views of the spec over the mode

With auth on, the `…SpecOn` text gives the spec over the mode (the gates applied to `on = true`);
with auth off, `etcd…Spec`'s gives it after an update (the update `kvOpAu1` told no grant,
`v3rpc.kvDepOwnM_of_dep`; the auth index's lower bound `0`, `authPubLbM_zero`). A registration of
the spec over the mode is then one of either text (`isGrpcRpcMd_mono`, `isGrpcRpcMd_mono_upd`). -/

/-- An update told no grant is one in any mode (`v3rpc.kvDepOwnM_of_dep` at a write). -/
theorem kvOpAuM_of_au1 (on : Bool) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (tok : Option GoString)
    (op : KVOp) (Q : KVState → IProp GF) :
    kvOpAu1 (GF := GF) ρ.rd.kv op Q ⊢ |==> v3rpc.kvOpAuM on (srvTLSId s) E ρ tok op Q :=
  v3rpc.kvDepOwnM_of_dep on s E ρ ρ.rd tok (.op1 op Q)

/-- With auth on, an update told the grant is one in the mode (`v3rpc.kvDepOwnM_true` at a write). -/
theorem kvOpAuM_of_on (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (tok : Option GoString) (op : KVOp) (Q : KVState → IProp GF) :
    v3rpc.kvOpAuOn (GF := GF) (srvTLSId s) E ρ tok op Q ⊢ v3rpc.kvOpAuM true (srvTLSId s) E ρ tok op Q :=
  (v3rpc.kvDepOwnM_true s E ρ ρ.rd tok (.op1 op Q)).2

theorem etcdPutSpecM_true (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (cid mid : w64) :
    ∀ md o Φ Ψe, etcdPutSpecOn (GF := GF) (srvTLSId s) E ρ cid mid md o Φ Ψe ⊢ etcdPutSpecM true (srvTLSId s) E ρ cid mid md o Φ Ψe := by
  intro md o Φ Ψe
  unfold etcdPutSpecOn etcdPutSpecOnW etcdPutSpecM etcdPutSpecMW
  iintro ⟨#HΨe, %F, #HF, %Q, %Hl, Hau, Hk⟩
  iframe HΨe
  iexists F
  iframe HF
  iexists Q
  isplitr
  · ipureintro; exact Hl.imp id (fun h => ⟨rfl, h⟩)
  isplitl [Hau]
  · iapply (kvOpAuM_of_on s E ρ _ _ Q) $$ Hau
  iintro %m Hm - Hg
  iapply Hk $$ Hm
  iapply Hg
  ipureintro; rfl

theorem etcdDeleteSpecM_true (s : Loc) (E : apply.AEnv GF)
    (ρ : ReqNames) (cid mid : w64) :
    ∀ md o Φ Ψe, etcdDeleteSpecOn (GF := GF) (srvTLSId s) E ρ cid mid md o Φ Ψe ⊢
      etcdDeleteSpecM true (srvTLSId s) E ρ cid mid md o Φ Ψe := by
  intro md o Φ Ψe
  unfold etcdDeleteSpecOn etcdDeleteSpecOnW etcdDeleteSpecM etcdDeleteSpecMW
  iintro ⟨#HΨe, %Hsh, %F, #HF, %Q, %Hz, Hau, Hk⟩
  iframe HΨe
  isplitr
  · ipureintro; exact fun _ => Hsh
  iexists F
  iframe HF
  iexists Q
  isplitr
  · ipureintro; exact Hz
  isplitl [Hau]
  · iapply (kvOpAuM_of_on s E ρ _ _ Q) $$ Hau
  iintro %m Hm Hg
  iapply Hk $$ Hm
  iapply Hg
  ipureintro; rfl

theorem etcdRangeSpecM_true (s : Loc) (E : apply.AEnv GF)
    (γr : ReadNames) (cid mid : w64) :
    ∀ md o Φ Ψe, etcdRangeSpecOn (GF := GF) (srvTLSId s) E γr cid mid md o Φ Ψe ⊢
      etcdRangeSpecM true (srvTLSId s) E γr cid mid md o Φ Ψe := by
  intro md o Φ Ψe
  unfold etcdRangeSpecOn etcdRangeSpecOnW etcdRangeSpecM etcdRangeSpecMW
  iintro ⟨#HΨe, %c, %F, %Q, %n, #Hc, #HF, #Hn, Hq, Hk⟩
  iexists c, F, Q, n
  iframe Hc HF Hn Hq
  isplitr
  · iintro -; iexact HΨe
  isplitr
  · isplit
    · iintro -; iapply HΨe
    · iintro -; iapply HΨe
  iintro %m Hm Hg
  iapply Hk $$ Hm
  iapply Hg
  ipureintro; rfl

theorem etcdTxnSpecM_true (s : Loc) (E : apply.AEnv GF)
    (ρ : ReqNames) (γr : ReadNames) (cid mid : w64) :
    ∀ md t Φ Ψe, etcdTxnSpecOn (GF := GF) (srvTLSId s) E ρ γr cid mid md t Φ Ψe ⊢
      etcdTxnSpecM true (srvTLSId s) E ρ γr cid mid md t Φ Ψe := by
  intro md t Φ Ψe
  unfold etcdTxnSpecOn etcdTxnSpecOnW etcdTxnSpecM etcdTxnSpecMW
  iintro ⟨#HΨe, %Hpl, %Q, Hd, %c, %F, %n, #Hc, #HF, #Hn, Hk⟩
  iframe HΨe
  isplitr
  · ipureintro; exact ⟨Hpl.1, fun _ => Hpl.2⟩
  iexists Q
  isplitl [Hd]
  · icases Hd with (%H | ⟨%H, Ha⟩ | ⟨%H, Ha⟩)
    · ileft; ipureintro; exact H
    · iright; ileft; isplitr
      · ipureintro; exact H
      iexact Ha
    · iright; iright; isplitr
      · ipureintro; exact ⟨H.1, H.2.1.imp id (fun h => ⟨rfl, h⟩), H.2.2⟩
      iapply (kvOpAuM_of_on s E ρ _ _ Q) $$ Ha
  iexists c, F, n
  iframe Hc HF Hn
  iintro %m Hm - Hg
  iapply Hk $$ Hm
  iapply Hg
  ipureintro; rfl

theorem etcdPutSpecM_false (s : Loc) (E : apply.AEnv GF)
    (ρ : ReqNames) (cid mid : w64) :
    ∀ md o Φ Ψe, GrpcSpec.md (etcdPutSpec (GF := GF) E ρ.rd cid mid) md o Φ Ψe ⊢
      |==> etcdPutSpecM false (srvTLSId s) E ρ cid mid md o Φ Ψe := by
  intro md o Φ Ψe
  unfold GrpcSpec.md etcdPutSpec etcdPutSpecW etcdPutSpecM etcdPutSpecMW
  iintro ⟨⟨%F, #HF, %Q, %Hl, Hau, Hk⟩, #HΨe⟩
  imod (kvOpAuM_of_au1 _ s E ρ (auth.mdTokenOf md) (.put o) Q) $$ Hau with Hau
  imodintro
  iframe HΨe
  iexists F
  iframe HF
  iexists Q
  isplitr
  · ipureintro; exact Or.inl Hl
  isplitl [Hau]
  · iexact Hau
  iintro %m Hm Hr -
  iapply Hk $$ Hm
  iapply Hr
  ipureintro; rfl

theorem etcdDeleteSpecM_false (s : Loc) (E : apply.AEnv GF)
    (ρ : ReqNames) (cid mid : w64) :
    ∀ md o Φ Ψe, GrpcSpec.md (etcdDeleteSpec (GF := GF) E ρ.rd cid mid) md o Φ Ψe ⊢
      |==> etcdDeleteSpecM false (srvTLSId s) E ρ cid mid md o Φ Ψe := by
  intro md o Φ Ψe
  unfold GrpcSpec.md etcdDeleteSpec etcdDeleteSpecW etcdDeleteSpecM etcdDeleteSpecMW
  iintro ⟨⟨%F, #HF, %Q, %Hz, Hau, Hk⟩, #HΨe⟩
  imod (kvOpAuM_of_au1 _ s E ρ (auth.mdTokenOf md) (.deleteRange o) Q) $$ Hau with Hau
  imodintro
  iframe HΨe
  isplitr
  · ipureintro; intro h; cases h
  iexists F
  iframe HF
  iexists Q
  isplitr
  · ipureintro; exact Hz
  isplitl [Hau]
  · iexact Hau
  iintro %m Hm -
  iapply Hk $$ Hm

theorem etcdRangeSpecM_false [go_etcd_io.etcd.server.v3.etcdserver.Assumptions] (s : Loc) (E : apply.AEnv GF)
    (γr : ReadNames) (cid mid : w64) :
    ∀ md o Φ Ψe, GrpcSpec.md (etcdRangeSpec (GF := GF) E γr cid mid) md o Φ Ψe ⊢
      |==> etcdRangeSpecM false (srvTLSId s) E γr cid mid md o Φ Ψe := by
  intro md o Φ Ψe
  unfold GrpcSpec.md etcdRangeSpec etcdRangeSpecW etcdRangeSpecM etcdRangeSpecMW
  iintro ⟨⟨%c, %F, %Q, #Hc, #HF, Hq, Hk⟩, #HΨe⟩
  imod (authPubLbM_zero (GF := GF) E.authMode) with #Hn
  imodintro
  iexists c, F, Q, 0
  iframe Hc HF Hn Hq
  isplitr
  · iintro -; iexact HΨe
  isplitr
  · isplit
    · iintro -; iapply HΨe
    · iintro -; iapply HΨe
  iintro %m Hm -
  iapply Hk $$ Hm

/-- `etcdRangeSpecE`'s caller meets the spec over the mode with auth off (the auth index's lower
bound `0`, `authPubLbM_zero`; the auth gate `on = true` vacuous). -/
theorem etcdRangeSpecE_M [go_etcd_io.etcd.server.v3.etcdserver.Assumptions] (s : Loc) (E : apply.AEnv GF)
    (γr : ReadNames) (cid mid : w64) :
    ∀ md o Φ Ψe, etcdRangeSpecE (GF := GF) E γr cid mid md o Φ Ψe ⊢
      |==> etcdRangeSpecM false (srvTLSId s) E γr cid mid md o Φ Ψe := by
  intro md o Φ Ψe
  unfold etcdRangeSpecE etcdRangeSpecEW etcdRangeSpecM etcdRangeSpecMW
  iintro ⟨%c, %F, %Q, #Hc, #HF, Hq, Hck, He, Hk⟩
  imod (authPubLbM_zero (GF := GF) E.authMode) with #Hn
  imodintro
  iexists c, F, Q, 0
  iframe Hc HF Hn Hq Hck He
  iintro %m Hm -
  iapply Hk $$ Hm

theorem etcdTxnSpecM_false [go_etcd_io.etcd.server.v3.etcdserver.Assumptions] (s : Loc) (E : apply.AEnv GF)
    (ρ : ReqNames) (γr : ReadNames) (cid mid : w64) :
    ∀ md t Φ Ψe, GrpcSpec.md (etcdTxnSpec (GF := GF) E ρ.rd γr cid mid) md t Φ Ψe ⊢
      |==> etcdTxnSpecM false (srvTLSId s) E ρ γr cid mid md t Φ Ψe := by
  intro md t Φ Ψe
  unfold GrpcSpec.md etcdTxnSpec etcdTxnSpecW etcdTxnSpecM etcdTxnSpecMW
  iintro ⟨⟨%Hpl, %Q, Hd, %c, %F, #Hc, #HF, Hk⟩, #HΨe⟩
  imod (authPubLbM_zero (GF := GF) E.authMode) with #Hn
  ihave Hd : iprop(|==> ((⌜txn.txnReadonly t = true ∧ Q = fun _ => iprop(True)⌝ ∨
        (⌜txn.txnReadonly t = true ∧ txn.txnSerializable t = false⌝ ∗ kvReadAu γr.kv Q) ∨
        (⌜txn.txnReadonly t = false ∧
            (txn.txnPlain t ∨ (false = true ∧ ρ.kv.lm = .revocable ∧ txnPlainL t)) ∧
            txnNoZeroEnd t ∧ txnNestOk t⌝ ∗
          v3rpc.kvOpAuM false (srvTLSId s) E ρ (auth.mdTokenOf md) (.txn t) Q)))) $$ [Hd]
  · icases Hd with (%H | ⟨%H, Ha⟩ | ⟨%H, Ha⟩)
    · imodintro; ileft; ipureintro; exact H
    · imodintro; iright; ileft; isplitr
      · ipureintro; exact H
      iexact Ha
    · imod (kvOpAuM_of_au1 _ s E ρ (auth.mdTokenOf md) (.txn t) Q) $$ Ha with Ha
      imodintro; iright; iright; isplitr
      · ipureintro; exact ⟨H.1, Or.inl H.2.1, H.2.2, txnNestOk_of_plain t Hpl.1 Hpl.2⟩
      iexact Ha
  imod Hd with Hd
  imodintro
  iframe HΨe
  isplitr
  · ipureintro; exact ⟨fun _ => Hpl.2, fun h => by cases h⟩
  iexists Q
  iframe Hd
  iexists c, F, 0
  iframe Hc HF Hn
  iintro %m Hm Hr -
  iapply Hk $$ Hm
  iapply Hr
  ipureintro; rfl

theorem etcdCompactSpecM_false (E : apply.AEnv GF) (ρ : ReqNames)
    (cid mid : w64) :
    ∀ md o Φ Ψe, GrpcSpec.md (etcdCompactSpec (GF := GF) E ρ.rd cid mid) md o Φ Ψe ⊢
      |==> GrpcSpec.md (etcdCompactSpecM false E ρ cid mid) md o Φ Ψe := by
  intro md o Φ Ψe
  unfold GrpcSpec.md etcdCompactSpecM etcdCompactSpecMW etcdCompactSpec
  iintro ⟨H, #Hd⟩
  imodintro
  isplitl [H]
  · iframe H
    ipureintro; rfl
  · iexact Hd

/-- **A client write's grant** (persistent; the auth-mode merge's 5a, 2026-10-29): the write's grant
(`v3rpc.opGrantT`) at the token of some attempt of the call on `conn` with a context of outgoing
metadata `om` (the caller does not know which attempt's metadata the server saw). (errdesc stage 1,
2026-11-20: indexed by the metadata `om`, until then by the context, through the pure
`metadata.outgoingOf`.) -/
def clientGrant (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (conn : Loc) (om : GrpcMd)
    (op : KVOp) (L₀ : List EntryModel) (σ : KVState) : IProp GF :=
  iprop(∃ md, ⌜clientAttemptMd conn om md⌝ ∗ v3rpc.opGrantT (srvTLSId s) E ρ (auth.mdTokenOf md) op L₀ σ)

/-- **A client write's update with auth on** (5a): `v3rpc.kvOpAuOn`'s, fired at most once, at a
lower bound `L₀` of the requested log the caller holds, told the grant of some attempt
(`clientGrant`) when it fires. -/
def clientOpAuOn (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (conn : Loc) (om : GrpcMd)
    (op : KVOp) (Q : KVState → IProp GF) : IProp GF :=
  iprop(∃ L₀ : List EntryModel, srvReqLogLb ρ.raft L₀ ∗
    kvAu1G ρ.kv (kvOpStep op) (clientGrant s E ρ conn om op L₀) Q)

/-- A client's update is one at the token of each of its attempts. -/
theorem clientOpAuOn_attempt (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (conn : Loc)
    (om : GrpcMd) (md : GrpcMd) (op : KVOp) (Q : KVState → IProp GF)
    (hmd : clientAttemptMd conn om md) :
    clientOpAuOn (GF := GF) s E ρ conn om op Q ⊢ v3rpc.kvOpAuOn (srvTLSId s) E ρ (auth.mdTokenOf md) op Q := by
  unfold clientOpAuOn v3rpc.kvOpAuOn
  iintro ⟨%L₀, #H0, Hau⟩
  iexists L₀
  iframe H0
  iapply (kvAu1G_mono ρ.kv (kvOpStep op) (clientGrant s E ρ conn om op L₀)
    (v3rpc.opGrantT (srvTLSId s) E ρ (auth.mdTokenOf md) op L₀) Q ?_) $$ Hau
  intro σ
  unfold clientGrant
  iintro Hg
  iexists md
  iframe Hg
  ipureintro; exact hmd

/-- An update not told the grant is one (at the empty lower bound). -/
theorem clientOpAuOn_of_au1 (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (conn : Loc)
    (om : GrpcMd) (op : KVOp) (Q : KVState → IProp GF) :
    kvOpAu1 (GF := GF) ρ.kv op Q ⊢ |==> clientOpAuOn s E ρ conn om op Q := by
  iintro H
  imod srvReqLogLb_nil (GF := GF) ρ.raft with #H0
  imodintro
  unfold clientOpAuOn
  iexists []
  iframe H0
  unfold kvOpAu1
  iapply kvAu1_G $$ H

/-- **A transaction's update with auth on** (5a): `txnUpdAt`'s, a writing one's update told the
grant of some attempt of the call (`clientOpAuOn`). -/
def txnUpdAtOn (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (conn : Loc) (om : GrpcMd)
    (γr : ReadNames) (t : TxnModel) (Q : KVState → IProp GF) : IProp GF :=
  iprop(⌜txn.txnReadonly t = true ∧ Q = fun _ => iprop(True)⌝ ∨
    (⌜txn.txnReadonly t = true ∧ txn.txnSerializable t = false⌝ ∗ kvReadAu γr.kv Q) ∨
    (⌜txn.txnReadonly t = false ∧ (txn.txnPlain t ∨ (ρ.kv.lm = .revocable ∧ txnPlainL t)) ∧
        txnNoZeroEnd t ∧ txnNestOk t⌝ ∗
      clientOpAuOn s E ρ conn om (.txn t) Q))

/-- A writing transaction's update, from its shape and its update (L13). -/
theorem txnUpdAtOn_write (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (conn : Loc)
    (om : GrpcMd) (γr : ReadNames) (t : TxnModel) (Q : KVState → IProp GF)
    (h1 : txn.txnReadonly t = false) (h2 : txn.txnPlain t) (h3 : txnNoZeroEnd t)
    (h4 : txnNestOk t) :
    clientOpAuOn (GF := GF) s E ρ conn om (.txn t) Q ⊢ txnUpdAtOn s E ρ conn om γr t Q := by
  iintro H
  unfold txnUpdAtOn
  iright; iright
  isplitl []
  · ipureintro; exact ⟨h1, Or.inl h2, h3, h4⟩
  iexact H

section monoT
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-! ### O2: monotonicity in the TLS fact (2026-11-23)

Each KV table spec is antitone in `T`: a registration at `T1` (the server's, `srvTLSId s`) serves a
caller at `T2` (the table's, `⌜tls = true⌝`) when `□ (T1 -∗ T2)` (`isGrpcRpcMd_mono`, with
`srvTLSId_iff` at the server's config). -/

open Iris.ProofMode in
theorem txnAuthOn_mono (T1 T2 : IProp GF) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (c : w64)
    (n : Nat) (tok : Option GoString) (t : TxnModel) :
    iprop(□ (T1 -∗ T2)) ∗ txnAuthOn T1 E ρ γr c n tok t ⊢ txnAuthOn T2 E ρ γr c n tok t := by
  unfold txnAuthOn
  split
  · exact v3rpc.txnAuthed_mono T1 T2 E γr c n tok t
  · iintro ⟨#HT, %tw, %h, H⟩
    iexists tw
    isplitr
    · ipureintro; exact h
    iapply v3rpc.writeGrantOn_mono T1 T2
    iframe HT H

open Iris.ProofMode in
theorem etcdPutSpecOnW_mono (T1 T2 : IProp GF) (E : apply.AEnv GF) (ρ : ReqNames) (cid mid : w64)
    (md : GrpcMd) (o : OpFull) (Φ : PutRespM → IProp GF) (Ψe : GoString → IProp GF) :
    iprop(□ (T1 -∗ T2)) ∗ etcdPutSpecOnW T2 E ρ cid mid md o Φ Ψe ⊢ etcdPutSpecOnW T1 E ρ cid mid md o Φ Ψe := by
  unfold etcdPutSpecOnW
  iintro ⟨#HT, He, %F, HF, %Q, %hl, Hau, Hk⟩
  iframe He
  iexists F
  iframe HF
  iexists Q
  isplitr
  · ipureintro; exact hl
  isplitl [Hau]
  · iapply v3rpc.kvOpAuOn_mono T1 T2
    iframe HT Hau
  iintro %m Hr Hg
  iapply Hk $$ Hr
  iapply v3rpc.writeGrantOn_mono T1 T2
  iframe HT Hg

open Iris.ProofMode in
theorem etcdDeleteSpecOnW_mono (T1 T2 : IProp GF) (E : apply.AEnv GF) (ρ : ReqNames) (cid mid : w64)
    (md : GrpcMd) (o : OpFull) (Φ : DelRespM → IProp GF) (Ψe : GoString → IProp GF) :
    iprop(□ (T1 -∗ T2)) ∗ etcdDeleteSpecOnW T2 E ρ cid mid md o Φ Ψe ⊢
      etcdDeleteSpecOnW T1 E ρ cid mid md o Φ Ψe := by
  unfold etcdDeleteSpecOnW
  iintro ⟨#HT, He, %hs, %F, HF, %Q, %hl, Hau, Hk⟩
  iframe He
  isplitr
  · ipureintro; exact hs
  iexists F
  iframe HF
  iexists Q
  isplitr
  · ipureintro; exact hl
  isplitl [Hau]
  · iapply v3rpc.kvOpAuOn_mono T1 T2
    iframe HT Hau
  iintro %m Hr Hg
  iapply Hk $$ Hr
  iapply v3rpc.writeGrantOn_mono T1 T2
  iframe HT Hg

open Iris.ProofMode in
theorem etcdRangeSpecOnW_mono (T1 T2 : IProp GF) (E : apply.AEnv GF) (γr : ReadNames) (cid mid : w64)
    (md : GrpcMd) (o : OpFull) (Φ : RangeRespM → IProp GF) (Ψe : GoString → IProp GF) :
    iprop(□ (T1 -∗ T2)) ∗ etcdRangeSpecOnW T2 E γr cid mid md o Φ Ψe ⊢
      etcdRangeSpecOnW T1 E γr cid mid md o Φ Ψe := by
  unfold etcdRangeSpecOnW
  iintro ⟨#HT, He, %c, %F, %Q, %n, Hc, HF, Hp, HQ, Hk⟩
  iframe He
  iexists c, F, Q, n
  iframe Hc HF Hp HQ
  iintro %m Hr Ha
  iapply Hk $$ Hr
  iapply v3rpc.rangeAuthed_mono T1 T2
  iframe HT Ha

open Iris.ProofMode in
theorem etcdTxnSpecOnW_mono (T1 T2 : IProp GF) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (cid mid : w64) (md : GrpcMd) (t : TxnModel) (Φ : TxnRespM → IProp GF) (Ψe : GoString → IProp GF) :
    iprop(□ (T1 -∗ T2)) ∗ etcdTxnSpecOnW T2 E ρ γr cid mid md t Φ Ψe ⊢
      etcdTxnSpecOnW T1 E ρ γr cid mid md t Φ Ψe := by
  unfold etcdTxnSpecOnW
  iintro ⟨#HT, He, %hs, %Q, HQ, %c, %F, %n, Hc, HF, Hp, Hk⟩
  iframe He
  isplitr
  · ipureintro; exact hs
  iexists Q
  isplitl [HQ]
  · icases HQ with (HQ | (HQ | ⟨%h, Hau⟩))
    · ileft; iexact HQ
    · iright; ileft; iexact HQ
    · iright; iright
      isplitr
      · ipureintro; exact h
      iapply v3rpc.kvOpAuOn_mono T1 T2
      iframe HT Hau
  iexists c, F, n
  iframe Hc HF Hp
  iintro %m Hr Ha
  iapply Hk $$ Hr
  iapply txnAuthOn_mono T1 T2
  iframe HT Ha

open Iris.ProofMode in
theorem etcdPutSpecMW_mono (on : Bool) (T1 T2 : IProp GF) (E : apply.AEnv GF) (ρ : ReqNames)
    (cid mid : w64) (md : GrpcMd) (o : OpFull) (Φ : PutRespM → IProp GF) (Ψe : GoString → IProp GF) :
    iprop(□ (T1 -∗ T2)) ∗ etcdPutSpecMW on T2 E ρ cid mid md o Φ Ψe ⊢
      etcdPutSpecMW on T1 E ρ cid mid md o Φ Ψe := by
  unfold etcdPutSpecMW
  iintro ⟨#HT, He, %F, HF, %Q, %hl, Hau, Hk⟩
  iframe He
  iexists F
  iframe HF
  iexists Q
  isplitr
  · ipureintro; exact hl
  isplitl [Hau]
  · iapply v3rpc.kvOpAuM_mono on T1 T2
    iframe HT Hau
  iintro %m Hr Hl Hg
  iapply Hk $$ Hr Hl
  iintro %h
  iapply v3rpc.writeGrantOn_mono T1 T2
  iframe HT
  iapply Hg $$ %h

open Iris.ProofMode in
theorem etcdDeleteSpecMW_mono (on : Bool) (T1 T2 : IProp GF) (E : apply.AEnv GF) (ρ : ReqNames)
    (cid mid : w64) (md : GrpcMd) (o : OpFull) (Φ : DelRespM → IProp GF) (Ψe : GoString → IProp GF) :
    iprop(□ (T1 -∗ T2)) ∗ etcdDeleteSpecMW on T2 E ρ cid mid md o Φ Ψe ⊢
      etcdDeleteSpecMW on T1 E ρ cid mid md o Φ Ψe := by
  unfold etcdDeleteSpecMW
  iintro ⟨#HT, He, %hs, %F, HF, %Q, %hl, Hau, Hk⟩
  iframe He
  isplitr
  · ipureintro; exact hs
  iexists F
  iframe HF
  iexists Q
  isplitr
  · ipureintro; exact hl
  isplitl [Hau]
  · iapply v3rpc.kvOpAuM_mono on T1 T2
    iframe HT Hau
  iintro %m Hr Hg
  iapply Hk $$ Hr
  iintro %h
  iapply v3rpc.writeGrantOn_mono T1 T2
  iframe HT
  iapply Hg $$ %h

open Iris.ProofMode in
theorem etcdRangeSpecMW_mono (on : Bool) (T1 T2 : IProp GF) (E : apply.AEnv GF) (γr : ReadNames)
    (cid mid : w64) (md : GrpcMd) (o : OpFull) (Φ : RangeRespM → IProp GF) (Ψe : GoString → IProp GF) :
    iprop(□ (T1 -∗ T2)) ∗ etcdRangeSpecMW on T2 E γr cid mid md o Φ Ψe ⊢
      etcdRangeSpecMW on T1 E γr cid mid md o Φ Ψe := by
  unfold etcdRangeSpecMW
  iintro ⟨#HT, %c, %F, %Q, %n, Hc, HF, Hp, HQ, He, Hf, Hk⟩
  iexists c, F, Q, n
  iframe Hc HF Hp HQ He Hf
  iintro %m Hr Ha
  iapply Hk $$ Hr
  iintro %h
  iapply v3rpc.rangeAuthed_mono T1 T2
  iframe HT
  iapply Ha $$ %h

open Iris.ProofMode in
theorem etcdTxnSpecMW_mono (on : Bool) (T1 T2 : IProp GF) (E : apply.AEnv GF) (ρ : ReqNames)
    (γr : ReadNames) (cid mid : w64) (md : GrpcMd) (t : TxnModel) (Φ : TxnRespM → IProp GF)
    (Ψe : GoString → IProp GF) :
    iprop(□ (T1 -∗ T2)) ∗ etcdTxnSpecMW on T2 E ρ γr cid mid md t Φ Ψe ⊢
      etcdTxnSpecMW on T1 E ρ γr cid mid md t Φ Ψe := by
  unfold etcdTxnSpecMW
  iintro ⟨#HT, He, %hs, %Q, HQ, %c, %F, %n, Hc, HF, Hp, Hk⟩
  iframe He
  isplitr
  · ipureintro; exact hs
  iexists Q
  isplitl [HQ]
  · icases HQ with (HQ | (HQ | ⟨%h, Hau⟩))
    · ileft; iexact HQ
    · iright; ileft; iexact HQ
    · iright; iright
      isplitr
      · ipureintro; exact h
      iapply v3rpc.kvOpAuM_mono on T1 T2
      iframe HT Hau
  iexists c, F, n
  iframe Hc HF Hp
  iintro %m Hr Hl Ha
  iapply Hk $$ Hr Hl
  iintro %h
  iapply txnAuthOn_mono T1 T2
  iframe HT
  iapply Ha $$ %h

end monoT

end defs

end client
end EtcdGrove
end Perennial
