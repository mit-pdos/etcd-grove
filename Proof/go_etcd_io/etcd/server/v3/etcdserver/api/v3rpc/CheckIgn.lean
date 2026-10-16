/-
**The gRPC checks exclude the `IgnoreValue`/`IgnoreLease` panic** (etcd#22395; the finding
`issues/etcd-txn-delete-then-ignore-put.md`): a branch `ops` passing `checkRequestOp` and
`checkIntervals` (with no later-sibling delete of a nested put, `siblingSafeL`, the other finding
of `checkIntervals`), run by the server from its read view `s0`, meets the run's premise on every
put that needs the previous key-value (`txn.IgnOk`, weak: the key is found when the put runs, or
was already missing at `s0`, when `checkTxn` rejects the transaction first). That is the premise
the apply thread's `Txn` takes (`txn.TxnPre`) to exclude `put`'s `prevKV.KVs[0]` of an empty list.
The gets' own premises (`GetOk`) are not the checks' business: `OpsGetsOk` keeps them, and
`check_gives_ignOk` turns them into the whole `OpsOk true`.

Open: the premise `siblingSafeL` comes from going through `check_gives_nodup`; the panic needs a
delete that runs *before* the put, and `checkIntervals` checks every such order (the unchecked one,
an earlier sibling's put and a later sibling's delete, runs the put first), so the statement
without it is believed true but not proved. Nor is `check_gives_ignOk` yet linked to the apply
thread's `txn.TxnPre` (the request's branch as the apply's `t.branch`, `s0 = stateAfter log`).

On the pinned code `check_gives_nodup` needs `noFromKeyDelL`, so this would hold only without
from-key deletes: `Then(OpDelete(k, WithFromKey()), OpPut(k, "", WithIgnoreValue()))` passes the
pinned `checkIntervals` and breaks `IgnOk` (the finding's reproduction). Lean-first (no Rocq
counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.CheckNodup
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.LogLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace v3rpc

open txn mvcc

mutual
/-- The run's premises on its gets only (`OpOk` without the `IgnOk` of the puts). -/
def OpGetsOk (s0 : List EtcdKv) (r : w64) : List EtcdKv → TxnOp → Prop
  | s, .get o => GetOk s o
  | _, .put _ _ _ => True
  | _, .delete _ => True
  | _, .putKeep _ _ => True
  | _, .putIgnVal _ _ => True
  | s, .txn cs ts es =>
    match cs.all (cmpHolds s0) with
    | true => OpsGetsOk s0 r s ts
    | false => OpsGetsOk s0 r s es

def OpsGetsOk (s0 : List EtcdKv) (r : w64) : List EtcdKv → List TxnOp → Prop
  | _, [] => True
  | s, op :: ops => OpGetsOk s0 r s op ∧ OpsGetsOk s0 r (applyChanges r s (srvOp s0 r s op).1) ops
end

/-- A key present at `s` that the changes `cs` do not delete is present after them. -/
theorem findKey_applyChanges_keep (r : w64) (k : GoString) :
    ∀ (cs : List Change) (s : List EtcdKv), s.Pairwise etcdKvLess → (findKey k s).isSome →
      k ∉ delKeysOf cs → (findKey k (applyChanges r s cs)).isSome
  | [], s, _, h, _ => h
  | c :: cs, s, hs, h, hd => by
    have hd' : k ∉ delKeysOf cs := fun hk => hd (by
      have : delKeysOf (c :: cs) = delKeysOf [c] ++ delKeysOf cs := by
        simp [delKeysOf, List.filterMap_cons]
        cases c <;> simp
      rw [this]; exact List.mem_append_right _ hk)
    show (findKey k (applyChanges r (applyChange r s c) cs)).isSome
    apply findKey_applyChanges_keep r k cs _ (applyChange_sorted hs r c) _ hd'
    cases c with
    | put k' v l =>
      simp only [applyChange]
      by_cases hk : k' = k
      · subst hk
        obtain ⟨nv, hnv, -⟩ := findKey_putKv_self hs r k' v l
        rw [hnv]; rfl
      · rw [findKey_putKv_other hs r k k' v l hk]; exact h
    | del k' =>
      simp only [applyChange]
      have hk : k' ≠ k := fun he => hd (by subst he; simp [delKeysOf])
      rw [findKey_filter_ne k k' s]
      simpa [hk] using h

mutual
theorem opOk_of_check (s0 : List EtcdKv) (r : w64) :
    ∀ (op : TxnOp) (s : List EtcdKv), OpGetsOk s0 r s op →
      (∀ k ∈ putKeysOf (srvOp s0 r s op).1, (findKey k s0).isSome → (findKey k s).isSome) →
      (∀ k ∈ putKeysOf (srvOp s0 r s op).1, k ∉ delKeysOf (srvOp s0 r s op).1) →
      s.Pairwise etcdKvLess → OpOk true s0 r s op
  | .get o, s, hg, _, _, _ => hg
  | .put _ _ _, _, _, _, _, _ => trivial
  | .delete _, _, _, _, _, _ => trivial
  | .putKeep k v, s, _, hp, _, _ => by
    simp only [OpOk, IgnOk]
    cases h0 : findKey k s0 with
    | none => exact Or.inr ⟨trivial, rfl⟩
    | some _ =>
      exact Or.inl (hp k (by simp [srvOp, putKeysOf]) (by simp [h0]))
  | .putIgnVal k l, s, _, hp, _, _ => by
    simp only [OpOk, IgnOk]
    cases h0 : findKey k s0 with
    | none => exact Or.inr ⟨trivial, rfl⟩
    | some _ =>
      exact Or.inl (hp k (by simp [srvOp, putKeysOf]) (by simp [h0]))
  | .txn cs ts es, s, hg, hp, hd, hs => by
    simp only [OpOk, OpGetsOk] at hg ⊢
    rw [srvOp_txn] at hp hd
    cases hc : cs.all (cmpHolds s0)
    · rw [hc] at hg hp hd
      exact opsOk_of_check s0 r es s hg hp hd hs
    · rw [hc] at hg hp hd
      exact opsOk_of_check s0 r ts s hg hp hd hs

theorem opsOk_of_check (s0 : List EtcdKv) (r : w64) :
    ∀ (ops : List TxnOp) (s : List EtcdKv), OpsGetsOk s0 r s ops →
      (∀ k ∈ putKeysOf (srvOps s0 r s ops).1, (findKey k s0).isSome → (findKey k s).isSome) →
      (∀ k ∈ putKeysOf (srvOps s0 r s ops).1, k ∉ delKeysOf (srvOps s0 r s ops).1) →
      s.Pairwise etcdKvLess → OpsOk true s0 r s ops
  | [], _, _, _, _, _ => trivial
  | op :: ops, s, hg, hp, hd, hs => by
    simp only [OpsGetsOk] at hg
    simp only [OpsOk]
    rw [srvOps_cons] at hp hd
    simp only [putKeysOf_append, delKeysOf_append, List.mem_append] at hp hd
    refine ⟨opOk_of_check s0 r op s hg.1 (fun k hk => hp k (Or.inl hk))
      (fun k hk hk' => hd k (Or.inl hk) (Or.inl hk')) hs, ?_⟩
    refine opsOk_of_check s0 r ops _ hg.2 (fun k hk h0 => ?_)
      (fun k hk hk' => hd k (Or.inr hk) (Or.inr hk')) (applyChanges_sorted r _ hs)
    exact findKey_applyChanges_keep r k _ s hs (hp k (Or.inr hk) h0)
      (fun hk' => hd k (Or.inr hk) (Or.inl hk'))
end

/-- **`check_gives_ignOk`**: a branch passing the gRPC layer's checks (`checkRequestOp` at some
budget, `checkIntervals`), with no later-sibling delete of a nested put, run by the server from
its read view `s0` (sorted: every state is, `mvcc.stateAfter_sorted`) whose gets are within the
model, meets the run's whole premise (`OpsOk true`, `txn.TxnPre`'s): no `IgnoreValue` or
`IgnoreLease` put finds its key deleted by the transaction (see the file header). -/
theorem check_gives_ignOk (n : Int) (ops : List ReqOp) (tops : List TxnOp) (s0 : List EtcdKv)
    (r : w64) (hs0 : s0.Pairwise etcdKvLess) (htx : ReqOp.toTxnOps ops = some tops)
    (hck : opsCheck n ops = none) (hsib : ReqOp.siblingSafeL ops) (hiv : intervalsOk ops)
    (hg : OpsGetsOk s0 r s0 tops) : OpsOk true s0 r s0 tops :=
  opsOk_of_check s0 r tops s0 hg (fun _ _ h => h)
    (check_gives_nodup n ops tops s0 s0 r htx hck hsib hiv).2 hs0

end v3rpc
end EtcdGrove
end Perennial
