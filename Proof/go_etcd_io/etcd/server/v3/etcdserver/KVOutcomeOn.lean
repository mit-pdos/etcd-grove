/-
**The auth applier's outcome is the mode-`on` model's** (the auth plan's E2v, 2026-10-26;
`notes/decisions.md`, "E2v of the auth plan"). Lean-first (no Rocq counterpart).

E2s's auth applier decides a KV request's outcome at the latest state, one checked permission at a
time (`apply.authOutL`): the auth layer's rejection with a checked permission refused there, or
the inner chain's outcome with every one granted there. E2t's apply step in the mode `on`
(`kv_applied_out_on`) takes the apply thread's outcome as the relation `outcomeOn`. Here the first
gives the second, for a plain KV request (not an admin one) above the consistent index at the
start chain with auth on and no alarm (`apply.alarmChain true false false`, the base chain), when
the checked permissions are the request's own (`reqPerms`) and the latest state is the model's
(`outcomeOn_of_authOutL`). What lifts it to an applied entry (the dispatch's KV cases in the mode
`on` through the auth applier's latest-state triples, the principal tie, the transaction's checked
permissions) is left (`notes/decisions.md`, "E2v of the auth plan").
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVApplyOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVModel
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVAuthBridge
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.AuthApplyLatest
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.DispatchKVL

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

section pure
variable [ext : FfiSyntax]

/-- A KV kind is dispatched through the chain (`dispatchLog`'s chain case). -/
theorem dispatchLog_kv (c : apply.Chain) (rq : apply.IRRModel) (lt : LeaseTable) (log : mvcc.Log)
    (hk : apply.isKVKind (apply.dispatchKind rq) = true) :
    dispatchLog c rq true lt log = chainLog c rq lt log := by
  unfold dispatchLog
  cases h : apply.dispatchKind rq <;> simp_all [apply.isKVKind, apply.preV3Kind, apply.storeKind]

/-- **The auth applier's outcome at the latest state is the mode-`on` model's** (see the file
header): for a plain KV request of the entry `m` above `c₀`, applied at the start chain with auth
on and no alarm, whose checked permissions are the request's own, at the history `hs` whose latest
state is the model's `s.1`: the log the outcome leaves is a successor of `outcomeOn`. -/
theorem outcomeOn_of_authOutL (c₀ : w64) (s : auth.AuthState × mvcc.Log) (m : EntryModel)
    (rq : apply.IRRModel) (ht : m.typ = W32 0) (hd : m.data ≠ [])
    (hdec : apply.irrDecode m.data = some rq) (hv : uint.Z c₀ < uint.Z m.index)
    (hna : apply.needAdminPermission rq = false)
    (hk : apply.isKVKind (apply.dispatchKind rq) = true) (hp : plainCover rq)
    (γa : auth.AuthNames) (hs : List auth.AuthState) (hl : hs.getLast? = some s.1)
    (oc : apply.Outcome)
    (h : apply.authOutL (.on γa) hs (auth.authInfoM (apply.principalOf rq)) (.quota .backend) rq
      s.2 (reqPerms rq) oc) :
    outcomeOn c₀ (apply.alarmChain true false false) s m (s.1, oc.logAfter s.2) := by
  have hm : m.typ = W32 0 ∧ m.data ≠ [] := ⟨ht, hd⟩
  have hna' : ¬ (uint.Z c₀ < uint.Z m.index ∧ apply.needAdminPermission rq = true) := by
    rintro ⟨-, h⟩; rw [hna] at h; cases h
  unfold outcomeOn
  rw [if_pos hm, hdec]
  simp only
  rw [if_neg hna']
  rcases h with ⟨rfl, hr⟩ | ⟨hc, hpass⟩
  · -- refused at the latest state: the log kept
    have hng := not_kvGranted_of_refusedL γa hs s.1 hl rq (reqPerms rq) (fun _ hx => hx) hr
    rw [if_pos ⟨hk, hng⟩]
    rfl
  · -- granted at the latest state: the inner chain's write, the model's
    have hg := kvGranted_of_passedL γa hs s.1 hl rq hpass
    have hng : ¬ (apply.isKVKind (apply.dispatchKind rq) = true ∧ ¬ kvGranted s.1 rq) := by
      rintro ⟨-, hn⟩; exact hn hg
    rw [if_neg hng]
    have hlog : oc.logAfter s.2 = chainLog (.quota .backend) rq [] s.2 := by
      rcases chainStep_plain [] (.quota .backend) rq s.2 oc hp hc with h | ⟨-, hx⟩
      · exact h
      · exact absurd hx (by decide)
    have hkv : kvEntry c₀ (apply.alarmChain true false false) [] s.2 m =
        chainLog (.quota .backend) rq [] s.2 := by
      unfold kvEntry
      rw [if_pos ht, if_neg hd, hdec]
      simp only [decide_eq_true hv]
      rw [dispatchLog_kv _ rq [] s.2 hk]
      rfl
    rw [hlog, hkv]

/-! ## The dispatched outcome's verdict on the request's own permissions (E2y) -/

/-- **No range end of the request is `"\x00"`** (a premise of the workload): the one end at which a
check can see another range than the model's (`authEndOf`: a non-`nil` empty `RangeEnd` on the
wire, which the model reads as `"\x00"`). -/
def noZeroEnds (rq : apply.IRRModel) : Prop := ∀ x ∈ reqPerms rq, x.2.1 ≠ [W8 0]

theorem authEndOf_eq (m e : GoString) (h : apply.authEndOf m e) (hm : m ≠ [W8 0]) : e = m := by
  rcases h with h | ⟨-, h⟩
  · exact h
  · exact absurd h hm

/-- **A transaction's verdict is on its own permissions** (`kvOutL`'s transaction case, E2s's
`txnMay`/`txnChecked`, against the model's `reqPerms`): a refusal is of a permission the model
asks, a pass covers every one it asks. A premise for transactions: the checks see a put's
`PrevKv` read (`checkPutAuth`), which the model's operation (`TxnOp.put`, no `PrevKv`) does not
record (`notes/decisions.md`, "E2y of the auth plan"). -/
def txnVerdictOwn (M : auth.AuthMode) (hs : List auth.AuthState) (rq : apply.IRRModel) : Prop :=
  ∀ t, rq.txn = some t →
    (apply.refusedMay M hs (auth.authInfoM (apply.principalOf rq)) (apply.txnMay t) →
      apply.refusedL M hs (auth.authInfoM (apply.principalOf rq)) (reqPerms rq)) ∧
    (∀ L, apply.txnChecked t L → apply.passedL M hs (auth.authInfoM (apply.principalOf rq)) L →
      apply.passedL M hs (auth.authInfoM (apply.principalOf rq)) (reqPerms rq))

/-- **The dispatched outcome decided at the latest state, on the request's own permissions**:
`kvOutL` (the dispatch's KV triple at the latest state, at the request's principal) is E2s's
`authOutL` at the model's `reqPerms`, for a request without `"\x00"` range ends and, for a
transaction, `txnVerdictOwn`. -/
theorem authOutL_of_kvOutL (M : auth.AuthMode) (hs : List auth.AuthState) (ci : apply.Chain)
    (rq : apply.IRRModel) (log : mvcc.Log) (oc : apply.Outcome) (hz : noZeroEnds rq)
    (ht : txnVerdictOwn M hs rq)
    (h : apply.kvOutL M hs (auth.authInfoM (apply.principalOf rq)) ci rq log oc) :
    apply.authOutL M hs (auth.authInfoM (apply.principalOf rq)) ci rq log (reqPerms rq) oc := by
  unfold apply.kvOutL at h
  split at h
  · rename_i hk
    obtain ⟨o, ho, e, he, h⟩ := h
    have hm : o.base.rangeEnd ≠ [W8 0] := by
      have := hz (o.key, o.base.rangeEnd, .read) (by simp [reqPerms, hk, ho])
      exact this
    rw [authEndOf_eq _ _ he hm] at h
    simpa [reqPerms, hk, ho] using h
  · rename_i hk
    obtain ⟨o, ho, h⟩ := h
    simpa [reqPerms, hk, ho] using h
  · rename_i hk
    obtain ⟨o, ho, e, he, h⟩ := h
    have hm : o.base.rangeEnd ≠ [W8 0] := by
      have := hz (o.key, o.base.rangeEnd, .write) (by simp [reqPerms, hk, ho])
      exact this
    rw [authEndOf_eq _ _ he hm] at h
    simpa [reqPerms, hk, ho] using h
  · rename_i hk
    obtain ⟨t, htx, h⟩ := h
    obtain ⟨hr, hp⟩ := ht t htx
    rcases h with ⟨rfl, h⟩ | ⟨hc, L, hL, h⟩
    · exact Or.inl ⟨rfl, hr h⟩
    · exact Or.inr ⟨hc, hp L hL h⟩
  · exact h.elim

/-- **The apply thread's KV outcome is the mode-`on` model's** (the auth plan's E2y): the
dispatched outcome decided at the latest state (`kvOutL`, `apply.uberApplier.Apply.wp_kvL`), for a
plain KV request of the entry `m` above `c₀` at the start chain with auth on and no alarm, without
`"\x00"` range ends and with `txnVerdictOwn`, at the history `hs` whose latest state is the
model's `s.1`, is `outcomeOn`'s (E2t's `kv_applied_out_on` hypothesis). -/
theorem outcomeOn_of_kvOutL (c₀ : w64) (s : auth.AuthState × mvcc.Log) (m : EntryModel)
    (rq : apply.IRRModel) (ht : m.typ = W32 0) (hd : m.data ≠ [])
    (hdec : apply.irrDecode m.data = some rq) (hv : uint.Z c₀ < uint.Z m.index)
    (hna : apply.needAdminPermission rq = false)
    (hk : apply.isKVKind (apply.dispatchKind rq) = true) (hp : plainCover rq)
    (γa : auth.AuthNames) (hs : List auth.AuthState) (hl : hs.getLast? = some s.1)
    (hz : noZeroEnds rq) (htx : txnVerdictOwn (.on γa) hs rq)
    (oc : apply.Outcome)
    (h : apply.kvOutL (.on γa) hs (auth.authInfoM (apply.principalOf rq)) (.quota .backend) rq s.2 oc) :
    outcomeOn c₀ (apply.alarmChain true false false) s m (s.1, oc.logAfter s.2) :=
  outcomeOn_of_authOutL c₀ s m rq ht hd hdec hv hna hk hp γa hs hl oc
    (authOutL_of_kvOutL _ hs _ rq s.2 oc hz htx h)

end pure

end EtcdGrove
end Perennial
