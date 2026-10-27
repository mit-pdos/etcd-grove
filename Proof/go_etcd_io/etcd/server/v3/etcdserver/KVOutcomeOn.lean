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
variable [GooseExts]

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
asks, a pass covers every one it asks. Of the wire transaction (`txnW`, E3e): a put's `PrevKv`
read is in both. A theorem since E3e (`txnVerdictOwn_of`); a premise until then. -/
def txnVerdictOwn (M : auth.AuthMode) (hs : List auth.AuthState) (rq : apply.IRRModel) : Prop :=
  apply.dispatchKind rq = .txn → ∀ t, rq.txnW = some t →
    (apply.refusedMay M hs (auth.authInfoM (apply.principalOf rq)) (apply.txnMay t) →
      apply.refusedL M hs (auth.authInfoM (apply.principalOf rq)) (reqPerms rq)) ∧
    (∀ L, apply.txnChecked t L → apply.passedL M hs (auth.authInfoM (apply.principalOf rq)) L →
      apply.passedL M hs (auth.authInfoM (apply.principalOf rq)) (reqPerms rq))

/-- No permission's range end is `"\x00"`. -/
def endsOk (L : List apply.Perm3) : Prop := ∀ x ∈ L, x.2.1 ≠ [W8 0]

theorem endsOk_append (L L' : List apply.Perm3) (h : endsOk (L ++ L')) :
    endsOk L ∧ endsOk L' :=
  ⟨fun x hx => h x (List.mem_append_left _ hx), fun x hx => h x (List.mem_append_right _ hx)⟩

/-- The comparisons' reads as the model has them. -/
abbrev cmpPerms (cs : List CmpModel) : List apply.Perm3 :=
  cs.map (fun cm => (cm.key, cm.rangeEnd, .read))

theorem cmps_may_mem (cs : List CmpModel) (x : apply.Perm3) (hz : endsOk (cmpPerms cs))
    (h : apply.cmpsMay cs x) : x ∈ cmpPerms cs := by
  obtain ⟨cm, hcm, e, he, rfl⟩ := h
  have hm : (cm.key, cm.rangeEnd, auth.PermType.read) ∈ cmpPerms cs :=
    List.mem_map_of_mem (f := fun cm : CmpModel => (cm.key, cm.rangeEnd, auth.PermType.read)) hcm
  rw [authEndOf_eq _ _ he (hz _ hm)]
  exact hm

theorem cmps_checked_sub : ∀ (cs : List CmpModel) (L : List apply.Perm3),
    endsOk (cmpPerms cs) → apply.cmpsChecked cs L → ∀ y ∈ cmpPerms cs, y ∈ L
  | [], _, _, _, y, hy => by simp at hy
  | cm :: cs, L, hz, h, y, hy => by
    obtain ⟨e, L', he, hL', rfl⟩ := h
    have hz' := endsOk_append [(cm.key, cm.rangeEnd, auth.PermType.read)] (cmpPerms cs) hz
    simp only [cmpPerms, List.map_cons, List.mem_cons] at hy
    rcases hy with rfl | hy
    · have := authEndOf_eq _ _ he (hz'.1 _ List.mem_cons_self)
      rw [this]; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (cmps_checked_sub cs L' hz'.2 hL' y hy)

mutual
theorem op_may_mem : ∀ (op : txn.TxnOpW) (x : apply.Perm3), endsOk (opPerms op) →
    apply.opMay op x → x ∈ opPerms op
  | .get o, x, hz, h => by
    obtain ⟨e, he, rfl⟩ := h
    have hm : (o.key, o.base.rangeEnd, auth.PermType.read) ∈ opPerms (.get o) := by
      simp [opPerms]
    rw [authEndOf_eq _ _ he (hz _ hm)]
    exact hm
  | .put o, x, _, h => h
  | .delete o, x, hz, h => by
    obtain ⟨e, he, h⟩ := h
    have hm : (o.key, o.base.rangeEnd, auth.PermType.write) ∈ opPerms (.delete o) := by
      simp [opPerms]
    rw [authEndOf_eq _ _ he (hz _ hm)] at h
    rcases h with rfl | ⟨hp, rfl⟩
    · exact hm
    · simp [opPerms, hp]
  | .txn cs ts es, x, hz, h => by
    have hz' := endsOk_append _ _ hz
    have hz'' := endsOk_append _ _ hz'.1
    show x ∈ cmpPerms cs ++ opsPerms ts ++ opsPerms es
    rcases h with h | h | h
    · exact List.mem_append_left _ (List.mem_append_left _ (cmps_may_mem cs x hz''.1 h))
    · exact List.mem_append_left _ (List.mem_append_right _ (ops_may_mem ts x hz''.2 h))
    · exact List.mem_append_right _ (ops_may_mem es x hz'.2 h)

theorem ops_may_mem : ∀ (ops : List txn.TxnOpW) (x : apply.Perm3), endsOk (opsPerms ops) →
    apply.opsMay ops x → x ∈ opsPerms ops
  | [], _, _, h => h.elim
  | op :: ops, x, hz, h => by
    have hz' := endsOk_append _ _ hz
    show x ∈ opPerms op ++ opsPerms ops
    rcases h with h | h
    · exact List.mem_append_left _ (op_may_mem op x hz'.1 h)
    · exact List.mem_append_right _ (ops_may_mem ops x hz'.2 h)
end

mutual
theorem op_checked_sub : ∀ (op : txn.TxnOpW) (L : List apply.Perm3), endsOk (opPerms op) →
    apply.opChecked op L → ∀ y ∈ opPerms op, y ∈ L
  | .get o, L, hz, h, y, hy => by
    obtain ⟨e, he, rfl⟩ := h
    have hm : (o.key, o.base.rangeEnd, auth.PermType.read) ∈ opPerms (.get o) := by
      simp [opPerms]
    rw [authEndOf_eq _ _ he (hz _ hm)]
    simpa [opPerms] using hy
  | .put o, L, _, h, y, hy => by
    have h' : L = apply.putPerms o := h
    rw [h']; exact hy
  | .delete o, L, hz, h, y, hy => by
    obtain ⟨e, he, rfl⟩ := h
    have hm : (o.key, o.base.rangeEnd, auth.PermType.write) ∈ opPerms (.delete o) := by
      simp [opPerms]
    rw [authEndOf_eq _ _ he (hz _ hm)]
    simp only [opPerms] at hy
    cases hp : o.base.prevKV <;> simp only [hp, Bool.false_eq_true, ↓reduceIte] at hy ⊢
    · simp_all
    · simp only [List.mem_cons, List.mem_append, List.not_mem_nil, _root_.or_false] at hy ⊢
      exact hy.symm
  | .txn cs ts es, L, hz, h, y, hy => by
    obtain ⟨L1, L2, L3, h1, h2, h3, rfl⟩ := h
    have hz' := endsOk_append _ _ hz
    have hz'' := endsOk_append _ _ hz'.1
    have hy' : y ∈ cmpPerms cs ++ opsPerms ts ++ opsPerms es := hy
    simp only [List.mem_append] at hy' ⊢
    rcases hy' with (hy | hy) | hy
    · exact Or.inl (cmps_checked_sub cs L1 hz''.1 h1 y hy)
    · exact Or.inr (Or.inl (ops_checked_sub ts L2 hz''.2 h2 y hy))
    · exact Or.inr (Or.inr (ops_checked_sub es L3 hz'.2 h3 y hy))

theorem ops_checked_sub : ∀ (ops : List txn.TxnOpW) (L : List apply.Perm3), endsOk (opsPerms ops) →
    apply.opsChecked ops L → ∀ y ∈ opsPerms ops, y ∈ L
  | [], _, _, _, y, hy => by simp [opsPerms] at hy
  | op :: ops, L, hz, h, y, hy => by
    obtain ⟨L1, L2, h1, h2, rfl⟩ := h
    have hz' := endsOk_append _ _ hz
    have hy' : y ∈ opPerms op ++ opsPerms ops := hy
    rcases List.mem_append.1 hy' with hy | hy
    · exact List.mem_append_left _ (op_checked_sub op L1 hz'.1 h1 y hy)
    · exact List.mem_append_right _ (ops_checked_sub ops L2 hz'.2 h2 y hy)
end

/-- **A transaction's verdict is on its own permissions** (E3e): for a request without `"\x00"`
range ends, the checks' permissions are the model's (`reqPerms` of the wire transaction). -/
theorem txnVerdictOwn_of (M : auth.AuthMode) (hs : List auth.AuthState) (rq : apply.IRRModel)
    (hz : noZeroEnds rq) : txnVerdictOwn M hs rq := by
  intro hk t ht
  have hp : reqPerms rq = cmpPerms t.cmps ++ opsPerms t.thenOps ++ opsPerms t.elseOps := by
    simp only [reqPerms, hk, ht]
  have hz0 : endsOk (reqPerms rq) := hz
  rw [hp] at hz0
  have hz1 := endsOk_append _ _ hz0
  have hz2 := endsOk_append _ _ hz1.1
  constructor
  · intro hr
    unfold apply.refusedMay at hr
    unfold apply.refusedL
    refine apply.latestOk_mono _ _ _ _ (fun stl ⟨x, hx, hn⟩ => ⟨x, ?_, hn⟩) hr
    rw [hp]
    simp only [List.mem_append]
    rcases hx with hx | hx | hx
    · exact Or.inl (Or.inl (cmps_may_mem _ x hz2.1 hx))
    · exact Or.inl (Or.inr (ops_may_mem _ x hz2.2 hx))
    · exact Or.inr (ops_may_mem _ x hz1.2 hx)
  · intro L hL hpass
    obtain ⟨L1, L2, L3, h1, h2, h3, rfl⟩ := hL
    unfold apply.passedL at hpass ⊢
    refine apply.latestOk_mono _ _ _ _ (fun stl h y hy => h y ?_) hpass
    rw [hp] at hy
    simp only [List.mem_append] at hy ⊢
    rcases hy with (hy | hy) | hy
    · exact Or.inl (cmps_checked_sub _ L1 hz2.1 h1 y hy)
    · exact Or.inr (Or.inl (ops_checked_sub _ L2 hz2.2 h2 y hy))
    · exact Or.inr (Or.inr (ops_checked_sub _ L3 hz1.2 h3 y hy))

/-- **The dispatched outcome decided at the latest state, on the request's own permissions**:
`kvOutL` (the dispatch's KV triple at the latest state, at the request's principal) is E2s's
`authOutL` at the model's `reqPerms`, for a request without `"\x00"` range ends (a transaction's
through `txnVerdictOwn_of`, E3e). -/
theorem authOutL_of_kvOutL (M : auth.AuthMode) (hs : List auth.AuthState) (ci : apply.Chain)
    (rq : apply.IRRModel) (log : mvcc.Log) (oc : apply.Outcome) (hz : noZeroEnds rq)
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
    obtain ⟨hr, hp⟩ := txnVerdictOwn_of M hs rq hz hk t htx
    rcases h with ⟨rfl, h⟩ | ⟨hc, L, hL, h⟩
    · exact Or.inl ⟨rfl, hr h⟩
    · exact Or.inr ⟨hc, hp L hL h⟩
  · exact h.elim

/-- **The apply thread's KV outcome is the mode-`on` model's** (the auth plan's E2y): the
dispatched outcome decided at the latest state (`kvOutL`, `apply.uberApplier.Apply.wp_kvL`), for a
plain KV request of the entry `m` above `c₀` at the start chain with auth on and no alarm, without
`"\x00"` range ends, at the history `hs` whose latest state is the
model's `s.1`, is `outcomeOn`'s (E2t's `kv_applied_out_on` hypothesis). -/
theorem outcomeOn_of_kvOutL (c₀ : w64) (s : auth.AuthState × mvcc.Log) (m : EntryModel)
    (rq : apply.IRRModel) (ht : m.typ = W32 0) (hd : m.data ≠ [])
    (hdec : apply.irrDecode m.data = some rq) (hv : uint.Z c₀ < uint.Z m.index)
    (hna : apply.needAdminPermission rq = false)
    (hk : apply.isKVKind (apply.dispatchKind rq) = true) (hp : plainCover rq)
    (γa : auth.AuthNames) (hs : List auth.AuthState) (hl : hs.getLast? = some s.1)
    (hz : noZeroEnds rq)
    (oc : apply.Outcome)
    (h : apply.kvOutL (.on γa) hs (auth.authInfoM (apply.principalOf rq)) (.quota .backend) rq s.2 oc) :
    outcomeOn c₀ (apply.alarmChain true false false) s m (s.1, oc.logAfter s.2) :=
  outcomeOn_of_authOutL c₀ s m rq ht hd hdec hv hna hk hp γa hs hl oc
    (authOutL_of_kvOutL _ hs _ rq s.2 oc hz h)

end pure

end EtcdGrove
end Perennial
