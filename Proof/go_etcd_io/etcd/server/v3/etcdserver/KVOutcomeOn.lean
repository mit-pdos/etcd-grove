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
theorem outcomeOn_of_authOutL (c₀ : w64) (s : OnState) (m : EntryModel)
    (rq : apply.IRRModel) (ht : m.typ = W32 0) (hd : m.data ≠ [])
    (hdec : apply.irrDecode m.data = some rq) (hv : uint.Z c₀ < uint.Z m.index)
    (hna : apply.needAdminPermission rq = false)
    (hk : apply.isKVKind (apply.dispatchKind rq) = true) (hp : plainCover rq)
    (γa : auth.AuthNames) (hs : List auth.AuthState) (hl : hs.getLast? = some s.1)
    (oc : apply.Outcome)
    (h : apply.authOutL (.on γa) hs (auth.authInfoM (apply.principalOf rq)) (.quota .backend) rq
      s.2.1 (reqPerms rq) oc) :
    outcomeOn c₀ (apply.alarmChain true false false) s m (s.1, oc.logAfter s.2.1, s.2.2) := by
  have hm : m.typ = W32 0 ∧ m.data ≠ [] := ⟨ht, hd⟩
  have hak : apply.authKVKind (apply.dispatchKind rq) = true := apply.authKVKind_of_isKVKind _ hk
  rw [outcomeOn_nonadmin c₀ _ s m _ rq hm hdec hna]
  rcases h with ⟨rfl, hr⟩ | ⟨hc, hpass⟩
  · -- refused at the latest state: the state kept
    have hng := not_kvGranted_of_refusedL γa hs s.1 hl rq (reqPerms rq) (fun _ hx => hx) hr
    rw [if_pos ⟨hak, fun h => hng h.1⟩]
    rfl
  · -- granted at the latest state: the inner chain's write, the model's
    have hg := kvGranted_of_passedL γa hs s.1 hl rq hpass
    have hng : ¬ (apply.authKVKind (apply.dispatchKind rq) = true ∧
        ¬ kvGrantedL s.1 (mvcc.leaseItemsOf (mvcc.stateAfter s.2.1)) rq) := by
      rintro ⟨-, hn⟩; exact hn ⟨hg, leaseGrantedM_of_plainCover _ _ _ hp⟩
    rw [if_neg hng]
    have hlog : oc.logAfter s.2.1 = chainLog (.quota .backend) rq s.2.2 s.2.1 := by
      rcases chainStep_plain s.2.2 (.quota .backend) rq s.2.1 oc hp hc with h | ⟨-, hx⟩
      · exact h
      · exact absurd hx (by decide)
    have hkv : kvEntry c₀ (apply.alarmChain true false false) s.2.2 s.2.1 m =
        chainLog (.quota .backend) rq s.2.2 s.2.1 := by
      unfold kvEntry
      rw [if_pos ht, if_neg hd, hdec]
      simp only [decide_eq_true hv]
      rw [dispatchLog_kv _ rq s.2.2 s.2.1 hk]
      rfl
    have htb : kvTable c₀ (apply.alarmChain true false false) s.2.2 m = s.2.2 := by
      unfold kvTable
      rw [if_pos ht, if_neg hd, hdec]
      simp only
      unfold dispatchTable
      split
      · rfl
      · exact chainTable_plain rq s.2.2 hp _
    rw [hlog, hkv, htb]

/-! ## The dispatched outcome's verdict on the request's own permissions (E2y) -/

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

/-- (auth-lease S2) A lease attaching no key is refused only vacuously: its refusal gives any
refusal. -/
theorem refusedL_of_leaseRefusedL_none (M : auth.AuthMode) (hs : List auth.AuthState)
    (ai : auth.AuthInfoM) (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64) (id : w64)
    (perms : List apply.Perm3) (hn : ∀ k : GoString, I.lookup ⟨k⟩ ≠ some id)
    (h : apply.leaseRefusedL M hs ai I id) : apply.refusedL M hs ai perms := by
  cases M with
  | on γa =>
    intro stl hl
    obtain ⟨-, k, hk, -⟩ := h stl hl
    exact absurd hk (hn k)
  | off => trivial
  | any => trivial

/-- The same for a transaction's checkable permissions. -/
theorem refusedMay_of_leaseRefusedL_none (M : auth.AuthMode) (hs : List auth.AuthState)
    (ai : auth.AuthInfoM) (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64) (id : w64)
    (May : apply.Perm3 → Prop) (hn : ∀ k : GoString, I.lookup ⟨k⟩ ≠ some id)
    (h : apply.leaseRefusedL M hs ai I id) : apply.refusedMay M hs ai May := by
  cases M with
  | on γa =>
    intro stl hl
    obtain ⟨-, k, hk, -⟩ := h stl hl
    exact absurd hk (hn k)
  | off => trivial
  | any => trivial

/-- **The dispatched outcome decided at the latest state, on the request's own permissions**:
`kvOutL` (the dispatch's KV triple at the latest state, at the request's principal) is E2s's
`authOutL` at the model's `reqPerms`, for a request without `"\x00"` range ends (a transaction's
through `txnVerdictOwn_of`, E3e) and (auth-lease S2) of the mode-`on` log's plain shape
(`plainCover`: no lease, so `kvOutL`'s lease parts are vacuous). -/
theorem authOutL_of_kvOutL (M : auth.AuthMode) (hs : List auth.AuthState) (ci : apply.Chain)
    (rq : apply.IRRModel) (log : mvcc.Log) (oc : apply.Outcome) (hz : noZeroEnds rq)
    (hp : plainCover rq)
    (h : apply.kvOutL M hs (auth.authInfoM (apply.principalOf rq)) ci rq log oc) :
    apply.authOutL M hs (auth.authInfoM (apply.principalOf rq)) ci rq log (reqPerms rq) oc := by
  have hz0 := leaseItemsOf_zero_none log
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
    have hl0 : o.leaseID = W64 0 := by
      unfold plainCover at hp; rw [hk] at hp; exact hp.2.2 o ho
    have hpr : reqPerms rq = apply.putPerms o := by simp [reqPerms, hk, ho]
    rw [hpr]
    rcases h with ⟨rfl, h | ⟨id, hid, h⟩⟩ | ⟨hc, h1, -⟩
    · exact Or.inl ⟨rfl, h⟩
    · rw [List.mem_singleton.1 hid, hl0] at h
      exact Or.inl ⟨rfl, refusedL_of_leaseRefusedL_none _ _ _ _ _ _ hz0 h⟩
    · exact Or.inr ⟨hc, h1⟩
  · rename_i hk
    obtain ⟨o, ho, e, he, h⟩ := h
    have hm : o.base.rangeEnd ≠ [W8 0] := by
      have := hz (o.key, o.base.rangeEnd, .write) (by simp [reqPerms, hk, ho])
      exact this
    rw [authEndOf_eq _ _ he hm] at h
    simpa [reqPerms, hk, ho] using h
  · rename_i hk
    obtain ⟨t, htx, h⟩ := h
    obtain ⟨hr, hpa⟩ := txnVerdictOwn_of M hs rq hz hk t htx
    have hpl : txn.txnPlain t.toModel := by
      unfold plainCover at hp; rw [hk] at hp
      exact hp.2.2 t.toModel (by rw [← apply.IRRModel.txnW_map, htx]; rfl)
    have hl0 := txnPutsW_plain t hpl
    unfold apply.txnOutLL at h
    rcases h with ⟨rfl, h | ⟨o, ho, h⟩⟩ | ⟨hc, ⟨L, hL, h⟩, -⟩
    · exact Or.inl ⟨rfl, hr h⟩
    · rw [hl0 o ho] at h
      exact Or.inl ⟨rfl, hr (refusedMay_of_leaseRefusedL_none _ _ _ _ _ _ hz0 h)⟩
    · exact Or.inr ⟨hc, hpa L hL h⟩
  · rename_i hk
    unfold plainCover at hp; rw [hk] at hp; exact hp.elim
  · exact h.elim

/-- **The apply thread's KV outcome is the mode-`on` model's** (the auth plan's E2y): the
dispatched outcome decided at the latest state (`kvOutL`, `apply.uberApplier.Apply.wp_kvL`), for a
plain KV request of the entry `m` above `c₀` at the start chain with auth on and no alarm, without
`"\x00"` range ends, at the history `hs` whose latest state is the
model's `s.1`, is `outcomeOn`'s (E2t's `kv_applied_out_on` hypothesis). -/
theorem outcomeOn_of_kvOutL (c₀ : w64) (s : OnState) (m : EntryModel)
    (rq : apply.IRRModel) (ht : m.typ = W32 0) (hd : m.data ≠ [])
    (hdec : apply.irrDecode m.data = some rq) (hv : uint.Z c₀ < uint.Z m.index)
    (hna : apply.needAdminPermission rq = false)
    (hk : apply.isKVKind (apply.dispatchKind rq) = true) (hp : plainCover rq)
    (γa : auth.AuthNames) (hs : List auth.AuthState) (hl : hs.getLast? = some s.1)
    (hz : noZeroEnds rq)
    (oc : apply.Outcome)
    (h : apply.kvOutL (.on γa) hs (auth.authInfoM (apply.principalOf rq)) (.quota .backend) rq s.2.1 oc) :
    outcomeOn c₀ (apply.alarmChain true false false) s m (s.1, oc.logAfter s.2.1, s.2.2) :=
  outcomeOn_of_authOutL c₀ s m rq ht hd hdec hv hna hk hp γa hs hl oc
    (authOutL_of_kvOutL _ hs _ rq s.2.1 oc hz hp h)

/-! ## The lease verdict and the lease-exact outcome (auth-lease S3a §6, Draft rev 5 §3, §3a) -/

/-- **The lease check passed at the latest state is the model's `leaseOk` there** (`KVAuthBridge`'s
`leaseOk_iff`, its pass half): no shape needed, `granted1` at `(k, [], .write)` is `leaseOk`'s clause. -/
theorem leaseOk_of_leasePassedL (γa : auth.AuthNames) (hs : List auth.AuthState) (stl : auth.AuthState)
    (hl : hs.getLast? = some stl) (a : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64) (id : w64)
    (h : apply.leasePassedL (.on γa) hs (auth.authInfoM a) I id) : leaseOk stl a I id := by
  rcases h stl hl with h | h
  · exact Or.inr (Or.inl h)
  · by_cases hen : stl.enabled = false
    · exact Or.inl hen
    · refine Or.inr (Or.inr fun k hk => ?_)
      rcases h k hk with h' | h'
      · exact absurd h' hen
      · exact h'

/-- **The lease check refused at the latest state is the model's `¬ leaseOk` there** (the refusal half). -/
theorem not_leaseOk_of_leaseRefusedL (γa : auth.AuthNames) (hs : List auth.AuthState)
    (stl : auth.AuthState) (hl : hs.getLast? = some stl) (a : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64) (id : w64)
    (h : apply.leaseRefusedL (.on γa) hs (auth.authInfoM a) I id) : ¬ leaseOk stl a I id := by
  obtain ⟨hna, k, hk, hng⟩ := h stl hl
  rintro (hen | had | hall)
  · exact hng (Or.inl hen)
  · exact hna had
  · exact hng (Or.inr (hall k hk))

/-- **`kvOutL` is the model's verdict `kvGrantedL` at the latest state** (Draft §3: for every
admitted kind, the lease part included, at the log's lease items): a refusal is the auth layer's
rejection of a request `kvGrantedL` refuses, a pass the inner chain's outcome of one it grants. -/
theorem kvGrantedL_of_kvOutL (γa : auth.AuthNames) (hs : List auth.AuthState) (stl : auth.AuthState)
    (hl : hs.getLast? = some stl) (ci : apply.Chain) (rq : apply.IRRModel) (log : mvcc.Log)
    (oc : apply.Outcome) (hz : noZeroEnds rq)
    (h : apply.kvOutL (.on γa) hs (auth.authInfoM (apply.principalOf rq)) ci rq log oc) :
    (oc = .rejected .auth ∧ ¬ kvGrantedL stl (mvcc.leaseItemsOf (mvcc.stateAfter log)) rq) ∨
      (apply.chainStep apply.backendStep ci rq log oc ∧
        kvGrantedL stl (mvcc.leaseItemsOf (mvcc.stateAfter log)) rq) := by
  unfold apply.kvOutL at h
  split at h
  · rename_i hk
    obtain ⟨o, ho, e, he, h⟩ := h
    have hm : o.base.rangeEnd ≠ [W8 0] := hz (o.key, o.base.rangeEnd, .read) (by simp [reqPerms, hk, ho])
    rw [authEndOf_eq _ _ he hm] at h
    have hp : reqPerms rq = [(o.key, o.base.rangeEnd, .read)] := by simp [reqPerms, hk, ho]
    have hlg : leaseGrantedM stl (mvcc.leaseItemsOf (mvcc.stateAfter log)) rq := by
      unfold leaseGrantedM; rw [hk]; trivial
    rcases h with ⟨rfl, hr⟩ | ⟨hc, hpa⟩
    · exact Or.inl ⟨rfl, fun hg => not_kvGranted_of_refusedL γa hs stl hl rq _
        (fun x hx => by rw [hp]; exact hx) hr hg.1⟩
    · exact Or.inr ⟨hc, kvGranted_of_passedL γa hs stl hl rq (by rw [hp]; exact hpa), hlg⟩
  · rename_i hk
    obtain ⟨o, ho, h⟩ := h
    have hp : reqPerms rq = apply.putPerms o := by simp [reqPerms, hk, ho]
    rcases h with ⟨rfl, hr | ⟨id, hid, hr⟩⟩ | ⟨hc, hpa, hlp⟩
    · exact Or.inl ⟨rfl, fun hg => not_kvGranted_of_refusedL γa hs stl hl rq _
        (fun x hx => by rw [hp]; exact hx) hr hg.1⟩
    · rw [List.mem_singleton.1 hid] at hr
      refine Or.inl ⟨rfl, fun hg => ?_⟩
      have h2 := hg.2
      unfold leaseGrantedM at h2; rw [hk] at h2
      exact not_leaseOk_of_leaseRefusedL γa hs stl hl _ _ _ hr (h2 o ho)
    · refine Or.inr ⟨hc, kvGranted_of_passedL γa hs stl hl rq (by rw [hp]; exact hpa), ?_⟩
      unfold leaseGrantedM; rw [hk]
      intro o' ho'
      rw [ho] at ho'; cases ho'
      exact leaseOk_of_leasePassedL γa hs stl hl _ _ _ (hlp _ (List.mem_singleton.2 rfl))
  · rename_i hk
    obtain ⟨o, ho, e, he, h⟩ := h
    have hm : o.base.rangeEnd ≠ [W8 0] := hz (o.key, o.base.rangeEnd, .write) (by simp [reqPerms, hk, ho])
    rw [authEndOf_eq _ _ he hm] at h
    have hp : reqPerms rq = (o.key, o.base.rangeEnd, .write) ::
        if o.base.prevKV then [(o.key, o.base.rangeEnd, .read)] else [] := by simp [reqPerms, hk, ho]
    have hlg : leaseGrantedM stl (mvcc.leaseItemsOf (mvcc.stateAfter log)) rq := by
      unfold leaseGrantedM; rw [hk]; trivial
    rcases h with ⟨rfl, hr⟩ | ⟨hc, hpa⟩
    · exact Or.inl ⟨rfl, fun hg => not_kvGranted_of_refusedL γa hs stl hl rq _
        (fun x hx => by rw [hp]; exact hx) hr hg.1⟩
    · exact Or.inr ⟨hc, kvGranted_of_passedL γa hs stl hl rq (by rw [hp]; exact hpa), hlg⟩
  · rename_i hk
    obtain ⟨t, htx, h⟩ := h
    obtain ⟨hr, hpa⟩ := txnVerdictOwn_of (.on γa) hs rq hz hk t htx
    unfold apply.txnOutLL at h
    rcases h with ⟨rfl, h | ⟨o, ho, h⟩⟩ | ⟨hc, ⟨L, hL, h⟩, hlp⟩
    · exact Or.inl ⟨rfl, fun hg => not_kvGranted_of_refusedL γa hs stl hl rq _
        (fun x hx => hx) (hr h) hg.1⟩
    · refine Or.inl ⟨rfl, fun hg => ?_⟩
      have h2 := hg.2
      unfold leaseGrantedM at h2; rw [hk] at h2
      exact not_leaseOk_of_leaseRefusedL γa hs stl hl _ _ _ h (h2 t htx o ho)
    · refine Or.inr ⟨hc, kvGranted_of_passedL γa hs stl hl rq (hpa L hL h), ?_⟩
      unfold leaseGrantedM; rw [hk]
      intro t' ht' o ho
      rw [htx] at ht'; cases ht'
      exact leaseOk_of_leasePassedL γa hs stl hl _ _ _ (hlp o ho)
  · rename_i hk
    obtain ⟨id, hid, h⟩ := h
    have hp : reqPerms rq = [] := by simp [reqPerms, hk]
    rcases h with ⟨rfl, hr | ⟨id', hid', hr⟩⟩ | ⟨hc, -, hlp⟩
    · exfalso
      obtain ⟨x, hx, -⟩ := hr stl hl
      exact List.not_mem_nil hx
    · rw [List.mem_singleton.1 hid'] at hr
      refine Or.inl ⟨rfl, fun hg => ?_⟩
      have h2 := hg.2
      unfold leaseGrantedM at h2; rw [hk] at h2
      exact not_leaseOk_of_leaseRefusedL γa hs stl hl _ _ _ hr (h2 id hid)
    · refine Or.inr ⟨hc, fun x hx => by rw [hp] at hx; exact absurd hx List.not_mem_nil, ?_⟩
      unfold leaseGrantedM; rw [hk]
      intro id' hid'
      rw [hid] at hid'; cases hid'
      exact leaseOk_of_leasePassedL γa hs stl hl _ _ _ (hlp _ (List.mem_singleton.2 rfl))
  · exact h.elim

/-- A KV kind changes no table. -/
theorem backendTable_kv (rq : apply.IRRModel) (lt : LeaseTable)
    (hk : apply.isKVKind (apply.dispatchKind rq) = true) : backendTable rq lt = lt := by
  unfold backendTable
  split <;> simp_all [apply.isKVKind]

theorem chainTable_kv (rq : apply.IRRModel) (lt : LeaseTable)
    (hk : apply.isKVKind (apply.dispatchKind rq) = true) :
    ∀ c : apply.Chain, chainTable c rq lt = lt := by
  intro c
  induction c with
  | backend => exact backendTable_kv rq lt hk
  | corrupt c ih => simp only [chainTable]; split <;> simp [ih]
  | capped c ih => simp only [chainTable]; split <;> simp [ih]
  | auth _ c ih => simp only [chainTable]; exact ih
  | quota c ih => simp only [chainTable]; exact ih

/-- **The backend's outcome of a KV request of the auth-on log is the model's** (`backendLog`), at
the table `lt`: a plain request's always (`plainCover`), a leased put's or transaction's when the
outcome is lease-exact at `lt`'s ids (`apply.leaseExactL`, Draft §3a). -/
theorem backendLog_of_step (lm : lease.Mode) (lt : LeaseTable) (rq : apply.IRRModel) (log : mvcc.Log)
    (oc : apply.Outcome) (hk : apply.isKVKind (apply.dispatchKind rq) = true) (hp : plainReqL lm rq)
    (hex : plainCover rq ∨ apply.leaseExactL lt.ids rq log oc) (hb : apply.backendStep rq log oc) :
    oc.logAfter log = backendLog lt rq log := by
  have hpc : plainReqL lm rq → apply.dispatchKind rq = .txn → ∀ t, rq.txn = some t → txn.txnLeased t := by
    rintro (⟨hc, -⟩ | ⟨-, -, -, hk' | ⟨-, ht⟩⟩) hkt t htt
    · unfold plainCover at hc; rw [hkt] at hc; exact txn.txnLeased_of_plain t (hc.2.2 t htt)
    · rw [hk'] at hkt; cases hkt
    · exact ht t htt
  unfold apply.backendStep at hb
  unfold backendLog
  split at hb
  · rename_i hkd
    obtain ⟨op, hop, hb⟩ := hb
    rw [hkd, hop]
    simp only
    have hex' : (op.leaseID ≠ W64 0 ∧ op.leaseID ∉ lt.ids → oc.logAfter log = log) ∧
        (oc = .rejected .backend → (op.leaseID ≠ W64 0 ∧ op.leaseID ∉ lt.ids) ∨
          (txn.needsPrev op = true ∧ mvcc.findKey op.key (mvcc.stateAfter log) = none)) := by
      rcases hex with hc | he
      · have h0 : op.leaseID = W64 0 := by unfold plainCover at hc; rw [hkd] at hc; exact hc.2.2 op hop
        refine ⟨fun h => absurd h0 h.1, fun hr => ?_⟩
        rcases hb with ⟨h1, -⟩ | ⟨h1, h2, -⟩ | ⟨-, rfl⟩
        · exact absurd h0 h1
        · exact Or.inr ⟨h1, h2⟩
        · cases hr
      · unfold apply.leaseExactL at he; rw [hkd] at he; exact he op hop
    rcases hb with ⟨-, rfl⟩ | ⟨h1, h2, rfl⟩ | ⟨h1, rfl⟩
    · rcases hex'.2 rfl with hm | ⟨h1, h2⟩
      · rw [if_pos (show leaseMissingIn lt op.leaseID from hm)]; rfl
      · by_cases hm : leaseMissingIn lt op.leaseID
        · rw [if_pos hm]; rfl
        · rw [if_neg hm, if_pos (by simp [h1, h2])]; rfl
    · by_cases hm : leaseMissingIn lt op.leaseID
      · rw [if_pos hm]; rfl
      · rw [if_neg hm, if_pos (by simp [h1, h2])]; rfl
    · by_cases hm : leaseMissingIn lt op.leaseID
      · have := hex'.1 hm
        simp [apply.Outcome.logAfter] at this
      · rw [if_neg hm, if_neg]
        · rfl
        · intro hc
          simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hc
          have := h1 hc.1
          rw [hc.2] at this; cases this
  · rename_i hkd
    obtain ⟨op, hop, rfl⟩ := hb
    rw [hkd, hop]; rfl
  · rename_i hkd
    subst hb
    rw [hkd]; rfl
  · rename_i hkd
    obtain ⟨t, htt, hb⟩ := hb
    rw [hkd, htt]
    simp only
    have hl := hpc hp hkd t htt
    have hex' : (oc.logAfter log ≠ log → txn.PathsLeaseOk (mvcc.stateAfter log) lt.ids
          (t.branch (txn.txnOk (mvcc.stateAfter log) t))) ∧
        (oc = .rejected .backend → ¬ (txn.PathsIgnOk (mvcc.stateAfter log)
          (t.branch (txn.txnOk (mvcc.stateAfter log) t)) ∧
          txn.PathsLeaseOk (mvcc.stateAfter log) lt.ids (t.branch (txn.txnOk (mvcc.stateAfter log) t)))) := by
      rcases hex with hc | he
      · have hpl : txn.txnPlain t := by unfold plainCover at hc; rw [hkd] at hc; exact hc.2.2 t htt
        refine ⟨fun _ => ?_, fun hr hc' => ?_⟩
        · unfold TxnModel.branch; split
          · exact txn.pathsLeaseOk_plain _ _ _ hpl.1
          · exact txn.pathsLeaseOk_plain _ _ _ hpl.2
        · rcases hb with ⟨-, hn⟩ | ⟨rfl, -⟩
          · exact hn hpl hc'.1
          · cases hr
      · unfold apply.leaseExactL at he; rw [hkd] at he
        exact ⟨(he t htt).1, (he t htt).2 hl⟩
    rcases hb with ⟨rfl, -⟩ | ⟨rfl, -, hig⟩
    · rw [if_neg (hex'.2 rfl)]; rfl
    · by_cases hch : mvcc.commitLog log
          (txn.srvRunTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t).2.1 = log
      · split <;> (simp only [apply.Outcome.logAfter]; try exact hch)
      · rw [if_pos ⟨hig, hex'.1 (by simpa [apply.Outcome.logAfter] using hch)⟩]; rfl
  · rename_i hkd; rw [hkd] at hk; simp [apply.isKVKind] at hk
  · rename_i hkd; rw [hkd] at hk; simp [apply.isKVKind] at hk
  · rename_i hkd; rw [hkd] at hk; simp [apply.isKVKind] at hk
  · rename_i hkd; exfalso
    simp only [apply.isKVKind] at hk
    rename_i h1 h2 h3 h4 h5 h6 h7
    cases h : apply.dispatchKind rq <;> simp_all

/-- **The apply thread's KV outcome is the mode-`on` model's, at the lease mode `lm`** (Draft §3,
§6: `outcomeOn_of_kvOutL` at `plainReqL lm` with the lease verdict): a KV request of the auth-on log
at the lease mode `lm`, its dispatched outcome decided at the latest state (`kvOutL`), and lease-exact
at the model's table when not plain (`leaseExactL`, Draft §3a). -/
theorem outcomeOn_of_kvOutLL (lm : lease.Mode) (c₀ : w64) (s : OnState) (m : EntryModel)
    (rq : apply.IRRModel) (ht : m.typ = W32 0) (hd : m.data ≠ [])
    (hdec : apply.irrDecode m.data = some rq) (hv : uint.Z c₀ < uint.Z m.index)
    (hna : apply.needAdminPermission rq = false)
    (hk : apply.isKVKind (apply.dispatchKind rq) = true) (hp : plainReqL lm rq)
    (γa : auth.AuthNames) (hs : List auth.AuthState) (hl : hs.getLast? = some s.1)
    (hz : noZeroEnds rq) (oc : apply.Outcome)
    (h : apply.kvOutL (.on γa) hs (auth.authInfoM (apply.principalOf rq)) (.quota .backend) rq s.2.1 oc)
    (hex : plainCover rq ∨ apply.leaseExactL s.2.2.ids rq s.2.1 oc) :
    outcomeOn c₀ (apply.alarmChain true false false) s m (s.1, oc.logAfter s.2.1, s.2.2) := by
  have hm : m.typ = W32 0 ∧ m.data ≠ [] := ⟨ht, hd⟩
  have hak : apply.authKVKind (apply.dispatchKind rq) = true := apply.authKVKind_of_isKVKind _ hk
  rw [outcomeOn_nonadmin c₀ _ s m _ rq hm hdec hna]
  rcases kvGrantedL_of_kvOutL γa hs s.1 hl _ rq s.2.1 oc hz h with ⟨rfl, hng⟩ | ⟨hc, hg⟩
  · rw [if_pos ⟨hak, hng⟩]
    rfl
  · rw [if_neg (fun h => h.2 hg)]
    have hlog : oc.logAfter s.2.1 = backendLog s.2.2 rq s.2.1 :=
      backendLog_of_step lm s.2.2 rq s.2.1 oc hk hp hex hc
    have hkv : kvEntry c₀ (apply.alarmChain true false false) s.2.2 s.2.1 m =
        backendLog s.2.2 rq s.2.1 := by
      unfold kvEntry
      rw [if_pos ht, if_neg hd, hdec]
      simp only [decide_eq_true hv]
      rw [dispatchLog_kv _ rq s.2.2 s.2.1 hk]
      rfl
    have htb : kvTable c₀ (apply.alarmChain true false false) s.2.2 m = s.2.2 := by
      unfold kvTable
      rw [if_pos ht, if_neg hd, hdec]
      simp only
      unfold dispatchTable
      split
      · rfl
      · exact chainTable_kv rq s.2.2 hk _
    rw [hlog, hkv, htb]

/-- **A revocation's backend outcome is the model's** at a table whose ids are not `0` and cover the
leases of the log's keys (`liveSt`, the keys' leases live, Draft §1): `revokeLog` deletes the lease's
keys, none when the lease is not live. -/
theorem revokeLog_eq_backendLog (lt : LeaseTable) (rq : apply.IRRModel) (log : mvcc.Log) (id : w64)
    (hk : apply.dispatchKind rq = .leaseRevoke) (hid : rq.leaseRevoke = some id)
    (hlive : liveSt lt.ids (mvcc.stateAfter log)) (h0 : W64 0 ∉ lt.ids) :
    apply.revokeLog log id = backendLog lt rq log := by
  unfold backendLog
  rw [hk, hid]
  simp only
  by_cases hin : id ∈ lt.ids
  · rw [if_pos hin]
    have hne : id ≠ W64 0 := fun h => h0 (h ▸ hin)
    unfold apply.revokeLog mvcc.leaseDels mvcc.leaseDelKeys revokeChanges
    rw [if_neg hne, List.map_map]
    rfl
  · rw [if_neg hin]
    have hnil : mvcc.leaseDels (mvcc.stateAfter log) id = [] := by
      unfold mvcc.leaseDels mvcc.leaseDelKeys
      split
      · rfl
      · rename_i hne
        rw [List.filter_eq_nil_iff.2]
        · rfl
        intro v hv hc
        have hc' : v.lease = id := by simpa using hc
        rcases hlive v hv with h | h
        · exact hne (hc' ▸ h)
        · exact hin (hc' ▸ h)
    unfold apply.revokeLog
    rw [hnil]
    unfold mvcc.commitLog
    simp

open Classical in
/-- **The apply thread's revocation outcome is the mode-`on` model's** (Draft §6: the revocation
decided at the latest state, `kvOutL`'s revocation case): refused there, the state kept; granted, the
model's write (the lease's keys deleted, none if it is not live) and its table. -/
theorem outcomeOn_of_kvOutL_revoke (c₀ : w64) (s : OnState) (m : EntryModel)
    (rq : apply.IRRModel) (ht : m.typ = W32 0) (hd : m.data ≠ [])
    (hdec : apply.irrDecode m.data = some rq) (hv : uint.Z c₀ < uint.Z m.index)
    (hna : apply.needAdminPermission rq = false) (hk : apply.dispatchKind rq = .leaseRevoke)
    (γa : auth.AuthNames) (hs : List auth.AuthState) (hl : hs.getLast? = some s.1)
    (hz : noZeroEnds rq) (hlive : liveSt s.2.2.ids (mvcc.stateAfter s.2.1)) (h0 : W64 0 ∉ s.2.2.ids)
    (oc : apply.Outcome)
    (h : apply.kvOutL (.on γa) hs (auth.authInfoM (apply.principalOf rq)) (.quota .backend) rq s.2.1 oc) :
    outcomeOn c₀ (apply.alarmChain true false false) s m (s.1, oc.logAfter s.2.1,
      if oc = .rejected .auth then s.2.2 else kvTable c₀ (apply.alarmChain true false false) s.2.2 m) := by
  have hm : m.typ = W32 0 ∧ m.data ≠ [] := ⟨ht, hd⟩
  have hak : apply.authKVKind (apply.dispatchKind rq) = true := by rw [hk]; rfl
  rw [outcomeOn_nonadmin c₀ _ s m _ rq hm hdec hna]
  rcases kvGrantedL_of_kvOutL γa hs s.1 hl _ rq s.2.1 oc hz h with ⟨rfl, hng⟩ | ⟨hc, hg⟩
  · rw [if_pos ⟨hak, hng⟩, if_pos rfl]
    rfl
  · rw [if_neg (fun h => h.2 hg)]
    have hc' : apply.backendStep rq s.2.1 oc := hc
    unfold apply.backendStep at hc'
    rw [hk] at hc'
    obtain ⟨id, hid, rfl⟩ := hc'
    have hkv : kvEntry c₀ (apply.alarmChain true false false) s.2.2 s.2.1 m =
        backendLog s.2.2 rq s.2.1 := by
      unfold kvEntry
      rw [if_pos ht, if_neg hd, hdec]
      simp only [decide_eq_true hv]
      unfold dispatchLog
      rw [hk]
      rfl
    rw [if_neg (fun h => by cases h)]
    simp only [apply.Outcome.logAfter]
    rw [hkv, ← revokeLog_eq_backendLog s.2.2 rq s.2.1 id hk hid hlive h0]

end pure

end EtcdGrove
end Perennial
