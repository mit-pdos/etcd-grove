/-
**The apply thread's entry with auth on: the facts `applyEntryNormal.specOn` needs** (the auth
plan's E3o, 2026-10-27). Lean-first (no Rocq counterpart).

- `entryOkOn`: the entry's premise in the mode `on` (`entryOk`'s, with an admitted admin request,
  `adminKindOk`, beside the requests `rqOk` admits);
- `kvShapedL_of_log`: a KV request of the mode-`on` log (`noZeroEnds`, `kvShapeAll`, which the log
  keeps since E3o) has its checks of the cache's shape at any history (`apply.kvShapedL`, what the
  latest-state triple `apply.Apply.kvSpecL` asks);
- `kvEntryOn_below`: an entry at or below the start's consistent index (replayed, `v3` false)
  leaves the mode-`on` model's state;
- `kvApplied_nextOn`: after the entry, the apply thread's ghost state at the next state and the
  applied log the mode-`on` model's (`kvLogAtM true`, for `applied_predepositM`): `kvApplied_next`'s
  counterpart;
- `srvRest_admin`: an admin entry leaves the rest buckets (`restAfter_other`);
- `srvAuthApplyResB_open`: the apply thread's auth row with auth on, opened: the authority at a
  history whose latest state is the model's, the write token and the admin share, with the facts
  an entry's application uses, and the row back at any later history;
- `srv_uberAuthStepsL_at`: the uber-applier's latest-state admin triples at the opened row's write
  token (`srv_uberAuthStepsL_on`'s, without giving the row back).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ApplyEntryOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AppliedOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ApplyTieOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.UberOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ApplyKVCore

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section pure
variable [GooseExts]

/-- **An entry's premise in the auth mode `on`** (`entryOk`'s): no data, or data decoding to a
request with an id that `rqOk` admits at the apply thread's log or an admitted admin request
(`adminKindOk`), dispatchable on the apply thread's chain. -/
def entryOkOn (x : apply.ApplyKV) (m : EntryModel) : Prop :=
  m.data = [] ∨ ∃ rq, apply.irrDecode m.data = some rq ∧ (∃ id, apply.irrId rq = some id) ∧
    (apply.rqOk x.log rq ∨ apply.adminKindOk rq) ∧ apply.dispatchOk x.chain.authOn rq

theorem latestOk_all (M : auth.AuthMode) (hs : List auth.AuthState) (P : auth.AuthState → Prop)
    (h : ∀ stl, P stl) : apply.latestOk M hs P := by
  cases M with
  | on γa => intro stl _; exact h stl
  | off => trivial
  | any => trivial

/-- **A KV request of the mode-`on` log has its checks of the cache's shape at any history**: its
permissions are (`kvShapeAll`), and with no range end `"\x00"` every permission a transaction's
check may see is one of them (`cmps_may_mem`, `ops_may_mem`). -/
theorem kvShapedL_of_log (M : auth.AuthMode) (hs : List auth.AuthState) (rq : apply.IRRModel)
    (hz : noZeroEnds rq) (ha : kvShapeAll rq) : apply.kvShapedL M hs rq := by
  have hall : ∀ L : List apply.Perm3, (∀ x ∈ L, x ∈ reqPerms rq) →
      apply.shapedL M hs L := by
    intro L hL
    exact latestOk_all M hs _ (fun _ _ x hx => ha x (hL x hx))
  unfold apply.kvShapedL
  split
  · rename_i hk
    intro o ho
    apply hall
    intro x hx
    simp only [reqPerms, hk, ho]
    exact hx
  · rename_i hk
    intro o ho
    apply hall
    intro x hx
    simp only [reqPerms, hk, ho]
    exact hx
  · rename_i hk
    intro o ho
    apply hall
    intro x hx
    simp only [reqPerms, hk, ho]
    exact hx
  · rename_i hk
    intro t ht
    have hp : reqPerms rq = cmpPerms t.cmps ++ opsPerms t.thenOps ++ opsPerms t.elseOps := by
      simp only [reqPerms, hk, ht]
    have hz0 : endsOk (reqPerms rq) := hz
    rw [hp] at hz0
    have hz1 := endsOk_append _ _ hz0
    have hz2 := endsOk_append _ _ hz1.1
    apply latestOk_all M hs _
    intro _ _ x hx
    apply ha x
    rw [hp]
    simp only [List.mem_append]
    rcases hx with hx | hx | hx
    · exact Or.inl (Or.inl (cmps_may_mem _ x hz2.1 hx))
    · exact Or.inl (Or.inr (ops_may_mem _ x hz2.2 hx))
    · exact Or.inr (ops_may_mem _ x hz1.2 hx)
  · trivial

/-- **An entry at or below the start's consistent index leaves the mode-`on` model's state**
(replayed: `dispatch` runs with `v3` false, `dispatchLog`'s first case). -/
theorem kvEntryOn_below (c₀ : w64) (ch : apply.Chain) (s : auth.AuthState × mvcc.Log)
    (m : EntryModel) (hv : ¬ uint.Z c₀ < uint.Z m.index) : kvEntryOn c₀ ch s m = s := by
  have hk : kvEntry c₀ ch [] s.2 m = s.2 := by
    unfold kvEntry
    split
    · split
      · rfl
      · split
        · unfold dispatchLog
          rw [if_pos (Or.inr (by simp [hv]))]
        · rfl
    · rfl
  unfold kvEntryOn
  split
  · split
    · rw [if_neg (fun h => hv h.1)]
      split
      · rfl
      · rw [hk]
    · rfl
  · rw [hk]

/-- An admitted admin request sets neither cluster field (`dispatchKind` tries them first). -/
theorem adminKindOk_noCluster (rq : apply.IRRModel) (h : apply.adminKindOk rq) :
    rq.clusterVersionSet = none ∧ rq.clusterMemberAttrSet = none := by
  unfold apply.adminKindOk apply.dispatchKind at h
  constructor
  · cases hc : rq.clusterVersionSet with
    | none => rfl
    | some _ => simp [hc] at h
  · cases hc : rq.clusterMemberAttrSet with
    | none => rfl
    | some _ =>
      cases hv : rq.clusterVersionSet <;> simp [hc, hv] at h

/-- **An admitted admin request's `apply.Apply`, with either `v3`, keeps the KV log and the chain**
(`applyStep_admin_keep`'s, any `v3`). -/
theorem applyStep_admin_keepV (rq : apply.IRRModel) (v3 : Bool) (x x' : apply.ApplyKV)
    (out : apply.ApplyOut) (hk : apply.adminKindOk rq) (h : apply.applyStep rq v3 x x' out) :
    x'.log = x.log ∧ x'.chain = x.chain := by
  cases v3 with
  | true => exact applyStep_admin_keep rq x x' out hk h
  | false =>
    cases out with
    | skipped => obtain ⟨-, rfl⟩ := h; exact ⟨rfl, rfl⟩
    | rejected => obtain ⟨-, rfl⟩ := h; exact ⟨rfl, rfl⟩
    | dispatched o b =>
      obtain ⟨-, hd, hl, hc⟩ := h
      unfold apply.dispatchStep at hd
      rw [if_pos (Or.inr rfl)] at hd
      subst hd
      refine ⟨hl, ?_⟩
      rcases hc with hc | ⟨h, -⟩
      · exact hc
      · cases h

/-- An admitted admin request writes nothing to the KV. -/
theorem adminKindOk_nonwrite (rq : apply.IRRModel) (h : apply.adminKindOk rq) :
    ¬ writeKind (apply.dispatchKind rq) := by
  unfold apply.adminKindOk at h
  split at h <;> rename_i hk <;> simp_all [writeKind]

/-- **The mode-`on` model's log after an entry is within the revision budget** (`kvEntry_len`'s,
with `entryOkOn`: an admin request writes nothing). -/
theorem kvEntryOn_len (c₀ : w64) (ch : apply.Chain) (st : auth.AuthState) (x : apply.ApplyKV)
    (m : EntryModel) (hok : entryOkOn x m) (hl : x.log.length < 2 ^ 63) :
    (kvEntryOn c₀ ch (st, x.log) m).2.length < 2 ^ 63 := by
  have hk : (kvEntry c₀ ch [] x.log m).length < 2 ^ 63 := by
    rcases hok with hd | ⟨rq, hdec, hid, hrq | hadm, hdk⟩
    · exact kvEntry_len c₀ ch [] x m (Or.inl hd) hl
    · exact kvEntry_len c₀ ch [] x m (Or.inr ⟨rq, hdec, hid, hrq, hdk⟩) hl
    · rw [kvEntry_nonwrite c₀ ch [] x.log m (Or.inr (Or.inr (fun rq' h => by
        rw [hdec] at h; cases h; exact adminKindOk_nonwrite rq hadm)))]
      exact hl
  unfold kvEntryOn
  split
  · split
    · split
      · exact hl
      · split
        · exact hl
        · exact hk
    · exact hl
  · exact hk

/-- The inner chain with auth on (quota over the backend) never answers the auth layer's
rejection. -/
theorem chainStep_quota_not_auth (rq : apply.IRRModel) (log : mvcc.Log) (o : apply.Outcome)
    (h : apply.chainStep apply.backendStep (.quota .backend) rq log o) :
    o ≠ .rejected .auth := by
  rintro rfl
  simp only [apply.chainStep, apply.backendStep] at h
  split at h <;> simp_all

/-- **The auth layer's verdict is the model's** (`authTie`, for the waiter): a KV request's
dispatched outcome decided at the latest state `st` of `hs` (`kvOutL`, `apply.Apply.kvSpecL`'s
post), on its own permissions (`noZeroEnds`): the auth layer's rejection exactly when `st` does
not grant it. -/
theorem authTie_of_kvOutL (γa : auth.AuthNames) (hs : List auth.AuthState) (st : auth.AuthState)
    (hl : hs.getLast? = some st) (rq : apply.IRRModel) (log : mvcc.Log) (out : apply.ApplyOut)
    (hz : noZeroEnds rq)
    (h : ∀ o b, out = .dispatched o b →
      apply.kvOutL (.on γa) hs (auth.authInfoM (apply.principalOf rq)) (.quota .backend) rq log o) :
    authTie st rq out := by
  intro _ o skip hout
  rcases authOutL_of_kvOutL _ hs _ rq log o hz (h o skip hout) with ⟨rfl, hr⟩ | ⟨hc, hpass⟩
  · exact ⟨fun _ => not_kvGranted_of_refusedL γa hs st hl rq _ (fun _ hx => hx) hr, fun _ => rfl⟩
  · have hg := kvGranted_of_passedL γa hs st hl rq hpass
    exact ⟨fun hr => absurd hr (chainStep_quota_not_auth rq log o hc), fun hn => absurd hg hn⟩

/-- A request of no KV kind has its verdict tied vacuously. -/
theorem authTie_nonKV (st : auth.AuthState) (rq : apply.IRRModel) (out : apply.ApplyOut)
    (hk : apply.isKVKind (apply.dispatchKind rq) = false) : authTie st rq out := by
  intro h; rw [hk] at h; cases h

theorem ite_eq_iff_or {α : Sort _} {c : Prop} [Decidable c] {a b k : α} :
    (if c then a else b) = k ↔ (c ∧ a = k) ∨ (¬c ∧ b = k) := by
  by_cases h : c <;> simp [h]

/-- The field `dispatchKind` dispatches on is set. -/
theorem dispatchKind_field (rq : apply.IRRModel) :
    (apply.dispatchKind rq = .authUserAdd → rq.authUserAdd.isSome = true) ∧
    (apply.dispatchKind rq = .authRoleAdd → rq.authRoleAdd.isSome = true) ∧
    (apply.dispatchKind rq = .authUserGrantRole → rq.authUserGrantRole.isSome = true) ∧
    (apply.dispatchKind rq = .authRoleGrantPermission →
      rq.authRoleGrantPermission.isSome = true) ∧
    (apply.dispatchKind rq = .authEnable → rq.authEnable = true) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro hd <;>
    simp only [apply.dispatchKind, ite_eq_iff_or, reduceCtorEq,
      _root_.and_false, _root_.false_or, _root_.or_false] at hd <;>
    repeat (first | assumption | obtain ⟨_, hd⟩ := hd)

/-- **An admitted admin request needs the admin permission.** -/
theorem adminKindOk_needAdmin (rq : apply.IRRModel) (h : apply.adminKindOk rq) :
    apply.needAdminPermission rq = true := by
  have hk : apply.dispatchKind rq = .authUserAdd ∨ apply.dispatchKind rq = .authRoleAdd ∨
      apply.dispatchKind rq = .authUserGrantRole ∨
      apply.dispatchKind rq = .authRoleGrantPermission ∨ apply.dispatchKind rq = .authEnable := by
    unfold apply.adminKindOk at h
    cases hd : apply.dispatchKind rq <;> rw [hd] at h <;> simp at h ⊢
  obtain ⟨h1, h2, h3, h4, h5⟩ := dispatchKind_field rq
  unfold apply.needAdminPermission
  rcases hk with hk | hk | hk | hk | hk
  · simp [h1 hk]
  · simp [h2 hk]
  · simp [h3 hk]
  · simp [h4 hk]
  · simp [h5 hk]

/-- The floor of a request that is no KV write holds trivially. -/
theorem applyFloorOk_nonFloor (rq : apply.IRRModel) (v3 : Bool) (F log : mvcc.Log)
    (out : apply.ApplyOut) (hk : apply.isFloorKind (apply.dispatchKind rq) = false) :
    apply.applyFloorOk rq v3 F log out := by
  cases out with
  | dispatched o b => intro _ h; rw [hk] at h; cases h
  | _ => trivial

/-- An admitted admin request is of no kind the plain log admits (`putgetKind`). -/
theorem adminKindOk_notPutget (rq : apply.IRRModel) (h : apply.adminKindOk rq) :
    ¬ putgetKind (apply.dispatchKind rq) := by
  unfold apply.adminKindOk at h
  split at h <;> rename_i hk <;> simp_all [putgetKind]

/-- **An entry that neither writes nor takes an admin step leaves the mode-`on` model's state**
(a cluster request, `kvEntry_nonwrite`). -/
theorem kvEntryOn_keep (c₀ : w64) (ch : apply.Chain) (s : auth.AuthState × mvcc.Log)
    (m : EntryModel) (rq : apply.IRRModel) (ht : m.typ = W32 0) (hd : m.data ≠ [])
    (hdec : apply.irrDecode m.data = some rq) (hna : apply.needAdminPermission rq = false)
    (hw : ¬ writeKind (apply.dispatchKind rq)) : kvEntryOn c₀ ch s m = s := by
  have hk : kvEntry c₀ ch [] s.2 m = s.2 :=
    kvEntry_nonwrite c₀ ch [] s.2 m
      (Or.inr (Or.inr (fun rq' h => by rw [hdec] at h; cases h; exact hw)))
  unfold kvEntryOn
  rw [if_pos ⟨ht, hd⟩, hdec]
  simp only [hna, Bool.false_eq_true, _root_.and_false, ↓reduceIte]
  split
  · rfl
  · rw [hk]

/-- An admitted admin request is no KV request and takes no floor. -/
theorem adminKindOk_kinds (rq : apply.IRRModel) (h : apply.adminKindOk rq) :
    apply.isKVKind (apply.dispatchKind rq) = false ∧
      apply.isFloorKind (apply.dispatchKind rq) = false := by
  unfold apply.adminKindOk at h
  split at h <;> rename_i hk <;> simp_all [apply.isKVKind, apply.isFloorKind]

/-- A plain request's kind: no admin permission needed (`plainCover`). -/
theorem plainCover_needAdmin (rq : apply.IRRModel) (hp : plainCover rq)
    (hk : putgetKind (apply.dispatchKind rq)) : apply.needAdminPermission rq = false := by
  unfold plainCover at hp
  unfold putgetKind at hk
  rcases hk with h | h | h | h | h <;> rw [h] at hp <;> simp only at hp <;>
    first | exact hp.2.1 | exact hp.2

/-- A plain request of no KV kind (a cluster request) is no write and takes no floor. -/
theorem putget_nonKV (k : apply.ReqKind) (h1 : putgetKind k) (h2 : apply.isKVKind k = false) :
    ¬ writeKind k ∧ apply.isFloorKind k = false := by
  unfold putgetKind at h1
  rcases h1 with h | h | h | h | h <;> subst h <;> simp_all [writeKind, apply.isKVKind, apply.isFloorKind]

/-- **A plain request that writes nothing keeps the log and the chain** (any `v3`). -/
theorem applyStep_keep (rq : apply.IRRModel) (v3 : Bool) (x x' : apply.ApplyKV)
    (out : apply.ApplyOut) (hp : plainCover rq) (hw : ¬ writeKind (apply.dispatchKind rq))
    (h : apply.applyStep rq v3 x x' out) : x'.log = x.log ∧ x'.chain = x.chain := by
  obtain ⟨hc, hl⟩ := applyStep_plain [] rq v3 x x' out hp h
  refine ⟨?_, hc⟩
  rcases hl with hl | ⟨-, hl⟩
  · rw [hl]
    unfold dispatchLog
    split
    · rfl
    · split
      · exact chainLog_nonwrite rq [] x.log hw x.chain
      · rfl
  · exact hl

/-- **A plain request replayed (`v3` false) keeps the log and the chain.** -/
theorem applyStep_plain_false (rq : apply.IRRModel) (x x' : apply.ApplyKV)
    (out : apply.ApplyOut) (hp : plainCover rq) (h : apply.applyStep rq false x x' out) :
    x'.log = x.log ∧ x'.chain = x.chain := by
  obtain ⟨hc, hl⟩ := applyStep_plain [] rq false x x' out hp h
  refine ⟨?_, hc⟩
  rcases hl with hl | ⟨-, hl⟩
  · rw [hl]; unfold dispatchLog; rw [if_pos (Or.inr rfl)]
  · exact hl

/-- An entry with no data leaves the mode-`on` model's state. -/
theorem kvEntryOn_nodata (c₀ : w64) (ch : apply.Chain) (s : auth.AuthState × mvcc.Log)
    (m : EntryModel) (hd : m.data = []) : kvEntryOn c₀ ch s m = s := by
  unfold kvEntryOn
  rw [if_neg (fun h => h.2 hd), kvEntry_nonwrite c₀ ch [] s.2 m (Or.inl hd)]


/-- **An entry's premise in the mode `on` at a small log, from its shape** (`entryOk_of_shape`'s, for
the apply loop with auth on): a plain request's as there, an admitted admin request's from the
chain's mode (`authEnable` dispatchable only with auth on). -/
theorem entryOkOn_of_shape (x : apply.ApplyKV) (m : EntryModel) (hs : entryShapeOn m)
    (ht : m.typ = W32 0) (hl : x.log.length ≤ mvcc.logCh x.log + 2)
    (hc : mvcc.logCh x.log < 2 ^ 48) (ha : x.chain.authOn = true) : entryOkOn x m := by
  rcases hs.1 ht with hd | ⟨rq, hdec, hid, hsh⟩
  · exact Or.inl hd
  · refine Or.inr ⟨rq, hdec, hid, ?_⟩
    rcases hsh with hsh | hadm
    · exact ⟨Or.inl (hsh.2 x.log (rqSmall_of_small x.log rq hl hc)), hsh.1 _⟩
    · refine ⟨Or.inr hadm, ?_, ?_, fun _ => ha⟩
      · intro h; unfold apply.adminKindOk at hadm; rw [h] at hadm; exact hadm
      · intro h; unfold apply.adminKindOk at hadm; rw [h] at hadm; exact hadm


/-- A conf change leaves the mode-`on` model's state. -/
theorem kvEntryOn_cc (c₀ : w64) (ch : apply.Chain) (s : auth.AuthState × mvcc.Log)
    (m : EntryModel) (ht : m.typ ≠ W32 0) : kvEntryOn c₀ ch s m = s := by
  unfold kvEntryOn
  rw [if_neg (fun h => ht h.1), kvEntry_nonwrite c₀ ch [] s.2 m (Or.inr (Or.inl ht))]

end pure

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The applied logs grow with the index, in the mode** (`appliedMono_of_inv`'s). -/
theorem appliedMono_of_invM (on : Bool) (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) :
    srvAppliedInvM (GF := GF) on s E γr ⊢ appliedMono γr := by
  iintro #Hinv
  iunfold appliedMono
  iintro !> %i %j %L1 %L2 %hij #H1 #H2
  iunfold srvAppliedInvM at Hinv
  iinv Hinv with Hi Hclose
  iunfold srvAppliedBodyM at Hi
  icases Hi with ⟨%vat, %v, %L, %M, %p, Hat, >Hauth, >HM, >Hp, >%HMk, >#HL, >#Hc, >#Hkl⟩
  ihave %Hm1 : iprop(⌜M.lookup i = some L1⌝) $$ [HM]
  · iunfold appliedLogAt at H1
    iapply ghost_map_lookup $$ HM H1
  ihave %Hm2 : iprop(⌜M.lookup j = some L2⌝) $$ [HM]
  · iunfold appliedLogAt at H2
    iapply ghost_map_lookup $$ HM H2
  imod Hclose $$ [Hat Hauth HM Hp] with -
  · inext
    iunfold srvAppliedBodyM
    iexists vat, v, L, M, p
    iframe Hat Hauth HM Hp HL Hc Hkl
    ipureintro; exact HMk
  imodintro
  ipureintro
  exact HMk.2.2 i j L1 L2 Hm1 Hm2 hij

/-- **An admin entry leaves the rest buckets** (`restAfter_other`: it sets no cluster field). -/
theorem srvRest_admin (E : apply.AEnv GF) (γr : ReadNames) (A : List EntryModel) (m : EntryModel)
    (rq : apply.IRRModel) (ht : m.typ = W32 0) (hd : m.data ≠ [])
    (hdec : apply.irrDecode m.data = some rq) (hk : apply.adminKindOk rq) :
    srvRest E γr (A ++ [m]) = srvRest E γr A := by
  obtain ⟨h1, h2⟩ := adminKindOk_noCluster rq hk
  rw [srvRest_snoc, restEntry_normal _ _ rq _ ht hd hdec, apply.restAfter_other rq _ _ h1 h2]
  rfl

/-- **After the entry, in the mode `on`** (`kvApplied_next`'s counterpart): the apply thread's KV
ghost state at the next state `x'` and auth state `st'` (the model's after `A ++ [m]`, the chain
the start's), and the applied log the mode-`on` model of the committed raft log through `i`
(`kvLogAtM true`). -/
theorem kvApplied_nextOn (γr : ReadNames) (A : List EntryModel) (m : EntryModel)
    (x' : apply.ApplyKV) (st' : auth.AuthState) (i : w64)
    (hi : uint.Z i = uint.Z γr.raft.ai0 + A.length + 1) (hc : x'.chain = γr.kv.ch0) :
    kvAppliedLOn (GF := GF) γr.raft γr.kv srvAuthSt0 (A ++ [m]) (st', x'.log) ⊢
      kvAppliedOn γr.raft γr.kv srvAuthSt0 (A ++ [m]) x' st' ∗ kvLogAtM true γr i x'.log := by
  iintro H
  ihave ⟨#HB, %Hl⟩ : iprop(srvRLogLb γr.raft (A ++ [m]) ∗
      ⌜(st', x'.log) = kvRaftOfOn γr.kv.c0 γr.kv.ch0 (srvAuthSt0, γr.kv.log0) (A ++ [m])⌝) $$ [H]
  · iunfold kvAppliedLOn at H; icases H with ⟨#HB, -, -, %Hl⟩; iframe HB; ipureintro; exact Hl
  isplitl [H]
  · iunfold kvAppliedOn
    iframe H
    ipureintro; exact hc
  iunfold kvLogAtM
  iexists A ++ [m]
  iframe HB
  ipureintro
  refine ⟨?_, ?_⟩
  · simp only [List.length_append, List.length_singleton]
    push_cast
    omega
  · rw [kvModelM_true]
    unfold kvModelOn
    rw [← Hl]

/-- **The certificates `apply.Apply` asks of a request that writes nothing** (a cluster request,
`kv_certPre`'s): every outcome leaves the log, which is certified. -/
theorem kv_certPre_keep (E : apply.AEnv GF) (γk : KVNames) (hγ : E.γ.cok = γk.cok)
    (c : apply.Chain) (rq : apply.IRRModel) (log : mvcc.Log) (hp : plainCover rq)
    (hw : ¬ writeKind (apply.dispatchKind rq)) :
    kvCert (GF := GF) γk log ⊢ apply.certPre E c rq log := by
  iintro #Hc
  unfold apply.certPre
  imodintro
  iintro %oc %hs
  have hl : oc.logAfter log = log := by
    rcases chainStep_plain [] c rq log oc hp hs with h | ⟨h, -⟩
    · rw [h, chainLog_nonwrite rq [] log hw c]
    · exact h
  rw [hl]
  iapply kvCert_certOk γk E.γ hγ $$ Hc

/-- `kvAppliedLOn`'s certificate and model equation. -/
theorem kvAppliedLOn_cert (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState)
    (A : List EntryModel) (s : auth.AuthState × mvcc.Log) :
    kvAppliedLOn (GF := GF) γ γk st₀ A s ⊢ kvAppliedLOn γ γk st₀ A s ∗ kvCert γk s.2 ∗
      ⌜s = kvRaftOfOn γk.c0 γk.ch0 (st₀, γk.log0) A⌝ := by
  iintro H
  iunfold kvAppliedLOn at H
  icases H with ⟨#HB, Hhi, #Hc, %Hl⟩
  isplitl [Hhi]
  · iunfold kvAppliedLOn; iframe HB Hhi Hc; ipureintro; exact Hl
  iframe Hc
  ipureintro; exact Hl


/-- **No registration in the mode `on` either** (a conf change's id: `entryWaitOk`'s refutation of
`reqWaitR`, at `reqWaitRM on`: the same claim, at the mode-off result). -/
theorem reqWaitRM_none (on : Bool) (ρ : ReqNames) (E : apply.AEnv GF) (id : w64) :
    (□ ∀ Ψ, reqWaitR (GF := GF) ρ E id Ψ -∗ False) ⊢ □ ∀ Ψ, reqWaitRM on ρ E id Ψ -∗ False := by
  iintro #H
  imodintro
  iintro %Ψ HR
  iunfold reqWaitRM at HR
  icases HR with ⟨%d, %rq, %γf, %F, Hc, Hf, %Hp⟩
  iapply H $$ %(resultΨ E ρ rq F)
  iunfold reqWaitR
  iexists d, rq, γf, F
  iframe Hc Hf
  ipureintro; exact ⟨Hp.1, rfl, Hp.2.2⟩

/-- The member's registry, from the server's view in the mode (`isServer_waitIs`'s). -/
theorem isServerM_waitIs (on : Bool) (s : Loc) (γ : ApplyNames) (ci : Loc)
    (TM : MetaCI → IProp GF) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) :
    isServerM (GF := GF) on s γ ci TM E ρ γr ⊢ idWaitIs ρ.ids ρ.ids.pfx ρ.wait := by
  iintro #H
  iunfold isServerM at H
  icases H with ⟨-, -, ⟨%v, #Hf⟩, -⟩
  iunfold srvFieldsAtM at Hf
  icases Hf with ⟨-, -, -, #Hwi, -⟩
  iunfold waitInvM at Hwi
  icases Hwi with ⟨-, #Hn⟩
  iexact Hn

end lemmas

section row
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The apply thread's auth row with auth on, opened** (see the file header). -/
theorem srvAuthApplyResB_open (s : Loc) (E : apply.AEnv GF) (γa : auth.AuthNames)
    (st : auth.AuthState) (hM : E.authMode = .on γa) :
    srvAuthApplyResB (GF := GF) s E st ⊢ ∃ (stl bel : Loc) (T : IProp GF) (hs : List auth.AuthState),
      srvAuthStoreAddr s ↦□ auth.authIface stl ∗ roLendsAuthBe E.RO stl bel ∗
      authWBackendAt bel (.on γa) E.P E.f T ∗
      apply.isAuthStepsX (auth.authIface stl) E.P E.f (.on γa) (auth.tieRes stl (.on γa))
        (adminW stl bel (.on γa) E.P E.f T) ∗
      auth.authOwnFu γa hs ∗ auth.tieRes stl (.on γa) hs ∗ ⌜hs.getLast? = some st⌝ ∗ T ∗
      auth.tpAdmin stl (.on γa) ∗
      (∀ (hs' : List auth.AuthState) (st' : auth.AuthState), auth.authOwnFu γa hs' -∗
        auth.tieRes stl (.on γa) hs' -∗ ⌜hs'.getLast? = some st'⌝ -∗ T -∗
        auth.tpAdmin stl (.on γa) -∗ srvAuthApplyResB s E st') := by
  iintro HR
  iunfold srvAuthApplyResB at HR
  icases HR with ⟨%stl, %bel, #Hf, HB, #Hlens, #Hro⟩
  have hB : ∀ st', authApplyResB (GF := GF) E.authMode stl st' bel E.P E.f =
      authApplyResB (GF := GF) (.on γa) stl st' bel E.P E.f := by intro; rw [hM]
  irevert HB
  rw [hB]
  unfold authApplyResB
  iintro ⟨%hs, %P0, %f0, %T, %be, Ho, HX, #Hw, HT, Htp, %Hl, #Hwa, #Hsteps⟩
  iexists stl, bel, T, hs
  iframe Hf Hro Hwa Hsteps Ho HX HT Htp
  isplitr
  · ipureintro; exact Hl
  iintro %hs' %st' Ho' HX' %Hl' HT' Htp'
  iunfold srvAuthApplyResB
  iexists stl, bel
  iframe Hf Hlens Hro
  rw [hB]
  unfold authApplyResB
  iexists hs', P0, f0, T, be
  iframe Ho' HX' Hw HT' Htp' Hwa Hsteps
  ipureintro; exact Hl'

/-- **Publication at the apply thread's auth row** (the auth plan's E3t): with the built part's
publication (`srvUberBase`'s `authPublishM`), the row at the model's auth state `st` (the latest of
its history) gets a published index recording `st` (`authPubAt`), the row kept. -/
theorem srvAuthApplyResB_publish (s : Loc) (ua : GoInterface) (E : apply.AEnv GF)
    (γa : auth.AuthNames) (st : auth.AuthState) (hM : E.authMode = .on γa) :
    srvUberBase (GF := GF) s ua E ⊢ srvAuthApplyResB s E st ={⊤}=∗
      srvAuthApplyResB s E st ∗ authPubAt E.authMode st := by
  iintro #Hb HAR
  icases srvAuthApplyResB_open s E γa st hM $$ HAR with ⟨%stl, %bel, %T, %hs, #Hf, #Hro, #Hwa,
    #Hsteps, Hfu, Ht, %Hl, HT, Htp, Hclose⟩
  iunfold srvUberBase at Hb
  icases Hb with ⟨%au, %le, #Hauf, -, -, -, %stl', %Hau, #HPub, -⟩
  subst Hau
  icombine Hf Hauf gives %Hst
  have Hst' := apply.mkOk_ptr_inj _ _ _ Hst
  subst Hst'
  ihave #HPub' : authPublishM (GF := GF) (.on γa) stl $$ []
  · rw [← hM]; iexact HPub
  iunfold auth.authOwnFu at Hfu
  icases Hfu with ⟨Ho, Hfuel⟩
  imod authPubAt_publish γa stl hs st Hl $$ HPub' Ho Ht with ⟨Ho, Ht, #Hpa⟩
  ihave HAR := Hclose $$ %hs %st [Ho Hfuel] Ht %Hl HT Htp
  · iunfold auth.authOwnFu; iframe Ho Hfuel
  imodintro
  iframe HAR
  rw [hM]
  iexact Hpa

variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **The uber-applier's latest-state admin triples at the opened row** (see the file header). -/
theorem srv_uberAuthStepsL_at
    (hUA : apply.applierV3backend.UserAdd.fuelSpecX (GF := GF) (hG := hG))
    (hRA : apply.applierV3backend.RoleAdd.fuelSpecX (GF := GF) (hG := hG))
    (hUGR : apply.applierV3backend.UserGrantRole.fuelSpecX (GF := GF) (hG := hG))
    (hRGP : apply.applierV3backend.RoleGrantPermission.fuelSpecX (GF := GF) (hG := hG))
    (hAE : apply.applierV3backend.AuthEnable.fuelSpecX (GF := GF) (hG := hG))
    (hApplyL : apply.authApplierV3.Apply.specL (GF := GF) (hG := hG))
    (hApply : apply.applierV3backend.Apply.spec (GF := GF) (hG := hG))
    (s : Loc) (ua : GoInterface) (E : apply.AEnv GF) (γa : auth.AuthNames) (stl bel : Loc)
    (T : IProp GF) (hM : E.authMode = .on γa) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      srvUberBase s ua E ∗ srvAuthStoreAddr s ↦□ auth.authIface stl ∗
      apply.isAuthStepsX (auth.authIface stl) E.P E.f (.on γa) (auth.tieRes stl (.on γa))
        (adminW stl bel (.on γa) E.P E.f T) ⊢
      apply.uberAuthStepsL ua E (adminW stl bel (.on γa) E.P E.f T)
        (fun γa' h => iprop(auth.authOwnFu γa' h ∗ auth.tieRes stl (.on γa) h))
        (auth.latestRes stl (.on γa)) := by
  iintro ⟨#Hpkg, #Hb, #Hf, #Hsteps⟩
  iunfold srvUberBase at Hb
  icases Hb with ⟨%au, %le, #Hauf, #Hlef, #Hub, -, %stl', %Hau, -, #HL⟩
  subst Hau
  icombine Hf Hauf gives %Hst
  have Hst' := apply.mkOk_ptr_inj _ _ _ Hst
  subst Hst'
  have hL : authStoreLatestM (GF := GF) E.authMode (auth.authIface stl) E.RD stl =
      apply.isAuthStoreL (auth.authIface stl) E.RD E.authMode (auth.latestRes stl (.on γa)) := by
    rw [hM]; rfl
  iapply (apply.uberAuthStepsL_of_base hUA hRA hUGR hRGP hAE hApplyL hApply ua E (auth.authIface stl)
    le (auth.tieRes stl (.on γa)) (adminW stl bel (.on γa) E.P E.f T) (auth.latestRes stl (.on γa)))
  iframe Hpkg Hub
  isplitr
  · rw [← hL]; iexact HL
  rw [hM]
  iexact Hsteps

variable [package_sem' : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `srvApplyKVOn`'s log certificate and chain mode (`srvApplyKV_idxCert`'s, `applyKV_authOn`). -/
theorem srvApplyKVOn_idxCert (s : Loc) (E : apply.AEnv GF) (γw : GName) (x : apply.ApplyKV)
    (st : auth.AuthState) :
    srvApplyKVOn (GF := GF) s E γw x st ⊢ srvApplyKVOn s E γw x st ∗ mvcc.idxCert E.γ.idx x.log ∗
      ⌜x.chain.authOn = E.authOn⌝ := by
  iintro H
  iunfold srvApplyKVOn at H
  icases H with ⟨%ua, Hua, #Hb, #Hap, Hkv, Hw⟩
  icases applyKV_idxCert E ua x $$ Hkv with ⟨Hkv, #Hc⟩
  ihave ⟨Hkv, %Ha⟩ := applyKV_authOn E ua x $$ Hkv
  isplitl [Hua Hkv Hw]
  · iunfold srvApplyKVOn
    iexists ua
    isplitl [Hua]
    · iexact Hua
    isplitr
    · iexact Hb
    isplitr
    · iexact Hap
    isplitl [Hkv]
    · iexact Hkv
    iexact Hw
  iframe Hc
  ipureintro; exact Ha


/-- `srvApplyKVOn`'s backend ownership, lent (`srvApplyKV_beOwn`'s). -/
theorem srvApplyKVOn_beOwn (s : Loc) (E : apply.AEnv GF) (γw : GName) (x : apply.ApplyKV)
    (st : auth.AuthState) :
    srvApplyKVOn (GF := GF) s E γw x st ⊢
      srvBeOwn s E ∗ (srvBeOwn s E -∗ srvApplyKVOn s E γw x st) := by
  iintro H
  iunfold srvApplyKVOn at H
  icases H with ⟨%ua, Hua, #Hb, #Hap, Hkv, Hbo, Hrest⟩
  iframe Hbo
  iintro Hbo
  iunfold srvApplyKVOn
  iexists ua
  isplitl [Hua]
  · iexact Hua
  isplitr
  · iexact Hb
  isplitr
  · iexact Hap
  isplitl [Hkv]
  · iexact Hkv
  isplitl [Hbo]
  · iexact Hbo
  iexact Hrest

/-- **One write token, the count raised by one, with auth on** (`srvWTPool_take_n`'s). -/
theorem srvWTPool_take_nOn (s : Loc) (E : apply.AEnv GF) (γp γw : GName) (x : apply.ApplyKV)
    (st : auth.AuthState) (n : Nat) :
    ⊢ srvWTPool (GF := GF) E γp -∗ ⧗ 1 -∗ srvWTTaken γp n -∗ srvApplyKVOn s E γw x st ={⊤}=∗
      mvcc.storeWT E.γ ∗ srvWTTaken γp (n + 1) ∗ srvApplyKVOn s E γw x st := by
  iintro #Hp Hr #Hv HKV
  icases srvApplyKVOn_beOwn s E γw x st $$ HKV with ⟨Hbo, HKV⟩
  icases srvBeOwn_frag s E $$ Hbo with ⟨%d, %Hd, Hg, Hbo⟩
  unfold srvWTPool
  iinv Hp with ⟨%a, %m, %d', >Ha, >Hg', >Hn, >Hc, >%Hb, Hrt⟩ Hclose
  ihave %Hdd := dghostVar_agree E.γbe d _ d' _ $$ Hg Hg'
  subst Hdd
  unfold srvWTTaken
  icases monoNatLbOwn_valid γp 1 a n $$ Hc Hv with %Hva
  replace Hva := Hva.2
  icases receipt_add_one_lt a $$ [Hr Ha] with ⟨%Hlt, Ha⟩
  · iframe
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  icases wbToks_split d m' $$ Hn with ⟨Ht, Hn⟩
  imod mono_nat_own_update (a + 1) (by omega) $$ Hc with ⟨Hc, #Hlb⟩
  imod Hclose $$ [Ha Hg' Hn Hc Hrt] with -
  · inext
    iexists a + 1, m', d
    iframe Ha Hg' Hn Hc Hrt
    ipureintro; omega
  ihave Hbo := Hbo $$ Hg
  ihave HKV := HKV $$ Hbo
  imodintro
  iframe HKV
  isplitl [Ht]
  · iapply storeWT_of_wbTok E.γ d Hd $$ Ht
  iapply monoNatLbOwn_le (n + 1) (by omega) $$ Hlb

/-- **The apply thread's KV log is small, with auth on** (`srvApplyKV_small`'s). -/
theorem srvApplyKVOn_small (s : Loc) (E : apply.AEnv GF) (γw : GName) (x : apply.ApplyKV)
    (st : auth.AuthState) :
    srvApplyKVOn (GF := GF) s E γw x st ⊢
      ⌜x.log.length ≤ mvcc.logCh x.log + 2 ∧ mvcc.logCh x.log < 2 ^ 48⌝ ∗
        srvApplyKVOn s E γw x st := by
  apply persistent_entails_right
  iintro H
  iunfold srvApplyKVOn at H
  icases H with ⟨%ua, -, -, -, Hkv, -⟩
  iunfold apply.applyKV at Hkv
  icases Hkv with ⟨%p, -, -, Hk⟩
  iunfold apply.kvOwn at Hk
  icases Hk with ⟨-, Hsw, -⟩
  iunfold txn.kvWriter at Hsw
  icases Hsw with ⟨Hsw, -⟩
  iapply txn.soleWriter_small' $$ Hsw

/-- **The uber-applier and the store's reader's token, lent, with auth on** (`srvApplyKV_ua_rt`'s,
for `applyConfChange`). -/
theorem srvApplyKVOn_ua_rt (s : Loc) (E : apply.AEnv GF) (γw : GName) (x : apply.ApplyKV)
    (st : auth.AuthState) :
    srvApplyKVOn (GF := GF) s E γw x st ⊢ ∃ ua : GoInterface, srvUberApplyAddr s ↦ ua ∗
      apply.applierFor ua E ∗ mvcc.storeRT E.γ ∗
      (srvUberApplyAddr s ↦ ua -∗ mvcc.storeRT E.γ -∗ srvApplyKVOn s E γw x st) := by
  iintro H
  iunfold srvApplyKVOn at H
  icases H with ⟨%ua, Hua, #Hb, #Hap, Hkv, Hbo, Hrest⟩
  iunfold apply.applyKV at Hkv
  icases Hkv with ⟨%p, %Hp, Hu, Ho⟩
  iunfold apply.kvOwn at Ho
  icases Ho with ⟨Hsr, Hsw, Hll, Hrd, Hwo⟩
  icases mvcc.writerOwn_rt E.γ $$ Hwo with ⟨Hrt, Hwo⟩
  iexists ua
  iframe Hua Hrt
  isplitr
  · iexact Hap
  iintro Hua Hrt
  ihave Hwo := Hwo $$ Hrt
  iunfold srvApplyKVOn
  iexists ua
  isplitl [Hua]
  · iexact Hua
  isplitr
  · iexact Hb
  isplitr
  · iexact Hap
  isplitl [Hu Hsr Hsw Hll Hrd Hwo]
  · iunfold apply.applyKV
    iexists p
    iframe Hu
    isplitr
    · ipureintro; exact Hp
    iunfold apply.kvOwn
    iframe
  isplitl [Hbo]
  · iexact Hbo
  iexact Hrest


/-- **The mode-`on` row lends its part shared with the mode-off row** (`srvApplyKV_core`'s; E3p, for
`snapshot`). -/
theorem srvApplyKVOn_core (s : Loc) (E : apply.AEnv GF) (γw : GName) (x : apply.ApplyKV)
    (st : auth.AuthState) :
    srvApplyKVOn (GF := GF) s E γw x st ⊢
      ∃ ua, srvApplyKVCore s E γw x ua ∗
        (srvApplyKVCore s E γw x ua -∗ srvApplyKVOn s E γw x st) := by
  iintro H
  iunfold srvApplyKVOn at H
  icases H with ⟨%ua, Hua, #Hb, #Hap, Hkv, Hbo, Hra, Har, Hw⟩
  iexists ua
  isplitl [Hua Hkv Hbo Hra Hw]
  · iunfold srvApplyKVCore
    isplitl [Hua]
    · iexact Hua
    isplitr
    · iexact Hap
    isplitl [Hkv]
    · iexact Hkv
    isplitl [Hbo]
    · iexact Hbo
    isplitl [Hra]
    · iexact Hra
    iexact Hw
  iintro Hc
  iunfold srvApplyKVCore at Hc
  icases Hc with ⟨Hua, -, Hkv, Hbo, Hra, Hw⟩
  iunfold srvApplyKVOn
  iexists ua
  isplitl [Hua]
  · iexact Hua
  isplitr
  · iexact Hb
  isplitr
  · iexact Hap
  isplitl [Hkv]
  · iexact Hkv
  isplitl [Hbo]
  · iexact Hbo
  isplitl [Hra]
  · iexact Hra
  isplitl [Har]
  · iexact Har
  iexact Hw

end row

end EtcdGrove
end Perennial
