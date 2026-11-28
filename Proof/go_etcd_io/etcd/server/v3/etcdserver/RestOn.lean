/-
**The rest buckets one entry later with auth on** (auth-lease S3a §6, Draft rev 5 §4): `srvRestM true`
(`srvRestT` at the mode-`on` model's table, `appliedTableM true`) after an entry that neither grants nor
revokes, whose table the model keeps (`appliedTableM_true_nonLease`, `appliedTableM_true_nodata`): the
`ApplyCmpArm`/`InvRest` lemmas (`srvRest_nodata`, `srvRest_admin`, `srvRest_applyP`, `srvRest_applyP0`) at
the auth-on table. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ApplyCmpArm
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ImageLeasesOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ApplyNormalOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.NoSpaceDeadOn

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section pure
variable [GooseExts]

/-- The auth-on table one entry later is the mode-`on` model's step. -/
theorem appliedTableM_true_snoc (γr : ReadNames) (A : List EntryModel) (m : EntryModel) :
    appliedTableM true γr (A ++ [m]) =
      (kvEntryOn γr.kv.c0 γr.kv.ch0
        (kvRaftOfOn γr.kv.c0 γr.kv.ch0 (srvAuthSt0, γr.kv.log0, []) (γr.raft.pre ++ A)) m).2.2 := by
  rw [appliedTableM_true]; unfold kvLeasesOn
  rw [← List.append_assoc, kvRaftOfOn_snoc]

theorem appliedTableM_true_eq (γr : ReadNames) (A : List EntryModel) :
    appliedTableM true γr A =
      (kvRaftOfOn γr.kv.c0 γr.kv.ch0 (srvAuthSt0, γr.kv.log0, []) (γr.raft.pre ++ A)).2.2 := by
  rw [appliedTableM_true]; rfl

/-- **An entry that neither grants nor revokes keeps the auth-on table.** -/
theorem appliedTableM_true_nonLease (γr : ReadNames) (A : List EntryModel) (m : EntryModel)
    (rq : apply.IRRModel) (ht : m.typ = W32 0) (hd : m.data ≠ [])
    (hdec : apply.irrDecode m.data = some rq) (hg : apply.dispatchKind rq ≠ .leaseGrant)
    (hr : apply.dispatchKind rq ≠ .leaseRevoke) :
    appliedTableM true γr (A ++ [m]) = appliedTableM true γr A := by
  rw [appliedTableM_true_snoc, appliedTableM_true_eq]
  generalize kvRaftOfOn γr.kv.c0 γr.kv.ch0 (srvAuthSt0, γr.kv.log0, []) (γr.raft.pre ++ A) = S
  rcases kvEntryOn_table_eq_or γr.kv.c0 γr.kv.ch0 S m with h | h
  · exact h
  · rw [h]; unfold kvTable; rw [if_pos ht, if_neg hd]
    simp only [hdec, dispatchTable]
    split
    · rfl
    · exact chainTable_nonLease _ rq _ hg hr

/-- **An entry with no data keeps the auth-on table.** -/
theorem appliedTableM_true_nodata (γr : ReadNames) (A : List EntryModel) (m : EntryModel)
    (ht : m.typ = W32 0) (hd : m.data = []) :
    appliedTableM true γr (A ++ [m]) = appliedTableM true γr A := by
  rw [appliedTableM_true_snoc, appliedTableM_true_eq]
  generalize kvRaftOfOn γr.kv.c0 γr.kv.ch0 (srvAuthSt0, γr.kv.log0, []) (γr.raft.pre ++ A) = S
  rcases kvEntryOn_table_eq_or γr.kv.c0 γr.kv.ch0 S m with h | h
  · exact h
  · rw [h]; simp [kvTable, ht, hd]

/-- **At either mode, an entry that neither grants nor revokes keeps the table** (auth-lease S3a2 §5). -/
theorem appliedTableM_nonLease {on : Bool} (γr : ReadNames) (A : List EntryModel) (m : EntryModel)
    (rq : apply.IRRModel) (ht : m.typ = W32 0) (hd : m.data ≠ [])
    (hdec : apply.irrDecode m.data = some rq) (hg : apply.dispatchKind rq ≠ .leaseGrant)
    (hr : apply.dispatchKind rq ≠ .leaseRevoke) :
    appliedTableM on γr (A ++ [m]) = appliedTableM on γr A := by
  cases on
  · simp only [appliedTableM_false]; exact appliedTable_nonLease γr A m rq ht hd hdec hg hr
  · exact appliedTableM_true_nonLease γr A m rq ht hd hdec hg hr

/-- **At either mode, an entry with no data keeps the table.** -/
theorem appliedTableM_nodata {on : Bool} (γr : ReadNames) (A : List EntryModel) (m : EntryModel)
    (ht : m.typ = W32 0) (hd : m.data = []) :
    appliedTableM on γr (A ++ [m]) = appliedTableM on γr A := by
  cases on
  · simp only [appliedTableM_false]; exact appliedTable_nodata γr A m ht hd
  · exact appliedTableM_true_nodata γr A m ht hd

end pure

section arm
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

open Iris.ProofMode in
/-- **`srvRestM true` one entry later, the table kept**, from the opened image through a writer `g` that
commutes with the lease records and is the entry's rest effect. -/
theorem srvRestM_keep (E : apply.AEnv GF) (γr : ReadNames) (A : List EntryModel) (m : EntryModel)
    (hT : appliedTableM true γr (A ++ [m]) = appliedTableM true γr A)
    (g : apply.RestM → apply.RestM)
    (hg : ∀ id t r, g (apply.restGrantT id t r) = apply.restGrantT id t (g r))
    (hre : restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ (A ++ [m])) =
      g (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A)))
    (f : w64 → w64) (hfb : E.lg = true → leaseTTLsGeReq (appliedTableM true γr A) f) :
    srvGrantIf E ∗ srvReqsIf E (appliedTableM true γr A) ∗
      apply.ltHalf E (srvIds E (appliedTableM true γr A).ids) ∗
      E.RO (g (apply.restLeasesWith f (srvIds E (appliedTableM true γr A).ids)
        (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A)))) ∗
      srvEver E (A ++ [m]) ⊢ srvRestM true E γr (A ++ [m]) := by
  iintro ⟨#HG, #HQ, HL, HR, HU⟩
  iapply (srvRestM_eq_at true E γr (A ++ [m])).2
  rw [hT, hre]
  iframe HU
  iapply (srvRestAt_open E _ _).2
  iexists f
  iframe HL HG HQ
  isplitr
  · ipureintro; exact hfb
  rw [← apply.restLeasesWith_comm g hg]
  iexact HR

open Iris.ProofMode in
/-- An entry with no data (`srvRest_nodata` at the mode's table; auth-lease S3a2 §5: at either mode). -/
theorem srvRestM_nodata {on : Bool} (E : apply.AEnv GF) (γr : ReadNames) (A : List EntryModel) (m : EntryModel)
    (ht : m.typ = W32 0) (hd : m.data = []) : srvRestM on E γr A ⊢ srvRestM on E γr (A ++ [m]) := by
  iintro H
  ihave ⟨H, HU⟩ := (srvRestM_eq_at on E γr A).1 $$ H
  iapply srvRestM_snoc on E γr A m (appliedTableM_nodata γr A m ht hd)
  rw [restEntry_nodata _ _ _ ht hd]
  iframe H HU

open Iris.ProofMode in
/-- An admitted admin request (`srvRest_admin` at the mode's table; S3a2 §5: at either mode). -/
theorem srvRestM_admin {on : Bool} (E : apply.AEnv GF) (γr : ReadNames) (A : List EntryModel) (m : EntryModel)
    (rq : apply.IRRModel) (ht : m.typ = W32 0) (hd : m.data ≠ [])
    (hdec : apply.irrDecode m.data = some rq) (hk : apply.adminKindOk rq) :
    srvRestM on E γr A ⊢ srvRestM on E γr (A ++ [m]) := by
  obtain ⟨h1, h2⟩ := adminKindOk_noCluster rq hk
  iintro H
  ihave ⟨H, HU⟩ := (srvRestM_eq_at on E γr A).1 $$ H
  iapply srvRestM_snoc on E γr A m (appliedTableM_nonLease γr A m rq ht hd hdec
    (adminKindOk_nonGrant rq hk) (adminKindOk_nonRevoke rq hk))
  rw [restEntry_normal _ _ rq _ ht hd hdec, apply.restAfter_other rq _ _ h1 h2]
  iframe H HU

open Iris.ProofMode in
/-- `srvRest_applyP0` at the auth-on table (a triple whose post carries no grant conjuncts). -/
theorem srvRestM_applyP0 (E : apply.AEnv GF) (γr : ReadNames) (A : List EntryModel) (m : EntryModel)
    (rq : apply.IRRModel) (v3 : Bool) (x x' : apply.ApplyKV) (out : apply.ApplyOut) (f : w64 → w64)
    (ht : m.typ = W32 0) (hd : m.data ≠ []) (hdec : apply.irrDecode m.data = some rq)
    (hv3 : v3 = decide (uint.Z γr.kv.c0 < uint.Z m.index))
    (hp : plainOrCmp rq ∨ kvCover rq) (hs : apply.applyStep rq v3 x x' out)
    (hfb : E.lg = true → leaseTTLsGeReq (appliedTableM true γr A) f) :
    srvGrantIf E ∗ srvReqsIf E (appliedTableM true γr A) ∗
      apply.ltHalf E (srvIds E (appliedTableM true γr A).ids) ∗
      E.RO (apply.restOut rq v3 out
        (apply.restLeasesWith f (srvIds E (appliedTableM true γr A).ids)
          (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A)))) ∗
      srvEver E (A ++ [m]) ⊢
      srvRestM true E γr (A ++ [m]) := by
  have hk : apply.dispatchKind rq ≠ .leaseGrant ∧ apply.dispatchKind rq ≠ .leaseRevoke := by
    rcases hp with hp | hp
    · exact plainOrCmp_nonLease rq hp
    · unfold kvCover at hp
      constructor <;> intro h <;> rw [h] at hp <;> exact hp.elim
  rw [show apply.restOut rq v3 out _ = _ from by
    rcases hp with hp | hp
    · exact restOut_plainOrCmp rq v3 x x' out _ hp hs
    · exact restOut_plain rq v3 x x' out _ hp hs]
  apply srvRestM_keep E γr A m (appliedTableM_true_nonLease γr A m rq ht hd hdec hk.1 hk.2)
    (apply.restAfter rq v3) (fun id t r => apply.restAfter_restGrantT rq v3 id t r) _ f hfb
  rw [← List.append_assoc, restModel_append, restEntry_normal _ _ rq _ ht hd hdec, ← hv3]

open Iris.ProofMode in
/-- `srvRest_applyP` at the auth-on table (`Apply.spec`'s post, a covered request or a compaction). -/
theorem srvRestM_applyP (E : apply.AEnv GF) (γr : ReadNames) (A : List EntryModel) (m : EntryModel)
    (rq : apply.IRRModel) (v3 : Bool) (x x' : apply.ApplyKV) (out : apply.ApplyOut) (f : w64 → w64)
    (ht : m.typ = W32 0) (hd : m.data ≠ []) (hdec : apply.irrDecode m.data = some rq)
    (hv3 : v3 = decide (uint.Z γr.kv.c0 < uint.Z m.index))
    (hp : plainOrCmp rq) (hs : apply.applyStep rq v3 x x' out)
    (hfb : E.lg = true → leaseTTLsGeReq (appliedTableM true γr A) f) :
    srvGrantIf E ∗ srvReqsIf E (appliedTableM true γr A) ∗ grantReqA E rq v3 out ∗
      ⌜apply.grantOutOkA x.chain rq v3 (srvIds E (appliedTableM true γr A).ids) out⌝ ∗
      apply.ltHalf E (apply.grantIdsA rq v3 out (srvIds E (appliedTableM true γr A).ids)) ∗
      (∃ t : w64, ⌜apply.grantTTLOk rq t⌝ ∗ E.RO (apply.grantRestA t rq v3 out (apply.restOut rq v3 out
        (apply.restLeasesWith f (srvIds E (appliedTableM true γr A).ids)
          (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A)))))) ∗
      srvEver E (A ++ [m]) ⊢
      srvRestM true E γr (A ++ [m]) := by
  have hk := (plainOrCmp_nonLease rq hp).1
  rw [apply.grantIdsA_nonGrant _ _ _ _ hk]
  simp only [apply.grantRestA_nonGrant _ _ _ _ _ hk]
  iintro ⟨#HG, #HQ, -, -, HL, ⟨%t, -, HR⟩, HU⟩
  iapply srvRestM_applyP0 E γr A m rq v3 x x' out f ht hd hdec hv3 (Or.inl hp) hs hfb
  iframe HG HQ HL HR HU

end arm

/-! ### The grant and revocation arms with auth on (auth-lease S3a §6, session 6) -/

section leasePure
variable [GooseExts]

/-- **The mode-`on` model's table never holds the id `0`** from a start whose table does not
(`kvTableOf_ne0`'s counterpart). -/
theorem kvRaftOfOn_ne0 (c₀ : w64) (ch : apply.Chain) :
    ∀ (s : OnState) (A : List EntryModel), W64 0 ∉ s.2.2.ids → W64 0 ∉ (kvRaftOfOn c₀ ch s A).2.2.ids
  | s, [], h => h
  | s, m :: A, h => kvRaftOfOn_ne0 c₀ ch (kvEntryOn c₀ ch s m) A (by
      rcases kvEntryOn_table_eq_or c₀ ch s m with e | e <;> rw [e]
      · exact h
      · exact kvTable_ne0 c₀ ch s.2.2 m h)

/-- An entry that decodes: its table is `dispatchTable`'s. -/
theorem kvTable_dec (c₀ : w64) (ch : apply.Chain) (lt : LeaseTable) (m : EntryModel)
    (rq : apply.IRRModel) (ht : m.typ = W32 0) (hd : m.data ≠ [])
    (hdec : apply.irrDecode m.data = some rq) :
    kvTable c₀ ch lt m = dispatchTable ch rq (decide (uint.Z c₀ < uint.Z m.index)) lt := by
  unfold kvTable; rw [if_pos ht, if_neg hd]; simp only [hdec]

/-- **A grant in the mode `on`**: no admin, no kind the auth layer checks, so today's step at the
table, which keeps the log (`kvEntry_grant`). -/
theorem kvEntryOn_grant (c₀ : w64) (ch : apply.Chain) (s : OnState) (m : EntryModel)
    (rq : apply.IRRModel) (hdec : apply.irrDecode m.data = some rq) (hg : apply.grantKindOk rq) :
    kvEntryOn c₀ ch s m = (s.1, s.2.1, kvTable c₀ ch s.2.2 m) := by
  rw [kvEntryOn_of_granted c₀ ch s m rq hdec hg.2.1
      (fun h => by rw [hg.1] at h; simp [apply.authKVKind, apply.isKVKind] at h),
    kvEntry_grant c₀ ch s.2.2 s.2.1 m rq hdec hg]

/-- **A grant dispatched at the start's chain in either auth mode** (`dispatchStep_start_grant` at
`on`: the auth layer checks no grant): applied, or the backend's rejection. -/
theorem dispatchStep_start_grantB (on : Bool) (rq : apply.IRRModel) (hg : apply.grantKindOk rq)
    (log : mvcc.Log) (o : apply.Outcome)
    (h : apply.dispatchStep (apply.alarmChain on false false) rq true log o) :
    (∃ l ns, o = .applied l ns) ∨ o = .rejected .backend := by
  obtain ⟨hk, hna, -, -⟩ := hg
  unfold apply.dispatchStep at h
  rw [if_neg (by simp [hk, apply.preV3Kind]), if_pos (Or.inr hk)] at h
  simp only [apply.alarmChain, apply.baseChain, apply.chainStep, apply.authChecks, hk, hna,
    Bool.false_eq_true, ↓reduceIte, _root_.or_self, apply.backendStep] at h
  rcases h with h | h
  · exact Or.inl ⟨_, _, h⟩
  · exact Or.inr h

/-- A revocation's backend table is a sub-table. -/
theorem backendTable_sub_revoke (rq : apply.IRRModel) (lt : LeaseTable)
    (hk : apply.dispatchKind rq = .leaseRevoke) : ∀ p ∈ backendTable rq lt, p ∈ lt := by
  intro p hp
  unfold backendTable at hp
  rw [hk] at hp
  simp only at hp
  split at hp
  · split at hp
    · exact (List.mem_filter.1 hp).1
    · exact hp
  · exact hp

/-- The auth-on chain's table for a revocation: the backend's. -/
theorem kvTable_revoke_on (c₀ : w64) (lt : LeaseTable) (m : EntryModel) (rq : apply.IRRModel)
    (ht : m.typ = W32 0) (hd : m.data ≠ []) (hdec : apply.irrDecode m.data = some rq)
    (hv : uint.Z c₀ < uint.Z m.index) (hk : apply.dispatchKind rq = .leaseRevoke) :
    kvTable c₀ (apply.alarmChain true false false) lt m = backendTable rq lt := by
  rw [kvTable_dec c₀ _ lt m rq ht hd hdec, decide_eq_true hv]
  unfold dispatchTable
  rw [if_neg (by simp [hk, apply.preV3Kind])]
  simp [apply.alarmChain, apply.baseChain, chainTable]

open Classical in
/-- **After `apply.Apply` on a revocation, in the mode `on`** (`kvOn_after_kv`'s counterpart, Draft
§6): dispatched; the auth layer's refusal keeps the model's table, an application is the backend's
(the lease dropped); the model's state after the entry the apply thread's. -/
theorem revokeOn_after (c₀ : w64) (st : auth.AuthState) (lt : LeaseTable) (x x' : apply.ApplyKV)
    (m : EntryModel) (rq : apply.IRRModel) (out : apply.ApplyOut)
    (ht : m.typ = W32 0) (hd : m.data ≠ []) (hdec : apply.irrDecode m.data = some rq)
    (hv : uint.Z c₀ < uint.Z m.index) (hr : apply.revokeKindOk rq)
    (γa : auth.AuthNames) (hs : List auth.AuthState) (hl : hs.getLast? = some st)
    (hz : noZeroEnds rq) (hlive : liveSt lt.ids (mvcc.stateAfter x.log)) (h0 : W64 0 ∉ lt.ids)
    (hdet : entryDetOn c₀ (st, x.log, lt) m) (hch : x.chain = apply.alarmChain true false false)
    (hstep : apply.applyStep rq true x x' out)
    (hout : ∀ o b, out = .dispatched o b →
      apply.kvOutL (.on γa) hs (auth.authInfoM (apply.principalOf rq)) (.quota .backend) rq x.log o) :
    x'.chain = x.chain ∧ ∃ o b lt', out = .dispatched o b ∧
      (st, x'.log, lt') = kvEntryOn c₀ x.chain (st, x.log, lt) m ∧
      ((o = .rejected .auth ∧ lt' = lt) ∨ (∃ l ns, o = .applied l ns ∧ lt' = backendTable rq lt)) := by
  cases out with
  | skipped => exact absurd hstep.1 (by rw [hr.2.2]; decide)
  | rejected => exact absurd hstep.1 (by rw [hr.2.1]; decide)
  | dispatched o b =>
    obtain ⟨-, hdisp, hlog, hchn, -⟩ := hstep
    have hc : x'.chain = x.chain := by
      rcases hchn with h | ⟨-, hka, -⟩
      · exact h
      · rw [hr.1] at hka; cases hka
    have ho := outcomeOn_of_kvOutL_revoke c₀ (st, x.log, lt) m rq ht hd hdec hv hr.2.1 hr.1 γa hs hl
      hz hlive h0 o (hout o b rfl)
    have he := outcomeOn_eq c₀ _ (st, x.log, lt) _ m hdet ho
    rw [kvTable_revoke_on c₀ lt m rq ht hd hdec hv hr.1] at he
    have hdisp' := hdisp
    rw [hch] at hdisp'
    rcases dispatchStep_on_off rq x.log o hdisp' with h | h
    · refine ⟨hc, o, b, lt, rfl, ?_, Or.inl ⟨h, rfl⟩⟩
      rw [hlog, hch, ← he, if_pos h]
    · obtain ⟨l, ns, hon⟩ := dispatchStep_start_revoke rq hr x.log o h
      refine ⟨hc, o, b, backendTable rq lt, rfl, ?_, Or.inr ⟨l, ns, hon, rfl⟩⟩
      rw [hlog, hch, ← he, if_neg (by rw [hon]; intro h'; cases h')]

/-- **A revocation's live set and image one entry later at a table `T`** (`revokeA_table`'s
dispatched case, the auth layer's refusal included): refused, kept; applied, the backend's. -/
theorem revokeA_tableT (rq : apply.IRRModel) (out : apply.ApplyOut) (f : w64 → w64)
    (T T' : LeaseTable) (hk : apply.dispatchKind rq = .leaseRevoke)
    (ho : ∃ o b, out = .dispatched o b ∧
      ((o = .rejected .auth ∧ T' = T) ∨ (∃ l ns, o = .applied l ns ∧ T' = backendTable rq T)))
    (R : apply.RestM) (hR : ∀ id, apply.restRevoke id R = R) :
    T'.ids = apply.revokeIdsA rq true out T.ids ∧
      apply.revokeRestA T.ids rq true out (apply.restLeasesWith f T.ids R) =
        apply.restLeasesWith f T'.ids R := by
  obtain ⟨o, b, rfl, ho⟩ := ho
  rcases ho with ⟨rfl, rfl⟩ | ⟨l, ns, rfl, rfl⟩
  · simp only [apply.revokeIdsA, apply.revokeRestA, apply.revokeIds_rejected,
      apply.revokeRest_rejected]
    constructor <;> first | trivial | rfl
  simp only [apply.revokeIdsA, apply.revokeRestA]
  cases hid : rq.leaseRevoke with
  | none =>
    have h1 : backendTable rq T = T := by unfold backendTable; rw [hk]; simp [hid]
    rw [h1]
    unfold apply.revokeIds apply.revokeRest
    rw [if_pos ⟨hk, rfl⟩, if_pos ⟨hk, rfl⟩, hid]
    exact ⟨rfl, rfl⟩
  | some id =>
    rw [apply.revokeIds_applied rq id l ns _ hk hid,
      apply.revokeRest_applied _ rq id l ns _ hk hid]
    have hf : (backendTable rq T).ids = T.ids.filter (· != id) := by
      unfold backendTable; rw [hk]; simp only [hid]
      split
      · unfold LeaseTable.ids
        rw [List.filter_map]
        congr 1
        apply List.filter_congr
        intro p _
        cases h : (p.1 == id) <;> simp_all [bne]
      · rename_i hm
        exact (List.filter_eq_self.2 (fun a ha => by
          simp only [bne_iff_ne, ne_eq, decide_eq_true_eq]
          intro e; subst e; exact hm ha)).symm
    refine ⟨hf, ?_⟩
    rw [hf]
    split
    · rw [restRevoke_leasesWith, hR]
    · rename_i hm
      rw [List.filter_eq_self.2 (fun a ha => by
        simp only [bne_iff_ne, ne_eq, decide_eq_true_eq]
        intro e; subst e; exact hm ha)]

/-- A revocation needs no KV permission (`reqPerms` is empty). -/
theorem noZeroEnds_revoke (rq : apply.IRRModel) (hk : apply.dispatchKind rq = .leaseRevoke) :
    noZeroEnds rq := by
  intro x hx; simp [reqPerms, hk] at hx

end leasePure

section leaseArm
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

open Iris.ProofMode in
/-- **A committed entry's grant id is new, auth on** (`kv_entry_grantFresh`'s, from `kvInvOn`'s
`kvGrantIds`). -/
theorem kv_entry_grantFresh_on (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState)
    (A : List EntryModel) (m : EntryModel) :
    ⊢ kvInvOn (GF := GF) γ γk st₀ -∗ srvRaftLogInv γ -∗ srvRLogLb γ (A ++ [m]) ={⊤}=∗
      ⌜m.data ≠ [] → ∀ gid, entryRevGrantId γk.lm m = some gid →
        gid ∉ logRevGrantIds γk.lm (A.filter fun m => decide (m.data ≠ []))⌝ := by
  iintro #Hinv #Hr #HB
  iunfold kvInvOn at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%L, HL, Hσ, Hh, %Hok, #Hw, HG⟩
  imod srvRLog_lb γ (⊤ \ ↑kvN) (mask_ndot_ne' nroot "raft_commit" "server_kv" (by decide))
    L (A ++ [m]) $$ Hr HL HB with ⟨HL, %Hp⟩
  iunfold kvGrantIds at HG
  icases HG with ⟨%U, %HU, HUs⟩
  imod Hclose $$ [HL Hσ Hh HUs] with -
  · inext; iexists L; iframe HL Hσ Hh Hw
    isplitr
    · ipureintro; exact Hok
    iunfold kvGrantIds; iexists U; iframe HUs; ipureintro; exact HU
  imodintro
  ipureintro
  intro hd gid hg
  have hnd : (logRevGrantIds γk.lm L).Nodup := by
    exact kvGrantIds_nodup_of HU
  exact grantId_fresh_transfer γk.lm A L m Hp.2.1 Hp.2.2 hnd hd gid hg

open Iris.ProofMode in
/-- **A grant's outcomes keep the log** (`chainStep_grant_logAfter`): its certificate is the
log's witness. -/
theorem kv_certPre_grantOn (E : apply.AEnv GF) (γ : ServerRaftNames) (γk : KVNames)
    (st₀ : auth.AuthState) (hNx : E.Nx = kvNxOn γ γk st₀)
    (c : apply.Chain) (rq : apply.IRRModel) (log : mvcc.Log)
    (hk : apply.dispatchKind rq = .leaseGrant) :
    kvNxOn (GF := GF) γ γk st₀ log ⊢ apply.certPre E c rq log := by
  iintro #Hc
  unfold apply.certPre
  imodintro
  iintro %oc %hs
  rw [apply.chainStep_grant_logAfter rq hk log c oc hs, hNx]
  iexact Hc

open Iris.ProofMode in
/-- **The certificates a revocation's latest-state outcomes need, in the mode `on`**
(`kv_certPreVW_on`'s counterpart, by `outcomeOn_of_kvOutL_revoke`). -/
theorem kv_certPreVW_revoke_on (E : apply.AEnv GF) (γ : ServerRaftNames) (γk : KVNames)
    (st₀ : auth.AuthState) (hNx : E.Nx = kvNxOn γ γk st₀) (c₀ : w64)
    (s : OnState) (m : EntryModel) (rq : apply.IRRModel)
    (ht : m.typ = W32 0) (hd : m.data ≠ []) (hdec : apply.irrDecode m.data = some rq)
    (hv : uint.Z c₀ < uint.Z m.index) (hr : apply.revokeKindOk rq)
    (γa : auth.AuthNames) (hs : List auth.AuthState) (hl : hs.getLast? = some s.1)
    (hlive : liveSt s.2.2.ids (mvcc.stateAfter s.2.1)) (h0 : W64 0 ∉ s.2.2.ids)
    (hdet : entryDetOn c₀ s m) :
    kvNxOn (GF := GF) γ γk st₀ (kvEntryOn c₀ (apply.alarmChain true false false) s m).2.1 ⊢
      apply.certPreVW true E (apply.alarmChain true false false) rq s.2.1
        (apply.kvOutL (.on γa) hs (auth.authInfoM (apply.principalOf rq)) (.quota .backend) rq
          s.2.1) := by
  simp only [apply.certPreVW, ↓reduceIte]
  iintro #Hc
  iunfold apply.certPreW
  iintro !> %oc %h
  have ho := outcomeOn_of_kvOutL_revoke c₀ s m rq ht hd hdec hv hr.2.1 hr.1 γa hs hl
    (noZeroEnds_revoke rq hr.1) hlive h0 oc h.2
  have he := outcomeOn_eq c₀ _ s _ m hdet ho
  have hlog : oc.logAfter s.2.1 = (kvEntryOn c₀ (apply.alarmChain true false false) s m).2.1 := by
    rw [← he]
  rw [hlog, hNx]
  iexact Hc

open Iris.ProofMode in
/-- **`srvRestT` one entry later through `Apply`'s post** (`srvRest_applyG` at any table: the table
after `T'` is `dispatch`'s of the table before `T`). -/
theorem srvRestT_applyG (E : apply.AEnv GF) (γr : ReadNames) (A : List EntryModel) (m : EntryModel)
    (rq : apply.IRRModel) (v3 : Bool) (x x' : apply.ApplyKV) (out : apply.ApplyOut) (f : w64 → w64)
    (T T' : LeaseTable)
    (ht : m.typ = W32 0) (hd : m.data ≠ []) (hdec : apply.irrDecode m.data = some rq)
    (hv3 : v3 = decide (uint.Z γr.kv.c0 < uint.Z m.index))
    (hTt : T' = dispatchTable x.chain rq v3 T)
    (hrev : apply.dispatchKind rq ≠ .leaseRevoke)
    (hg : apply.dispatchKind rq = .leaseGrant → grantPropOk E.lm rq)
    (hr : ∀ r, apply.restOut rq v3 out r = apply.restAfter rq v3 r)
    (hs : apply.applyStep rq v3 x x' out)
    (hfb : E.lg = true → leaseTTLsGeReq T f) :
    srvGrantIf E ∗ srvReqsIf E T ∗ grantReqA E rq v3 out ∗
      ⌜apply.grantOutOkA x.chain rq v3 (srvIds E T.ids) out⌝ ∗
      apply.ltHalf E (apply.grantIdsA rq v3 out (srvIds E T.ids)) ∗
      (∃ t : w64, ⌜apply.grantTTLOk rq t⌝ ∗ E.RO (apply.grantRestA t rq v3 out (apply.restOut rq v3 out
        (apply.restLeasesWith f (srvIds E T.ids)
          (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A)))))) ∗
      srvEver E (A ++ [m]) ⊢
      srvRestT E γr T' (A ++ [m]) := by
  have hre : restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ (A ++ [m])) =
      apply.restAfter rq v3 (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A)) := by
    rw [← List.append_assoc, restModel_append, restEntry_normal _ _ rq _ ht hd hdec, ← hv3]
  have hcomm := apply.restLeasesWith_comm (apply.restAfter rq v3)
    (fun id t r => apply.restAfter_restGrantT rq v3 id t r)
  simp only [hr, hcomm]
  iintro ⟨#Hgi, #Hrq, #Hgr, %Hgo, HL, ⟨%t, %Htt, HR⟩, HU⟩
  cases hlg : E.lg
  · have hk : apply.dispatchKind rq ≠ .leaseGrant := fun hk => by
      exact (hg hk).1 (apply.AEnv.lm_of_lg_false hlg)
    unfold srvRestT
    rw [hlg, hre]
    simp only [srvIds, hlg, Bool.false_eq_true, ↓reduceIte, apply.restLeasesWith_nil,
      apply.grantRestA_nonGrant _ _ _ _ _ hk]
    iexact HR
  · have hgk : apply.dispatchKind rq = .leaseGrant → apply.grantKindOk rq := fun hk => (hg hk).2
    simp only [srvIds, hlg, ↓reduceIte] at Hgo
    simp only [srvIds, hlg, ↓reduceIte]
    obtain ⟨f', hf', hfT, hfN⟩ := apply.grantRestA_leasesF x.chain t rq v3 out f T.ids
      (apply.restAfter rq v3 (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A))) Hgo
    have hT : apply.grantIdsA rq v3 out T.ids = T'.ids := by
      rw [hTt]
      exact (dispatchTableA_ids rq v3 x x' out _ hrev hgk hs Hgo).symm
    have hb : leaseTTLsGeReq T' f' := by
      rw [hTt]
      exact dispatchTableA_ttls rq v3 x x' out _ hrev hgk hs Hgo f' t
        (leaseTTLsGeReq_congr (hfb hlg) hfT) Htt hfN
    unfold srvRestT srvRestAt srvGrantIf
    irevert Hrq
    unfold srvReqsIf
    simp only [hlg, ↓reduceIte]
    iintro #Hrq
    rw [hf', hT, ← hre]
    iframe HL Hgi HU
    isplitl [HR]
    · iexists f'
      iframe HR
      ipureintro; exact hb
    rw [hTt]
    iapply srvReqs_dispatchA E rq v3 x x' out _ hrev hgk hs Hgo
    iframe Hrq Hgr

open Iris.ProofMode in
/-- **`srvRestT` one entry later, a revocation through the latest-state triple's post**
(`srvRest_applyR` at any table, the auth layer's refusal included: the table after `T'` is `T`
refused, the backend's applied). -/
theorem srvRestT_applyR (E : apply.AEnv GF) (γr : ReadNames) (A : List EntryModel) (m : EntryModel)
    (rq : apply.IRRModel) (out : apply.ApplyOut) (f : w64 → w64) (T T' : LeaseTable)
    (ht : m.typ = W32 0) (hd : m.data ≠ []) (hdec : apply.irrDecode m.data = some rq)
    (hv3 : true = decide (uint.Z γr.kv.c0 < uint.Z m.index))
    (hr : revokePropOk E.lm rq)
    (ho : ∃ o b, out = .dispatched o b ∧
      ((o = .rejected .auth ∧ T' = T) ∨ (∃ l ns, o = .applied l ns ∧ T' = backendTable rq T)))
    (hfb : E.lg = true → leaseTTLsGeReq T f) :
    srvGrantIf E ∗ srvReqsIf E T ∗
      apply.ltHalf E (apply.revokeIdsA rq true out (srvIds E T.ids)) ∗
      E.RO (apply.revokeRestA (srvIds E T.ids) rq true out
        (apply.restOut rq true out (apply.restLeasesWith f (srvIds E T.ids)
          (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A))))) ∗
      srvEver E (A ++ [m]) ⊢
      srvRestT E γr T' (A ++ [m]) := by
  have hk := hr.2.1
  have hlg : E.lg = true := apply.AEnv.lg_true_of_lm (by rw [hr.1]; decide)
  have hnc := dispatchKind_leaseRevoke_noCluster rq hk
  have hra : ∀ r, apply.restAfter rq true r = r := fun r => apply.restAfter_other rq true r hnc.1 hnc.2
  have hre : restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ (A ++ [m])) =
      restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A) := by
    rw [← List.append_assoc, restModel_append, restEntry_normal _ _ rq _ ht hd hdec, ← hv3, hra]
  have hro : ∀ r, apply.restOut rq true out r = r := fun r => by
    obtain ⟨o, b, rfl, -⟩ := ho
    exact hra r
  obtain ⟨hT, hR⟩ := revokeA_tableT rq out f T T' hk ho
    (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A))
    (fun id => restRevoke_restModel id _ _ _)
  have hsub : ∀ p ∈ T', p ∈ T := by
    obtain ⟨o, b, -, h⟩ := ho
    rcases h with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩
    · exact fun p hp => hp
    · exact backendTable_sub_revoke rq T hk
  unfold srvRestT srvRestAt srvGrantIf srvIds srvReqsIf
  simp only [hlg, ↓reduceIte, hro]
  rw [hR, ← hT, hre]
  iintro ⟨#HG, #HQ, HL, HR, HU⟩
  iframe HL HG HU
  isplitl [HR]
  · iexists f
    iframe HR
    ipureintro; exact leaseTTLsGeReq_sub (hfb hlg) hsub
  iapply srvReqs_sub E _ _ hsub $$ HQ

end leaseArm

section leaseNoSpace
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]
variable [errors_sem : _root_.Perennial.errors.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

open Iris.ProofMode in
/-- **`apply.Apply`'s result for a grant with auth on** (`applyResultIs_notNoSpace_grant` at the
auth-on start chain, which passes a grant through). -/
theorem applyResultIs_notNoSpace_grantOn (E : apply.AEnv GF) (rq : apply.IRRModel)
    (x x' : apply.ApplyKV) (ar : Loc) (out : apply.ApplyOut) (hg : apply.grantKindOk rq)
    (hch : x.chain = apply.alarmChain true false false)
    (hs : apply.applyStep rq true x x' out) :
    go_etcd_io.etcd.server.v3.etcdserver.apply.applyErrVars (GF := GF) ⊢
      go_etcd_io.etcd.server.v3.lease.leaseInit -∗
      apply.grantResA E rq out ar -∗ apply.applyResultIs rq true x.log ar out -∗
      apply.grantResA E rq out ar ∗ apply.applyResultIs rq true x.log ar out ∗
      (⌜ar = null⌝ ∨ ∃ err : GoInterface,
        structFieldRef go_etcd_io.etcd.server.v3.etcdserver.apply.Result go!"Err" ar ↦□ err ∗
        notNoSpaceErr err) := by
  have hg' := hg
  obtain ⟨hk, hna, hns, -⟩ := hg
  iintro #Hv #Hli Hg H
  cases out with
  | skipped => exact absurd hs.1 (by rw [hns]; decide)
  | rejected => exact absurd hs.1 (by rw [hna]; decide)
  | dispatched o skip =>
    have hoo := dispatchStep_start_grantB true rq hg' x.log o (hch ▸ hs.2.1)
    simp only [apply.applyResultIs, apply.dispatchResult, _root_.or_true, ↓reduceIte]
    icases H with ⟨%hnn, %v, #Hvv, Hans, #HeI⟩
    simp only [apply.grantResA]
    unfold apply.grantRes
    rw [if_pos ⟨hk, hnn⟩]
    icases Hg with ⟨%v', #Hvv', Hga, Hwb, %Hap⟩
    icombine Hvv Hvv' gives %Hvv''
    subst Hvv''
    ihave ⟨Hwb, #Hn⟩ : iprop((⌜o = .rejected .backend⌝ -∗ lease.lessorErrIs v.Err') ∗
        notNoSpaceErr v.Err') $$ [Hwb]
    · rcases hoo with ha | hb
      · iframe Hwb; rw [Hap ha]; iunfold notNoSpaceErr; ileft; ipureintro; rfl
      · ihave #HL := Hwb $$ %hb
        isplitl []
        · iintro -; iexact HL
        iapply lessorErrIs_notNoSpace $$ Hv Hli HL
    isplitl [Hga Hwb]
    · iexists v; iframe Hvv Hga Hwb; ipureintro; exact Hap
    isplitl [Hans]
    · isplitr
      · ipureintro; exact hnn
      iexists v; iframe Hvv Hans HeI
    iright; iexists v.Err'; iframe Hn; iapply apply.result_err_ro; iexact Hvv

open Iris.ProofMode in
/-- **`apply.Apply`'s result for a revocation with auth on** (`applyResultIs_notNoSpace_revoke` at the
auth-on start chain): the auth layer's refusal (an auth error), or applied (`nil` or
`ErrLeaseNotFound`); not `ErrNoSpace`'s. -/
theorem applyResultIs_notNoSpace_revokeOn (rq : apply.IRRModel) (x x' : apply.ApplyKV) (ar : Loc)
    (out : apply.ApplyOut) (hr : apply.revokeKindOk rq)
    (hch : x.chain = apply.alarmChain true false false)
    (hs : apply.applyStep rq true x x' out) :
    go_etcd_io.etcd.server.v3.etcdserver.apply.applyErrVars (GF := GF) ⊢
      go_etcd_io.etcd.server.v3.lease.leaseInit -∗
      apply.applyResultIs rq true x.log ar out -∗
      apply.applyResultIs rq true x.log ar out ∗
      (⌜ar = null⌝ ∨ ∃ err : GoInterface,
        structFieldRef go_etcd_io.etcd.server.v3.etcdserver.apply.Result go!"Err" ar ↦□ err ∗
        notNoSpaceErr err) := by
  have hr' := hr
  obtain ⟨hk, hna, hns⟩ := hr
  iintro #Hv #Hli H
  cases out with
  | skipped => exact absurd hs.1 (by rw [hns]; decide)
  | rejected => exact absurd hs.1 (by rw [hna]; decide)
  | dispatched o skip =>
    have hd := hs.2.1
    rw [hch] at hd
    rcases dispatchStep_on_off rq x.log o hd with hrej | hoff
    · subst hrej
      simp only [apply.applyResultIs, apply.dispatchResult, _root_.or_true, ↓reduceIte]
      icases H with ⟨%hnn, %v, #Hvv, Hans, #HeI⟩
      ihave #Hn : notNoSpaceErr v.Err' $$ [Hans]
      · unfold apply.dispatchAnswer
        rw [hk]
        dsimp only
        icases Hans with ⟨%r, %hresp, Hrv⟩
        simp only [apply.revokeOutcomeIs, apply.rejErrIs]
        icases Hrv with ⟨-, -, #HA⟩
        iunfold authApplyErrIs at HA
        icases HA with ⟨-, #HV⟩
        icases Hv with ⟨-, -, -, -, -, -, -, -, -, -, #Hap, -⟩
        iapply authErrVarIs_notNoSpace v.Err' $$ Hap HV
      isplitl [Hans]
      · isplitr
        · ipureintro; exact hnn
        iexists v
        iframe Hvv Hans HeI
      iright; iexists v.Err'; iframe Hn; iapply apply.result_err_ro; iexact Hvv
    obtain ⟨l, ns, ho⟩ := dispatchStep_start_revoke rq hr' x.log o hoff
    subst ho
    simp only [apply.applyResultIs, apply.dispatchResult, _root_.or_true, ↓reduceIte]
    icases H with ⟨%hnn, %v, #Hvv, Hans, #HeI⟩
    unfold apply.dispatchAnswer
    rw [hk]
    dsimp only
    icases Hans with ⟨%r, %hresp, Hrv⟩
    simp only [apply.revokeOutcomeIs]
    icases Hrv with ⟨%hrn, #HaE, #HrE⟩
    ihave #Hn : notNoSpaceErr v.Err' $$ []
    · iunfold apply.revokeErrIs at HrE
      icases HrE with (%he | ⟨%e, #He, %heq⟩)
      · iunfold notNoSpaceErr; ileft; ipureintro; exact he
      · iapply lessorErrIs_notNoSpace $$ Hv Hli
        iunfold lease.lessorErrIs
        iexists _, e
        iframe He
        ipureintro; exact ⟨Or.inl rfl, heq⟩
    isplitl []
    · isplitr
      · ipureintro; exact hnn
      iexists v
      iframe Hvv HeI
      iexists r
      isplitr
      · ipureintro; exact hresp
      (try iframe HaE)
      (try iframe HrE)
      ipureintro; exact hrn
    iright; iexists v.Err'; iframe Hn; iapply apply.result_err_ro; iexact Hvv

end leaseNoSpace

end EtcdGrove
end Perennial
