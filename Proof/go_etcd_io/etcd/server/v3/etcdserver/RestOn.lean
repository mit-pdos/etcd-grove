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
/-- An entry with no data (`srvRest_nodata` at the auth-on table). -/
theorem srvRestM_nodata (E : apply.AEnv GF) (γr : ReadNames) (A : List EntryModel) (m : EntryModel)
    (ht : m.typ = W32 0) (hd : m.data = []) : srvRestM true E γr A ⊢ srvRestM true E γr (A ++ [m]) := by
  iintro H
  ihave ⟨H, HU⟩ := (srvRestM_eq_at true E γr A).1 $$ H
  iapply srvRestM_snoc true E γr A m (appliedTableM_true_nodata γr A m ht hd)
  rw [restEntry_nodata _ _ _ ht hd]
  iframe H HU

open Iris.ProofMode in
/-- An admitted admin request (`srvRest_admin` at the auth-on table). -/
theorem srvRestM_admin (E : apply.AEnv GF) (γr : ReadNames) (A : List EntryModel) (m : EntryModel)
    (rq : apply.IRRModel) (ht : m.typ = W32 0) (hd : m.data ≠ [])
    (hdec : apply.irrDecode m.data = some rq) (hk : apply.adminKindOk rq) :
    srvRestM true E γr A ⊢ srvRestM true E γr (A ++ [m]) := by
  obtain ⟨h1, h2⟩ := adminKindOk_noCluster rq hk
  iintro H
  ihave ⟨H, HU⟩ := (srvRestM_eq_at true E γr A).1 $$ H
  iapply srvRestM_snoc true E γr A m (appliedTableM_true_nonLease γr A m rq ht hd hdec
    (adminKindOk_nonGrant rq hk) (adminKindOk_nonRevoke rq hk))
  rw [restEntry_normal _ _ rq _ ht hd hdec, apply.restAfter_other rq _ _ h1 h2]
  iframe H HU

open Iris.ProofMode in
/-- `srvRest_applyP0` at the auth-on table (a triple whose post carries no grant conjuncts). -/
theorem srvRestM_applyP0 (E : apply.AEnv GF) (γr : ReadNames) (A : List EntryModel) (m : EntryModel)
    (rq : apply.IRRModel) (v3 : Bool) (x x' : apply.ApplyKV) (out : apply.ApplyOut) (f : w64 → w64)
    (ht : m.typ = W32 0) (hd : m.data ≠ []) (hdec : apply.irrDecode m.data = some rq)
    (hv3 : v3 = decide (uint.Z γr.kv.c0 < uint.Z m.index))
    (hp : plainOrCmp rq) (hs : apply.applyStep rq v3 x x' out)
    (hfb : E.lg = true → leaseTTLsGeReq (appliedTableM true γr A) f) :
    srvGrantIf E ∗ srvReqsIf E (appliedTableM true γr A) ∗
      apply.ltHalf E (srvIds E (appliedTableM true γr A).ids) ∗
      E.RO (apply.restOut rq v3 out
        (apply.restLeasesWith f (srvIds E (appliedTableM true γr A).ids)
          (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A)))) ∗
      srvEver E (A ++ [m]) ⊢
      srvRestM true E γr (A ++ [m]) := by
  have hk := plainOrCmp_nonLease rq hp
  rw [restOut_plainOrCmp rq v3 x x' out _ hp hs]
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
  iapply srvRestM_applyP0 E γr A m rq v3 x x' out f ht hd hdec hv3 hp hs hfb
  iframe HG HQ HL HR HU

end arm

end EtcdGrove
end Perennial
