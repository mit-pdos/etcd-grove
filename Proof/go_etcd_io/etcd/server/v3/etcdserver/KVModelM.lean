/-
**The KV model in either auth mode** (`kvModelM`, `logShapeM`; moved out of `ServerOn.lean`,
strict M1, 2026-11-05, so that the server's store invariant over mvcc's API, `KVStoreApi.lean`,
imports the model without the server's proofs). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVAuthModel

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- **The committed log's shapes in the auth mode `on`**: `logShape` off (in a cluster that grants
leases or not, `lg`: the lease-grant stage's §2.8), `logShapeOn lm` on (auth-lease S3a: at the mode). -/
def logShapeM (on : Bool) (lm : lease.Mode) (L : List EntryModel) : Prop :=
  match on with
  | false => logShape lm L
  | true => logShapeOn lm L

/-- The shapes of either mode give a conf change's id `0`. -/
theorem logShapeM_cc (on : Bool) (lm : lease.Mode) (L : List EntryModel) (h : logShapeM on lm L) :
    ∀ m ∈ L, m.typ ≠ W32 0 → ccIdOf m.data = W64 0 := by
  cases on
  · exact fun m hm => (h m hm).2
  · exact fun m hm => (h m hm).2

theorem logShapeM_false (lm : lease.Mode) (L : List EntryModel) : logShapeM false lm L = logShape lm L :=
  rfl

theorem logShapeM_true (lm : lease.Mode) (L : List EntryModel) : logShapeM true lm L = logShapeOn lm L := rfl

theorem logShapeM_append (on : Bool) (lm : lease.Mode) (A B : List EntryModel) (h : logShapeM on lm (A ++ B)) :
    logShapeM on lm A := by
  cases on
  · exact fun m hm => h m (List.mem_append_left _ hm)
  · exact fun m hm => h m (List.mem_append_left _ hm)

/-- **`srvRest`'s lease table in the auth mode `on`** (auth-lease S3a, Draft rev 5 §4): the off table
`appliedTable` (`kvLeases` over the raft prefix and the applied entries, which ignores the auth layer)
off; with auth on the mode-`on` model's table over the same entries (`kvLeasesOn … srvAuthSt0`), which
keeps the table at a revocation the auth layer refused. -/
def appliedTableM (on : Bool) (γr : ReadNames) (A : List EntryModel) : LeaseTable :=
  if on then kvLeasesOn γr.kv srvAuthSt0 (γr.raft.pre ++ A) else appliedTable γr A

theorem appliedTableM_false (γr : ReadNames) (A : List EntryModel) :
    appliedTableM false γr A = appliedTable γr A := by
  simp [appliedTableM]

theorem appliedTableM_true (γr : ReadNames) (A : List EntryModel) :
    appliedTableM true γr A = kvLeasesOn γr.kv srvAuthSt0 (γr.raft.pre ++ A) := by
  simp [appliedTableM]

/-- **The model's table and `srvRest`'s agree at an empty raft prefix** (Draft rev 5 §3, review r4 N1
(a)): the mode-`on` model folds over the applied entries alone, `srvRest`'s table over the prefix and
them. -/
theorem appliedTableM_eq_model (γr : ReadNames) (A : List EntryModel) (h : γr.raft.pre = []) :
    (appliedTableM true γr A).ids =
      (kvRaftOfOn γr.kv.c0 γr.kv.ch0 (srvAuthSt0, γr.kv.log0, []) A).2.2.ids := by
  rw [appliedTableM_true, h, List.nil_append]; rfl

/-- **The KV model of the committed log `L` in the auth mode `on`**: `kvModel` off, the mode-`on`
model from the server's start state (`kvModelOn … srvAuthSt0`) on. -/
def kvModelM (on : Bool) (γk : KVNames) (L : List EntryModel) : mvcc.Log :=
  match on with
  | false => kvModel γk L
  | true => kvModelOn γk srvAuthSt0 L

theorem kvModelM_false (γk : KVNames) (L : List EntryModel) :
    kvModelM false γk L = kvModel γk L := rfl

theorem kvModelM_true (γk : KVNames) (L : List EntryModel) :
    kvModelM true γk L = kvModelOn γk srvAuthSt0 L := rfl

end pure

section rest
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **`srvRest` in the auth mode `on`** (auth-lease S3a, Draft rev 5 §4; the split decided by
etcd-grove-81 as a form): the off `srvRest`, and with auth on `srvRestT` at the mode-`on` model's
table (`appliedTableM true`). -/
def srvRestM (on : Bool) (E : apply.AEnv GF) (γr : ReadNames) (A : List EntryModel) : IProp GF :=
  match on with
  | false => srvRest E γr A
  | true => srvRestT E γr (appliedTableM true γr A) A

theorem srvRestM_false (E : apply.AEnv GF) (γr : ReadNames) (A : List EntryModel) :
    srvRestM (GF := GF) false E γr A = srvRest E γr A := rfl

/-- In a cluster that grants none, the mode does not matter. -/
theorem srvRestM_lg_false (on : Bool) (E : apply.AEnv GF) (γr : ReadNames) (A : List EntryModel)
    (h : E.lg = false) : srvRestM (GF := GF) on E γr A = srvRest E γr A := by
  cases on
  · rfl
  · unfold srvRestM; rw [srvRest_eq_T]; exact srvRestT_lg_false E γr _ _ A h

/-- `srvRestRp` in the auth mode `on` (Draft rev 5 §4, review r3 F2). -/
def srvRestRpM (on : Bool) (E : apply.AEnv GF) (γr : ReadNames) (A₀ : List EntryModel) (r : apply.RestM) :
    IProp GF :=
  if E.lg then iprop(srvRestAt E (appliedTableM on γr A₀) r ∗ srvEver E A₀) else E.RO r

/-- **At an empty raft prefix, before any entry, the mode does not matter** (both tables empty): a
fresh start's `srvRest` is `srvRestM`'s. -/
theorem srvRestM_nil (on : Bool) (E : apply.AEnv GF) (γr : ReadNames) (h : γr.raft.pre = []) :
    srvRestM (GF := GF) on E γr [] = srvRest E γr [] := by
  cases on
  · rfl
  · unfold srvRestM; rw [srvRest_eq_T]; unfold srvRestT appliedTableM appliedTable kvLeasesOn
    simp only [h, List.append_nil, ↓reduceIte]; rfl

/-- A conf change (a non-normal entry) leaves the mode's table (`appliedTable_cc`'s). -/
theorem appliedTableM_cc (on : Bool) (γr : ReadNames) (A : List EntryModel) (m : EntryModel)
    (ht : m.typ ≠ W32 0) : appliedTableM on γr (A ++ [m]) = appliedTableM on γr A := by
  cases on
  · simp only [appliedTableM_false]; exact appliedTable_cc γr A m ht
  · simp only [appliedTableM_true]
    unfold kvLeasesOn
    rw [← List.append_assoc, kvRaftOfOn_snoc]
    unfold kvEntryOn
    rw [if_neg (fun h => ht h.1)]
    unfold kvTable; rw [if_neg ht]

open Iris.ProofMode in
/-- **`srvRestT` as its two parts** (`srvRest_eq_at`'s, at any table). -/
theorem srvRestT_eq_at (E : apply.AEnv GF) (γr : ReadNames) (T : LeaseTable) (A : List EntryModel) :
    srvRestT E γr T A ⊣⊢ srvRestAt E T
      (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A)) ∗ srvEver E A := by
  unfold srvRestT
  cases h : E.lg
  · have hat : srvRestAt E T (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A)) =
        E.RO (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A)) := by
      unfold srvRestAt; rw [h]; rfl
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hat]
    constructor
    · iintro H; iframe H; iapply srvEver_false E A h
    · iintro ⟨H, -⟩; iexact H
  · simp only [↓reduceIte]
    exact .rfl

/-- **`srvRestM` as its two parts** (`srvRest_eq_at` at the mode's table). -/
theorem srvRestM_eq_at (on : Bool) (E : apply.AEnv GF) (γr : ReadNames) (A : List EntryModel) :
    srvRestM on E γr A ⊣⊢ srvRestAt E (appliedTableM on γr A)
      (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A)) ∗ srvEver E A := by
  cases on
  · rw [srvRestM_false, appliedTableM_false, srvRest_eq_T]; exact srvRestT_eq_at E γr _ A
  · exact srvRestT_eq_at E γr _ A

open Iris.ProofMode in
/-- **`srvRestM` opened** (`srvRest_open` at the mode's table). -/
theorem srvRestM_open (on : Bool) (E : apply.AEnv GF) (γr : ReadNames) (A : List EntryModel) :
    srvRestM on E γr A ⊢ ∃ f : w64 → w64, ⌜E.lg = true → leaseTTLsGeReq (appliedTableM on γr A) f⌝ ∗
      E.RO (apply.restLeasesWith f (srvIds E (appliedTableM on γr A).ids)
        (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A))) ∗
      apply.ltHalf E (srvIds E (appliedTableM on γr A).ids) ∗ srvGrantIf E ∗
      srvReqsIf E (appliedTableM on γr A) ∗ srvEver E A := by
  iintro H
  ihave ⟨H, HU⟩ := (srvRestM_eq_at on E γr A).1 $$ H
  ihave ⟨%f, %Hf, H1, H2, H3, H4⟩ := (srvRestAt_open E _ _).1 $$ H
  iexists f
  iframe H1 H2 H3 H4 HU
  ipureintro; exact Hf

open Iris.ProofMode in
/-- **`srvRestM` closed again** (`srvRest_close` at the mode's table). -/
theorem srvRestM_close (on : Bool) (E : apply.AEnv GF) (γr : ReadNames) (A : List EntryModel) :
    (∃ f : w64 → w64, ⌜E.lg = true → leaseTTLsGeReq (appliedTableM on γr A) f⌝ ∗
      E.RO (apply.restLeasesWith f (srvIds E (appliedTableM on γr A).ids)
        (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A))) ∗
      apply.ltHalf E (srvIds E (appliedTableM on γr A).ids) ∗ srvGrantIf E ∗
      srvReqsIf E (appliedTableM on γr A) ∗ srvEver E A) ⊢
      srvRestM on E γr A := by
  iintro ⟨%f, %Hf, H1, H2, H3, H4, HU⟩
  iapply (srvRestM_eq_at on E γr A).2
  iframe HU
  iapply (srvRestAt_open E _ _).2
  iexists f
  iframe H1 H2 H3 H4
  ipureintro; exact Hf

open Iris.ProofMode in
/-- **`srvRestM` one entry later, the table kept** (`srvRest_snoc` at the mode's table). -/
theorem srvRestM_snoc (on : Bool) (E : apply.AEnv GF) (γr : ReadNames) (A : List EntryModel) (m : EntryModel)
    (hT : appliedTableM on γr (A ++ [m]) = appliedTableM on γr A) :
    srvRestAt E (appliedTableM on γr A)
        (restEntry γr.kv.c0 m (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A))) ∗
      srvEver E A ⊢ srvRestM on E γr (A ++ [m]) := by
  iintro ⟨H, HU⟩
  iapply (srvRestM_eq_at on E γr (A ++ [m])).2
  rw [hT, ← List.append_assoc, restModel_append]
  iframe H
  iapply srvEver_snoc $$ HU

/-- **A log whose puts carry no lease attaches no key to a lease** (the keys' leases are live vacuously). -/
theorem leaseItems_of_noLease (l : mvcc.Log) (h : mvcc.LogNoLease l) (k : GoString) (id : w64)
    (hk : mvcc.leaseItemsOf (mvcc.stateAfter l) !! ⟨k⟩ = some id) : False := by
  rw [mvcc.leaseItemsOf_zero _ (mvcc.stateAfter_leaseZero l h)] at hk
  cases hk

end rest

end EtcdGrove
end Perennial
