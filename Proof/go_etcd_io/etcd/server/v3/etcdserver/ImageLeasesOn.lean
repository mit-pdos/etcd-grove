/-
**The auth-on lease table along the committed log** (auth-lease S3a, Draft rev 5 §5: the snapshot
path carries the leases). Lean-first (no Rocq counterpart).

The mode-`on` model's table (`kvLeasesOn`, `appliedTableM true`) steps as the off table does
(`kvTable`) or not at all (an admin entry above `c₀`, a request the auth layer refuses), so the off
table's facts along a prefix (`ImageLeases.lean`: `kvTableOf_mem`, `kvTableOf_nodup`,
`kvTableOf_mono`) hold of it, and with them the two mode facts a snapshot's `Recover` takes
(`appliedTableM_mono_mem`, `appliedTableM_rev_mem`), at either auth mode.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ImageLeases
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVModelM

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section table
variable [GooseExts]

/-- **The mode-`on` table step**: unchanged, or the off table's step. -/
theorem kvEntryOn_table_eq_or (c0 : w64) (ch : apply.Chain) (s : OnState) (m : EntryModel) :
    (kvEntryOn c0 ch s m).2.2 = s.2.2 ∨ (kvEntryOn c0 ch s m).2.2 = kvTable c0 ch s.2.2 m := by
  unfold kvEntryOn
  split
  · split
    · split
      · left; rfl
      · split
        · left; rfl
        · split
          · left; rfl
          · right; rfl
    · left; rfl
  · right; rfl

/-- **A lease of the mode-`on` table after `B` was in the table before, or granted in `B`.** -/
theorem kvRaftOfOn_table_mem (c0 : w64) (ch : apply.Chain) :
    ∀ (B : List EntryModel) (s : OnState) (q : w64 × w64), q ∈ (kvRaftOfOn c0 ch s B).2.2 →
      q ∈ s.2.2 ∨ q.1 ∈ srvGrantLog B := by
  intro B
  induction B with
  | nil => intro s q h; left; exact h
  | cons m B ih =>
    intro s q h
    have hsub : ∀ u, u ∈ srvGrantLog B → u ∈ srvGrantLog (m :: B) := fun u hu => by
      obtain ⟨e, he, hd, hg⟩ := (mem_srvGrantLog B u).1 hu
      exact (mem_srvGrantLog _ u).2 ⟨e, List.mem_cons_of_mem _ he, hd, hg⟩
    rcases ih (kvEntryOn c0 ch s m) q h with h1 | h1
    · rcases kvEntryOn_table_eq_or c0 ch s m with he | he
      · rw [he] at h1; left; exact h1
      · rw [he] at h1
        rcases kvTableOf_mem c0 ch [m] s.2.2 q h1 with h2 | h2
        · left; exact h2
        · right
          obtain ⟨e, he', hd, hg⟩ := (mem_srvGrantLog _ _).1 h2
          rw [List.mem_singleton] at he'; subst he'
          exact (mem_srvGrantLog _ _).2 ⟨e, List.mem_cons_self, hd, hg⟩
    · right; exact hsub _ h1

/-- **The mode-`on` table's ids stay distinct.** -/
theorem kvRaftOfOn_table_nodup (c0 : w64) (ch : apply.Chain) :
    ∀ (B : List EntryModel) (s : OnState), s.2.2.ids.Nodup → (kvRaftOfOn c0 ch s B).2.2.ids.Nodup := by
  intro B
  induction B with
  | nil => intro s h; exact h
  | cons m B ih =>
    intro s h
    apply ih
    rcases kvEntryOn_table_eq_or c0 ch s m with he | he
    · rw [he]; exact h
    · rw [he]; exact kvTableOf_nodup c0 ch [m] s.2.2 h

/-- **In the monotone mode no lease leaves the mode-`on` table** (no revocation is admitted). -/
theorem kvRaftOfOn_table_mono (c0 : w64) (ch : apply.Chain) :
    ∀ (B : List EntryModel) (s : OnState), plainLogOn .mono B →
      ∀ p ∈ s.2.2, p ∈ (kvRaftOfOn c0 ch s B).2.2 := by
  intro B
  induction B with
  | nil => intro s _ p h; exact h
  | cons m B ih =>
    intro s hpl p hp
    apply ih _ (fun e he => hpl e (List.mem_cons_of_mem _ he))
    rcases kvEntryOn_table_eq_or c0 ch s m with he | he
    · rw [he]; exact hp
    · rw [he]
      rcases kvTable_eq_or c0 ch s.2.2 m with he' | ⟨rq, ht, hd, hdec, he'⟩
      · rw [he']; exact hp
      · rw [he']
        rcases backendTable_cases rq s.2.2 with hb | ⟨g, -, -, -, hb⟩ | ⟨id, hk, hb⟩
        · rw [hb]; exact hp
        · rw [hb]; exact List.mem_append_left _ hp
        · exfalso
          rcases hpl m List.mem_cons_self ht hd rq hdec with ((⟨h1, -⟩ | h | h) | h)
          · have := (plainReqL_facts _ rq h1).2.2; rw [hk] at this; simp [putgetKind] at this
          · rw [h.2.1] at hk; cases hk
          · cases h.1
          · have := h.1; unfold apply.adminKindOk at this; rw [hk] at this; exact this

/-- `appliedTableM` across a suffix: the off table's fold, or the mode-`on` model's from the
prefix's state. -/
theorem appliedTableM_true_append (γr : ReadNames) (A B : List EntryModel) :
    appliedTableM true γr (A ++ B) =
      (kvRaftOfOn γr.kv.c0 γr.kv.ch0
        (kvRaftOfOn γr.kv.c0 γr.kv.ch0 (srvAuthSt0, γr.kv.log0, []) (γr.raft.pre ++ A)) B).2.2 := by
  rw [appliedTableM_true]; unfold kvLeasesOn
  rw [← List.append_assoc, kvRaftOfOn_append]

theorem appliedTableM_nodup (on : Bool) (γr : ReadNames) (A : List EntryModel) :
    (appliedTableM on γr A).ids.Nodup := by
  cases on
  · rw [appliedTableM_false]; exact appliedTable_nodup γr A
  · rw [appliedTableM_true]; unfold kvLeasesOn
    exact kvRaftOfOn_table_nodup _ _ _ _ List.nodup_nil

/-- **A lease of the snapshot's table (either mode) is granted in its log** (an empty prefix). -/
theorem appliedTableM_ids_granted (on : Bool) (γr : ReadNames) (hpre : γr.raft.pre = [])
    (A' : List EntryModel) (u : w64) (hu : u ∈ (appliedTableM on γr A').ids) : u ∈ srvGrantLog A' := by
  cases on
  · rw [appliedTableM_false] at hu; exact appliedTable_ids_granted γr hpre A' u hu
  · rw [appliedTableM_true, hpre, List.nil_append] at hu
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hu
    rcases kvRaftOfOn_table_mem _ _ A' _ q hq with h | h
    · cases h
    · exact h

/-- **The monotone mode, at either auth mode**: the mode's plain log (`plainLogM` off, `plainLogOn`
on) keeps every lease of the applied table in the snapshot's. -/
theorem appliedTableM_mono_mem (on : Bool) (γr : ReadNames) {A A' : List EntryModel}
    (hpre : A <+: A')
    (hpl : if on then plainLogOn .mono A' else plainLogM γr.kv.cmp .mono A') :
    ∀ p ∈ appliedTableM on γr A, p ∈ appliedTableM on γr A' := by
  cases on
  · simp only [appliedTableM_false]
    exact appliedTable_mono_mem γr hpre (by simpa using hpl)
  · obtain ⟨B, rfl⟩ := hpre
    have hpl' : plainLogOn .mono (A ++ B) := by simpa using hpl
    intro p hp
    rw [appliedTableM_true_append]
    rw [appliedTableM_true] at hp
    exact kvRaftOfOn_table_mono _ _ B _ (fun e he => hpl' e (List.mem_append_right _ he)) p hp

theorem appliedTableM_mono_sub (on : Bool) (γr : ReadNames) {A A' : List EntryModel}
    (hpre : A <+: A')
    (hpl : if on then plainLogOn .mono A' else plainLogM γr.kv.cmp .mono A') :
    ∀ id ∈ (appliedTableM on γr A).ids, id ∈ (appliedTableM on γr A').ids := by
  intro id h
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h
  exact List.mem_map.2 ⟨p, appliedTableM_mono_mem on γr hpre hpl p hp, rfl⟩

/-- **The revocable mode, at either auth mode** (`appliedTable_rev_mem`'s). -/
theorem appliedTableM_rev_mem (on : Bool) (γr : ReadNames) {A A' : List EntryModel}
    (hpre : A <+: A') (hnd : (srvGrantLog A').Nodup) (q : w64 × w64)
    (hu : q.1 ∈ srvGrantLog A) (hq : q ∈ appliedTableM on γr A') : q ∈ appliedTableM on γr A := by
  cases on
  · simp only [appliedTableM_false] at hq ⊢; exact appliedTable_rev_mem γr hpre hnd q hu hq
  · obtain ⟨B, rfl⟩ := hpre
    rw [appliedTableM_true_append] at hq
    rcases kvRaftOfOn_table_mem _ _ B _ q hq with h | h
    · rw [appliedTableM_true]; exact h
    · exfalso
      have he : srvGrantLog (A ++ B) = srvGrantLog A ++ srvGrantLog B := by
        unfold srvGrantLog logRevGrantIds; rw [List.filter_append, List.filterMap_append]
      rw [he] at hnd
      exact (List.nodup_append.1 hnd).2.2 _ hu _ h rfl

theorem appliedTableM_granted_live (on : Bool) (γr : ReadNames) {A A' : List EntryModel}
    (hpre : A <+: A') (hnd : (srvGrantLog A').Nodup) (u : w64)
    (hu : u ∈ srvGrantLog A) (hu' : u ∈ (appliedTableM on γr A').ids) :
    u ∈ (appliedTableM on γr A).ids := by
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hu'
  exact List.mem_map.2 ⟨q, appliedTableM_rev_mem on γr hpre hnd q hu hq, rfl⟩

end table

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

open Iris.ProofMode in
/-- **The applied log's grant ids have no repeat**, auth on (`kv_grantLog_nodup`'s, from `kvInvOn`'s
`kvGrantIds`). -/
theorem kv_grantLog_nodup_on (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState)
    (A : List EntryModel) :
    ⊢ kvInvOn (GF := GF) γ γk st₀ -∗ srvRaftLogInv γ -∗ srvRLogLb γ A ={⊤}=∗
      ⌜γk.lm = .revocable → (srvGrantLog A).Nodup⌝ := by
  iintro #Hinv #Hr #HB
  iunfold kvInvOn at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%L, HL, Hσ, Hh, %Hok, #Hw, HG⟩
  imod srvRLog_lb γ (⊤ \ ↑kvN) (mask_ndot_ne' nroot "raft_commit" "server_kv" (by decide))
    L A $$ Hr HL HB with ⟨HL, %Hp⟩
  iunfold kvGrantIds at HG
  icases HG with ⟨%U, %HU, HUs⟩
  imod Hclose $$ [HL Hσ Hh HUs] with -
  · inext; iexists L; iframe HL Hσ Hh Hw
    isplitr
    · ipureintro; exact Hok
    iunfold kvGrantIds; iexists U; iframe HUs; ipureintro; exact HU
  imodintro
  ipureintro
  intro hlm
  have hnd : (logRevGrantIds γk.lm L).Nodup := by
    exact kvGrantIds_nodup_of HU
  have h1 := Hp.2.2.filterMap (leRevGrantId γk.lm)
  rw [filterMap_leRevGrantId_opsOf, ← logRevGrantIds_noFill γk.lm L Hp.2.1] at h1
  have hn := hnd.sublist h1.sublist
  rw [← logRevGrantIds_filter_data, hlm] at hn
  exact hn

end lemmas

end EtcdGrove
end Perennial
