/- Prefixes retained by appendEntries are shared with previously delivered Ready batches. -/
module
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftpb
public import Proof.go_etcd_io.raft.v3.Protocol.Ghost

@[expose] public section
noncomputable section
namespace Perennial
namespace EtcdGrove
open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- The third index in `r[:n:n]` gives the writer a prefix with no writable slack.
The old Ready can continue reading every run, including the discarded suffix. -/
theorem replayTerms_prefix (r : GoSlice) (runs : List replayTermRun) (n : w64)
    (hn : 0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z r.len) :
    let out := slice.fullSlice r replayTermRun (W64 0) n n
    (r ↦*□ runs : IProp GF) ⊢ out ↦*□ runs.take (sint.nat n) ∗
      ownSliceCap replayTermRun out (DFrac.own 1) := by
  dsimp only
  iintro #Hr
  isplitr
  · icases (ownSlice_slice n n r DFrac.discard runs ⟨hn.1, Int.le_refl _, hn.2⟩).1 $$ Hr with ⟨Hpre, -, -⟩
    rw [ownSlice_unseal]; unfold ownSliceDef
    icases Hpre with (%Hnil | ⟨Harr, -⟩)
    · ileft; ipureintro
      obtain ⟨hp, hlen, _⟩ := (slice_mk_eq_nil ..).mp Hnil.1
      exact ⟨(slice_mk_eq_nil ..).mpr ⟨hp, hlen, hlen⟩, Hnil.2⟩
    · iright; isplitl [Harr]
      · iExactEq Harr; rfl
      · ipureintro; exact Int.le_refl _
  · iapply ownSliceCap_empty _ rfl (by dsimp [slice.fullSlice]; word)

/-- A recorded Raft entry carries the bound on its predecessor term, including the first
bootstrap entry whose predecessor has term zero. -/
theorem replayRecord_prev_le (γ : RaftNames) (e : EntryM) (prev : w64) :
    isEntryR (GF := GF) γ e prev ⊢ ⌜uint.Z prev ≤ uint.Z e.Term'⌝ := by
  iunfold isEntryR
  iintro (⟨%ldr, %γt, %b, %l0, %F0, -, -, -, -, %h, -, -, -⟩ | ⟨%boot, -⟩)
  · ipureintro; exact h.2.1
  · ipureintro
    obtain ⟨_, _, ht, hp⟩ := boot
    rw [hp, ht]; split <;> decide

/-- Two indexed entries of a recorded full log have nondecreasing terms. -/
theorem replayLog_term_le (γ : RaftNames) (es : List EntryM) (i j : Nat)
    (hi : i < es.length) (hj : j < es.length) (hij : i ≤ j) (bound : es.length < 2 ^ 64) :
    logRecs (GF := GF) γ base0 es ⊢ ⌜uint.Z es[i].Term' ≤ uint.Z es[j].Term'⌝ := by
  induction j with
  | zero =>
    have h : i = 0 := by omega
    subst i; iintro _; ipureintro; exact Int.le_refl _
  | succ j ih =>
    by_cases h : i = j + 1
    · subst i; iintro _; ipureintro; exact Int.le_refl _
    have hj' : j < es.length := by omega
    iintro #Hr
    ihave %lower := ih hj' (by omega) $$ Hr
    icases logRecs_lookup γ es (j + 1) es[j + 1] (List.getElem?_eq_getElem hj) (by omega) $$ Hr
      with ⟨%prev, %hprev, #Hentry⟩
    have hread := plogTermAt_lookup base0 es (W64 ((j + 1 : Nat) : Int)) j es[j]
      (List.getElem?_eq_getElem hj') (by rw [base0_index, uint_Z_W64 _ (by omega) (by omega)]; omega)
    rw [hread] at hprev
    cases hprev
    ihave %next := replayRecord_prev_le γ _ _ $$ Hentry
    ipureintro; exact Int.le_trans lower next

/-- Ready and WAL batches that are sublists of the recorded log inherit its term ordering. -/
theorem replayBatch_ordered (γ : RaftNames) (full : List EntryM) (es : List EntryModel)
    (sub : (es.map EntryModel.toM).Sublist full) (bound : full.length < 2 ^ 64) :
    logRecs (GF := GF) γ base0 full ⊢ ⌜es.Pairwise (fun a b => uint.nat a.term ≤ uint.nat b.term)⌝ := by
  have order : logRecs (GF := GF) γ base0 full ⊢
      ⌜full.Pairwise (fun a b => uint.nat a.Term' ≤ uint.nat b.Term')⌝ := by
    rw [List.pairwise_iff_getElem]
    refine (BI.forall_intro fun i => ?_).trans BI.pure_forall.2
    refine (BI.forall_intro fun j => ?_).trans BI.pure_forall.2
    refine (BI.forall_intro fun hi => ?_).trans BI.pure_forall.2
    refine (BI.forall_intro fun hj => ?_).trans BI.pure_forall.2
    refine (BI.forall_intro fun hij => ?_).trans BI.pure_forall.2
    iintro #Hr
    ihave %hle := replayLog_term_le γ full i j hi hj (by omega) bound $$ Hr
    ipureintro; word
  iintro #Hr
  ihave %ordered := order $$ Hr
  ipureintro
  have hbatch := ordered.sublist sub
  exact (List.pairwise_map (f := EntryModel.toM) (R := fun a b => uint.nat a.Term' ≤ uint.nat b.Term')).mp hbatch

/-- The equal-endpoints shortcut in `appendEntries` represents every entry in this batch
by one run when the log terms are nondecreasing. -/
theorem replayBatch_sameTerm (es : List EntryModel) (nonempty : 0 < es.length)
    (ordered : es.Pairwise (fun a b => uint.nat a.term ≤ uint.nat b.term))
    (ends : es[es.length - 1].term = es[0].term) (i : Nat) (hi : i < es.length) :
    es[i].term = es[0].term := by
  have leAt (a b : Nat) (ha : a < es.length) (hb : b < es.length) (hle : a ≤ b) :
      uint.nat es[a].term ≤ uint.nat es[b].term := by
    by_cases h : a = b
    · subst b; exact Nat.le_refl _
    · exact ordered.rel_getElem_of_lt ha hb (by omega)
  have hlo := leAt 0 i nonempty hi (Nat.zero_le _)
  have hhi := leAt i (es.length - 1) hi (by omega) (by omega)
  rw [ends] at hhi
  exact uint_nat_inj _ _ (Nat.le_antisymm hhi hlo)

/-- In the mixed-term branch the last entry is a sentinel. As long as the entries already
examined have the first term, the next indexed read is in bounds. -/
theorem replayBatch_scan_lt (es : List EntryModel) (nonempty : 0 < es.length)
    (term : w64) (different : es[es.length - 1].term ≠ term) (count : Nat)
    (scanned : ∀ (i : Nat) (hi : i < es.length), i < count → es[i].term = term) :
    count < es.length := by
  by_cases h : count < es.length
  · exact h
  exact False.elim (different (scanned (es.length - 1) (by omega) (by omega)))

/-- A Ready with no new entries returns exactly the existing slice, for any receiver. -/
theorem replayTerms.appendEntries_empty (r ents : GoSlice) (hempty : ents.len = W64 0) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver }}
      (App (Val (r @!! replayTerms.ty @!! go!"appendEntries")) (Val #ents))
    {{ RET #r; True }} := by
  wp_start
  (try wp_auto)
  simp only [hempty, decide_true]
  (try wp_auto)
  iapply HΦ; itrivial

end EtcdGrove
end Perennial
