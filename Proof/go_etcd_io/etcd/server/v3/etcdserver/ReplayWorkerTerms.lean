/- Preserve the concrete historical term delivered with the apply job. -/
module
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReplayCoverage
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.replayTerms__after

@[expose] public section
noncomputable section
namespace Perennial
namespace EtcdGrove
open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem rnReplayState.advance (γ : RNNames GF) (view : GoSlice) (a b : Nat) (hab : a ≤ b) :
    rnReplayState γ view a ⊢ rnReplayState γ view b := by
  unfold rnReplayState
  iintro ⟨%runs, #Hr, %hp⟩
  iexists runs; iframe Hr
  ipureintro; exact replayPending_mono hp hab

theorem rnReplayState.empty (γ : RNNames GF) (n : Nat) (hn : γ.a0.length ≤ n) :
    ⊢ rnReplayState γ slice.nil n := by
  unfold rnReplayState
  iexists ([] : List replayTermRun)
  ihave #Hnil := ownSlice_nil (GF := GF) (V := replayTermRun) DFrac.discard
  iframe Hnil
  ipureintro
  exact ⟨by simp [replayLayout], fun _ h => False.elim (Nat.not_lt_of_ge hn h)⟩

theorem rnReplayState.job (γ : RNNames GF) (view : GoSlice) (rt : w64) (n : Nat) :
    rnReplayState γ view n ⊢ rnReplayJob γ view rt n := by
  unfold rnReplayState rnReplayJob
  iintro ⟨%runs, #Hr, %hp⟩ !> %sm %ci %hc _ %ml _
  obtain ⟨r, hr, ht⟩ := hp.2 ci hc.2.2.1 hc.2.2.2
  obtain ⟨cov, found⟩ := replay_lookup_interval _ _ _ _ hp.1 hr ht
  imodintro
  iexists runs, r
  iframe Hr
  ipureintro; exact ⟨cov, found, ht.2.2⟩

theorem rnReplayState.appendEntries (γ : RNNames GF) (view ents : GoSlice) (n : Nat)
    (ls : List Loc) (es : List EntryModel)
    (order : es.Pairwise (fun a b => uint.nat a.term ≤ uint.nat b.term ∧ uint.nat a.index < uint.nat b.index))
    (above : ∀ first, es.head? = some first → n < γ.a0.length → γ.a0.length < uint.nat first.index)
    (getIndex : raftpb.Entry.GetIndex.spec (GF := GF) (hG := hG))
    (getTerm : raftpb.Entry.GetTerm.spec (GF := GF) (hG := hG)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
       rnReplayState γ view n ∗ ents ↦*□ ls ∗ entriesAt ls es }}
      (App (Val (view @!! replayTerms.ty @!! go!"appendEntries")) (Val #ents))
    {{ (out : GoSlice), RET #out; rnReplayState γ out n }} := by
  iintro %Φ ⟨#Hpkg, #Hstate, #Hsl, #Hrows⟩ HΦ
  cases es with
  | nil =>
    ihave %hlen : ⌜ls.length = 0⌝ $$ []
    · iunfold entriesAt at Hrows; icases Hrows with ⟨%h, -⟩; ipureintro; exact h
    ihave %hslen := ownSlice_len ents _ ls $$ Hsl
    wp_apply replayTerms.appendEntries_empty view ents (by word) $$ [$Hpkg]
    iapply HΦ; iexact Hstate
  | cons first rest =>
    iunfold rnReplayState at Hstate
    icases Hstate with ⟨%runs, #Hr, %hp⟩
    wp_apply replayTerms.appendEntries_nonempty view ents runs ls first rest (order.imp fun h => h.1)
      getIndex getTerm $$ [$Hpkg $Hr $Hsl $Hrows] as %out ⟨%k, %hcut, #Hout⟩
    obtain ⟨layout, bound, keep⟩ := replayRetain_coverage runs k first.index hp.1 hcut
    have idx := order.imp fun h => h.2
    obtain ⟨done, prior, _⟩ := replayFold_coverage _ (first :: rest) layout idx (by
      intro r hr e he
      have h := bound r hr
      rcases List.mem_cons.mp he with rfl | he
      · exact h
      · exact Nat.lt_trans h ((List.pairwise_cons.mp idx).1 e he))
    iapply HΦ
    iunfold rnReplayState
    iexists _
    iframe Hout
    ipureintro
    refine ⟨done, fun ci hn hci => prior _ _ (keep _ _ ?_ (hp.2 ci hn hci))⟩
    have h := above first rfl hn
    have := uint_nat_eq ci
    omega

/-- Advancing the cursor keeps the backend form (`after` drops only runs ending at or below it). -/
theorem replayPending_after (runs : List replayTermRun) (A : List EntryModel) (n : Nat) (idx : w64)
    (hn : n ≤ uint.nat idx) (hp : replayPending runs A n) :
    replayPending (runs.dropWhile (fun r => decide (uint.nat r.last' ≤ uint.nat idx))) A (uint.nat idx) := by
  refine ⟨replayLayout_sublist hp.1 (List.dropWhile_sublist _), ?_⟩
  intro ci h hci
  obtain ⟨r, hr, hc⟩ := hp.2 ci (by omega) hci
  refine ⟨r, ?_, hc⟩
  have hlarge : ¬uint.nat r.last' ≤ uint.nat idx := by
    have := hc.2.1; have := uint_nat_eq ci; omega
  clear hp
  induction runs with
  | nil => cases hr
  | cons x xs ih =>
    by_cases gone : uint.nat x.last' ≤ uint.nat idx
    · have hne : r ≠ x := by rintro rfl; exact hlarge gone
      simp only [List.dropWhile, gone, decide_true]
      exact ih ((List.mem_cons.mp hr).resolve_left hne)
    · simpa [List.dropWhile, gone] using hr

theorem rnReplayState.after (γ : RNNames GF) (view : GoSlice) (n : Nat) (idx : w64)
    (hn : n ≤ uint.nat idx) (after : replayTerms.after.spec (GF := GF) (hG := hG)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ rnReplayState γ view n }}
      (App (Val (view @!! replayTerms.ty @!! go!"after")) (Val #idx))
    {{ (out : GoSlice), RET #out; rnReplayState γ out (uint.nat idx) }} := by
  iintro %Φ ⟨#Hpkg, #Hs⟩ HΦ
  iunfold rnReplayState at Hs
  icases Hs with ⟨%runs, #Hr, %hp⟩
  wp_apply after view runs idx $$ [$Hpkg $Hr] as %out #Hout
  iapply HΦ
  iunfold rnReplayState
  iexists _
  iframe Hout
  ipureintro
  exact replayPending_after runs γ.a0 n idx hn hp

/-! ### (T10 step 3 (B), B2) The replay state over the durable state

`rnReplayHist γ view S n`: the loop's replay view describes the node's durable state `S` above the
apply cursor `n` (`replayHistoryMatches`), beside the backend form `rnReplayState` keeps
(`replayPending`, which `rnReplayState.job` reads until B4 builds the job from the history). Its
lemmas follow `rnReplayState`'s, each with the history premise its step needs (`ReplayCoverage`'s
`replayHistoryMatches_append`/`_same`, `ReplayHistory`'s `_after`); `.describe` is what B3's
payload (`∃ S, replayRunsDescribe runs S n ∧ S.term = rt`) takes. -/

def rnReplayHist (γ : RNNames GF) (view : GoSlice) (S : RaftState) (n : Nat) : IProp GF :=
  iprop(∃ runs : List replayTermRun, view ↦*□ runs ∗
    ⌜replayPending runs γ.a0 n ∧ replayHistoryMatches runs S n⌝)

instance rnReplayHist_persistent (γ : RNNames GF) (view : GoSlice) (S : RaftState) (n : Nat) :
    Persistent (rnReplayHist (GF := GF) γ view S n) := by
  unfold rnReplayHist; infer_instance

theorem rnReplayHist.state (γ : RNNames GF) (view : GoSlice) (S : RaftState) (n : Nat) :
    rnReplayHist γ view S n ⊢ rnReplayState γ view n := by
  unfold rnReplayHist rnReplayState
  iintro ⟨%runs, #Hr, %hp⟩
  iexists runs; iframe Hr
  ipureintro; exact hp.1

theorem rnReplayHist.describe (γ : RNNames GF) (view : GoSlice) (S : RaftState) (n : Nat) :
    rnReplayHist γ view S n ⊢ ∃ runs, view ↦*□ runs ∗ ⌜replayRunsDescribe runs S n⌝ := by
  unfold rnReplayHist
  iintro ⟨%runs, #Hr, %hp⟩
  iexists runs; iframe Hr
  ipureintro; exact replayHistoryMatches_describe runs S n hp.2

/-- The seed: the backend form and the history form of the same runs. -/
theorem rnReplayHist.intro (γ : RNNames GF) (view : GoSlice) (S : RaftState) (n : Nat)
    (runs : List replayTermRun) (hp : replayPending runs γ.a0 n) (hh : replayHistoryMatches runs S n) :
    view ↦*□ runs ⊢ rnReplayHist γ view S n := by
  unfold rnReplayHist
  iintro #Hr
  iexists runs; iframe Hr
  ipureintro; exact ⟨hp, hh⟩

/-- An unchanged log (`replayHistoryMatches_same`): the cursor moves up, `S` to a state with the
same log. -/
theorem rnReplayHist.advance (γ : RNNames GF) (view : GoSlice) (S S' : RaftState) (a b : Nat)
    (hab : a ≤ b) (hb : S'.base = S.base) (he : S'.ents = S.ents) :
    rnReplayHist γ view S a ⊢ rnReplayHist γ view S' b := by
  unfold rnReplayHist
  iintro ⟨%runs, #Hr, %hp⟩
  iexists runs; iframe Hr
  ipureintro; exact ⟨replayPending_mono hp.1 hab, replayHistoryMatches_same runs S S' a b hp.2 hb he hab⟩

/-- The empty view, at a state with no term above the cursor. -/
theorem rnReplayHist.empty (γ : RNNames GF) (S : RaftState) (n : Nat) (hn : γ.a0.length ≤ n)
    (hS : ∀ ci t, n < uint.nat ci → plogTermAt S.base S.ents ci = some t → False) :
    ⊢ rnReplayHist γ slice.nil S n := by
  unfold rnReplayHist
  iexists ([] : List replayTermRun)
  ihave #Hnil := ownSlice_nil (GF := GF) (V := replayTermRun) DFrac.discard
  iframe Hnil
  ipureintro
  exact ⟨⟨by simp [replayLayout], fun _ h => False.elim (Nat.not_lt_of_ge hn h)⟩,
    ⟨by simp [replayLayout], fun ci t h ht => False.elim (hS ci t h ht)⟩⟩

/-- A Ready's entries `es`, from the durable state `S` to `S'`: `S'` keeps `S`'s terms below the
batch (all of them above `n` when the batch is empty) and has the batch's from its first index on
(`plogTermAt_next_batch` gives both at `S.next`). -/
theorem rnReplayHist.appendEntries (γ : RNNames GF) (view ents : GoSlice) (S S' : RaftState) (n : Nat)
    (ls : List Loc) (es : List EntryModel)
    (order : es.Pairwise (fun a b => uint.nat a.term ≤ uint.nat b.term ∧ uint.nat a.index < uint.nat b.index))
    (above : ∀ first, es.head? = some first → n < γ.a0.length → γ.a0.length < uint.nat first.index)
    (below : ∀ ci t, n < uint.nat ci → (∀ first, es.head? = some first → uint.nat ci < uint.nat first.index) →
      plogTermAt S'.base S'.ents ci = some t → plogTermAt S.base S.ents ci = some t)
    (here : ∀ first, es.head? = some first → ∀ ci t, n < uint.nat ci → uint.nat first.index ≤ uint.nat ci →
      plogTermAt S'.base S'.ents ci = some t → ∃ e ∈ es, e.index = ci ∧ e.term = t)
    (getIndex : raftpb.Entry.GetIndex.spec (GF := GF) (hG := hG))
    (getTerm : raftpb.Entry.GetTerm.spec (GF := GF) (hG := hG)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
       rnReplayHist γ view S n ∗ ents ↦*□ ls ∗ entriesAt ls es }}
      (App (Val (view @!! replayTerms.ty @!! go!"appendEntries")) (Val #ents))
    {{ (out : GoSlice), RET #out; rnReplayHist γ out S' n }} := by
  iintro %Φ ⟨#Hpkg, #Hstate, #Hsl, #Hrows⟩ HΦ
  cases es with
  | nil =>
    ihave %hlen : ⌜ls.length = 0⌝ $$ []
    · iunfold entriesAt at Hrows; icases Hrows with ⟨%h, -⟩; ipureintro; exact h
    ihave %hslen := ownSlice_len ents _ ls $$ Hsl
    wp_apply replayTerms.appendEntries_empty view ents (by word) $$ [$Hpkg]
    iapply HΦ
    iunfold rnReplayHist at Hstate
    icases Hstate with ⟨%runs, #Hr, %hp⟩
    iunfold rnReplayHist
    iexists runs; iframe Hr
    ipureintro
    refine ⟨hp.1, hp.2.1, fun ci t hn ht => hp.2.2 ci t hn (below ci t hn (by simp) ht)⟩
  | cons first rest =>
    iunfold rnReplayHist at Hstate
    icases Hstate with ⟨%runs, #Hr, %hp⟩
    wp_apply replayTerms.appendEntries_nonempty view ents runs ls first rest (order.imp fun h => h.1)
      getIndex getTerm $$ [$Hpkg $Hr $Hsl $Hrows] as %out ⟨%k, %hcut, #Hout⟩
    have hp1 := hp.1
    obtain ⟨layout, bound, keep⟩ := replayRetain_coverage runs k first.index hp1.1 hcut
    have idx := order.imp fun h => h.2
    obtain ⟨done, prior, _⟩ := replayFold_coverage _ (first :: rest) layout idx (by
      intro r hr e he
      have h := bound r hr
      rcases List.mem_cons.mp he with rfl | he
      · exact h
      · exact Nat.lt_trans h ((List.pairwise_cons.mp idx).1 e he))
    have hh := replayHistoryMatches_append runs S S' n k first rest idx hp.2 hcut
      (fun ci t hn hlt ht => below ci t hn (by intro f hf; cases hf; exact hlt) ht)
      (here first rfl)
    iapply HΦ
    iunfold rnReplayHist
    iexists _
    iframe Hout
    ipureintro
    refine ⟨⟨done, fun ci hn hci => prior _ _ (keep _ _ ?_ (hp1.2 ci hn hci))⟩, hh⟩
    have h := above first rfl hn
    have := uint_nat_eq ci
    omega

theorem rnReplayHist.after (γ : RNNames GF) (view : GoSlice) (S : RaftState) (n : Nat) (idx : w64)
    (hn : n ≤ uint.nat idx) (after : replayTerms.after.spec (GF := GF) (hG := hG)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ rnReplayHist γ view S n }}
      (App (Val (view @!! replayTerms.ty @!! go!"after")) (Val #idx))
    {{ (out : GoSlice), RET #out; rnReplayHist γ out S (uint.nat idx) }} := by
  iintro %Φ ⟨#Hpkg, #Hs⟩ HΦ
  iunfold rnReplayHist at Hs
  icases Hs with ⟨%runs, #Hr, %hp⟩
  wp_apply after view runs idx $$ [$Hpkg $Hr] as %out #Hout
  iapply HΦ
  iunfold rnReplayHist
  iexists _
  iframe Hout
  ipureintro
  exact ⟨replayPending_after runs γ.a0 n idx hn hp.1, replayHistoryMatches_after runs S n idx hn hp.2⟩

end EtcdGrove
end Perennial
