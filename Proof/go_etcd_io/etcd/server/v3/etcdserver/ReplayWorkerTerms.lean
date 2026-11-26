/- Preserve the concrete historical term delivered with the apply job. -/
module
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReplayJob
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

end EtcdGrove
end Perennial
