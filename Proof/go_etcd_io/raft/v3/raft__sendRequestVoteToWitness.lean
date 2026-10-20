/-
Proof of `Spec/go_etcd_io/raft/v3/raft__sendRequestVoteToWitness.lean`.
-/
module

public import Spec.go_etcd_io.raft.v3.raft__sendRequestVoteToWitness
public import Spec.go_etcd_io.raft.v3.raftLog__lastEntryID
public import Spec.go_etcd_io.raft.v3.raftLog__subterm

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

omit ffi [FfiInterp ffi] [FfiSemantics ext ffi] [GoGlobalContext] in
/-- The entry at the last index of a well-formed log, past its boundary, is its last: its subterm
is `plogLastSub`. -/
theorem entry_last_sub (b : entryID) (es : List EntryM) (i : w64) (e : EntryM)
    (Hwf : PlogWf b es) (Hi : i = (plogLast b es).index') (Hlt : uint.Z b.index' < uint.Z i)
    (He : es[(uint.Z i - uint.Z b.index' - 1).toNat]? = some e) :
    e.Subterm' = plogLastSub es := by
  have Hli := plogLast_index b es Hwf
  rw [← Hi] at Hli
  unfold plogLastIndexZ at Hli
  unfold plogLastSub
  have Hne : es ≠ [] := by
    intro h; subst h; simp at Hli; omega
  obtain ⟨x, Hx⟩ := List.getLast?_isSome.mpr Hne |> Option.isSome_iff_exists.mp
  rw [Hx]
  have Hk := getLast?_some_getElem? es x Hx
  rw [show (uint.Z i - uint.Z b.index' - 1).toNat = es.length - 1 by omega] at He
  rw [Hk] at He
  cases He; rfl

set_option hygiene false in
/-- The rest once the subterm `v` is known (`subterm ↦ v`, `HlsV` its fact): copy the tally, queue
the request, log. -/
local macro "svw_tail " v:term : tactic => `(tactic| (
  -- `votes := r.trk.Votes`, copied into a fresh map `v`
  icases ownRaftPhysC_tracker c r id s $$ Hphys with ⟨%tv, Hf, Htrk, Hback⟩
  wp_auto
  iNamed Htrk
  have Hfr := (ownMap_fractional (GF := GF) tv.Votes' s.votes).fractional (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at Hfr
  icases Hfr.1 $$ Hvotes with ⟨Hvotes1, Hvotes2⟩
  wp_apply (wp_map_make1 (K := w64) (V := Bool)) as %vm Hvm
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (keys : List w64) (i : Int) => iprop(∃ (x : w64)
      (mv : GMap w64 Bool),
      "%Hi" ∷ ⌜0 ≤ i⌝ ∗
      "%Hmv" ∷ ⌜∀ k, mv !! k = if k ∈ keys.take i.toNat then s.votes !! k else none⌝ ∗
      "id" ∷ id_ptr ↦ x ∗ "v" ∷ v_ptr ↦ vm ∗ "votes" ∷ votes_ptr ↦ tv.Votes' ∗
      "Hvm" ∷ vm ↦$ mv ∗ "Hvotes2" ∷ tv.Votes' ↦${DFrac.own (Qp.half 1)} s.votes)) $$ Hvotes1
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [id v votes Hvm Hvotes2]
  · iexists _, ∅
    simp only [named]
    iframe
    ipureintro
    refine ⟨Int.le_refl _, fun k => ?_⟩
    simp
  isplitr
  · imodintro
    iintro %i %key %vv ⟨%Hkey, %Hvv⟩ HP
    iNamed HP
    wp_auto
    wp_apply (wp_map_lookup1 go.uint64 go.bool tv.Votes' s.votes key) $$ Hvotes2 as Hvotes2
    wp_apply wp_mapInsert $$ Hvm as Hvm
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists key, _
    simp only [named]
    iframe
    ipureintro
    refine ⟨by omega, fun k => ?_⟩
    have Htake : keys.take (i + 1).toNat = keys.take i.toNat ++ [key] := by
      rw [show (i + 1).toNat = i.toNat + 1 by omega]
      rw [List.take_add_one, Hkey]; rfl
    rw [Htake, GMap.lookup_insert_eq_iff]
    by_cases hk : key = k
    · subst hk; simp [Hvv]
    · simp only [hk, ↓reduceIte]; rw [Hmv]
      simp [List.mem_append, Ne.symm hk]
  iintro HP Hvotes1
  iNamed HP
  rw [Int.toNat_natCast, ← Hklen, List.take_length] at Hmv
  have Hmv' : mv = s.votes := by
    apply GMap.map_eq; intro k
    rw [Hmv k]
    by_cases hk : k ∈ keys
    · simp only [hk, ↓reduceIte]
    · simp only [hk, ↓reduceIte]
      have := mt (Hkset k).mpr hk
      cases h : s.votes !! k <;> simp_all
  subst Hmv'
  ihave Hvotes := Hfr.2 $$ [Hvotes1 Hvotes2]
  · iframe
  ihave Htrk : ownTrackerC c tv ⟨s.votes, s.progress, s.prvals, s.ep⟩ $$ [Hvotes Hprogs Hcfg]
  · unfold ownTrackerC; simp only [named]; iframe
    iframe Hprs Hepoch
    ipureintro; exact ⟨Hinv, Hdom, Hflags, Hsize, HmaxInfl, Hnw⟩
  ihave Hphys := Hback $$ %tv %s.votes Hf Htrk
  imod ownMap_persist $$ Hvm with #Hvm
  icases ownRaftPhysC_shared (c := c) (V := V) r id _ $$ Hphys with ⟨%lok, #Hfid, -, -, Hphys⟩
  icases ownRaftPhysC_witQ c r id _ $$ Hphys with ⟨%wsl, %μs, HT, Hwf, Hq, Hreseal⟩
  wp_auto
  iunfold ownWQueue at Hq
  icases Hq with ⟨%wms, Hsl, Hcap, Hbig⟩
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %m_sl ⟨m_sl, -⟩
  try wp_auto
  wp_apply wp_slice_append $$ [Hsl Hcap m_sl] as %wsl' ⟨Hsl, Hcap, -⟩
  · iframe
  wp_auto
  ihave #Hnil : (slice.nil ↦*□ ([] : List w64) : IProp GF) $$ []
  · iapply ownSlice_nil
  ihave #Hnilc : (slice.nil ↦*□ ([] : List w8) : IProp GF) $$ []
  · iapply ownSlice_nil
  ihave Hq' : ownWQueue wsl' (μs ++ [wVoteM id wid vt term s.logst.prev
      (s.logst.sents ++ s.logst.uents) $v s.votes]) $$ [Hsl Hcap Hbig]
  · iunfold ownWQueue
    iexists _
    iframe Hsl Hcap
    iapply BigSepL2.bigSepL2_snoc.2
    iframe Hbig
    iunfold ownWMsg
    iexists slice.nil, slice.nil
    simp only [wVoteM]
    iframe Hnil Hnilc
    isplitr
    · ipureintro
      subst Hlast
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | trivial | rfl
    iright; iexact Hvm
  ihave Hphys := Hreseal $$ %wsl' %_ %Hw HT Hwf Hq'
  try wp_auto
  wp_raft_logC
  iapply HΦ
  iframe Hphys
  ipureintro; exact HlsV))

theorem raft.sendRequestVoteToWitness.wp_proof
    (wp_raftLog_lastEntryID : raftLog.lastEntryID.spec (GF := GF) (hG := hG))
    (wp_raftLog_subterm : raftLog.subterm.spec (GF := GF) (hG := hG)) :
    raft.sendRequestVoteToWitness.spec (GF := GF) (hG := hG) := by
  intro c V r id s wid vt term Hw
  wp_start as Hphys
  wp_auto
  wp_apply raft.wp_load_raftLogC (c := c) (V := V) r id s $$ Hphys as Hphys
  icases ownRaftPhysC_log_same (c := c) (V := V) r id s $$ Hphys with ⟨Hlog, Hback⟩
  wp_apply wp_raftLog_lastEntryID s.log s.logst $$ [$Hlog] as %last ⟨Hlog, %Hlast⟩
  ihave Hphys := Hback $$ Hlog
  try wp_auto
  wp_apply raft.wp_load_raftLogC (c := c) (V := V) r id s $$ Hphys as Hphys
  icases ownRaftPhysC_log_same (c := c) (V := V) r id s $$ Hphys with ⟨Hlog, Hback⟩
  wp_apply wp_raftLog_subterm s.log s.logst _ $$ [$Hlog] as %t0 %st %ok ⟨Hlog, %Hok1⟩
  icases ownRaftLog_wf _ _ $$ Hlog with ⟨%Hwf, Hlog⟩
  ihave Hphys := Hback $$ Hlog
  try wp_auto
  -- `if !ok { subterm = 0 }`: the subterm reported, the last entry's or `0`
  have Hls : ∀ ls, (ls = W64 0 ∨ ls = st ∧ ok = true) →
      ls = W64 0 ∨ ls = plogLastSub (s.logst.sents ++ s.logst.uents) := by
    rintro ls (h | ⟨rfl, hok⟩)
    · exact Or.inl h
    · obtain ⟨e, He, -, Hst⟩ := Hok1 hok
      unfold plogEntryAt at He
      split at He
      · cases He
      right; rw [← Hst]
      exact entry_last_sub _ _ _ e Hwf (by rw [Hlast]) (by omega) He
  cases ok
  · -- not found: `subterm = 0`
    wp_auto
    have HlsV := Hls (W64 0) (Or.inl rfl)
    svw_tail (W64 0)
  · wp_auto
    have HlsV := Hls st (Or.inr ⟨rfl, rfl⟩)
    svw_tail st

end proof

end EtcdGrove
end Perennial
