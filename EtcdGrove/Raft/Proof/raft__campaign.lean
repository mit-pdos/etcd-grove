/-
Port of election_proof/proof_raft__campaign.v.

Lean notes: Rocq's `cmsg f` (with a ghost function `f` giving each request's entry id)
is `campMsg` at the one entry id every request carries, `L` (`lastEntryID()`'s result,
which the loop never changes), so the loop invariant needs no `f`. The two `wp_wand`
joins are `wp_join`. `own_tracker_cfg_size` is the pure `ownTracker_cfg_size`;
`elements_split` is `perm_id_cons`; `own_raft_phys_send_perm` is inlined as
`ownRaftPhys_outbox`. The slice range is a `doFor` over an index, as in Rocq.
`wp_raft_poll` is unused, as in Rocq (the postulates include `POLL`).
-/
import EtcdGrove.Raft.Spec.raft__campaign
import EtcdGrove.Raft.Spec.raft__becomeCandidate
import EtcdGrove.Raft.Spec.raft__becomePreCandidate
import EtcdGrove.Raft.Spec.raft__poll
import EtcdGrove.Raft.Spec.raft__send
import EtcdGrove.Raft.Spec.voteRespMsgType
import EtcdGrove.Raft.Spec.raft__promotable
import EtcdGrove.Raft.Spec.JointConfig__IDs
import EtcdGrove.Raft.Spec.raftLog__lastEntryID
import EtcdGrove.Raft.Spec.slices_Sort

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section helpers
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

/-- The message types `campaign` sends, by `pre` (`t = campaignPreElection`): the
request and the self-addressed response. -/
def vreqTy (pre : Bool) : MsgType := if pre then .preVote else .vote
def vrespTy (pre : Bool) : MsgType := if pre then .preVoteResp else .voteResp
def vreqW32 (pre : Bool) : w32 := if pre then MsgPreVote else MsgVote
def vrespW32 (pre : Bool) : w32 := if pre then MsgPreVoteResp else MsgVoteResp

/-- The role transition `campaign` makes, by `pre`. -/
def campRoleState (id : w64) (s : NState) (pre : Bool) : NState :=
  if pre then becomePrecandidate s else becomeCandidate id s

theorem campRoleState_logst (id : w64) (s : NState) (pre : Bool) :
    (campRoleState id s pre).logst = s.logst := by
  cases pre <;> rfl


/-- The request `campaign` sends voter `y`, carrying the entry id `e` that
`lastEntryID()` returned when it was built. -/
def campReq (pre : Bool) (id y T : w64) (e : entryID) : Msg :=
  Msg.mk (vreqTy pre) id y T false e.index' e.term' (W64 0) (W64 0) []

/-- The message `campaign` sends on behalf of voter `y`: the self-addressed response
when `y` is this node, a request otherwise. `send` panics on a self-addressed request,
which is exactly why the code splits these two cases. (Rocq's `cmsg f` takes a ghost
function `f` for the entry id of each request; every request carries the same one,
`L`, so here it is that entry id.) -/
def campMsg (pre : Bool) (id T : w64) (e : entryID) (y : w64) : Msg :=
  if y = id then Msg.plain (vrespTy pre) id id T false else campReq pre id y T e

omit [GoGlobalContext] [GoSemanticsFunctions] in
/-- `xs` enumerates the voters, so it is `id` followed by the other voters in some
order -- which is exactly the shape `step_campaignState` asks for. (Rocq
`elements_split`.) -/
theorem perm_id_cons (cfg : GSet w64) (id : w64) (xs : List w64) (Hid : id ∈ cfg)
    (Hnd : xs.Nodup) (Hmem : ∀ z, z ∈ xs ↔ z ∈ cfg) :
    xs ≡ₚ id :: elements (cfg \ {[id]}) := by
  have Hnin : id ∉ elements (cfg \ {[id]}) := by
    rw [GMap.elem_of_elements, GMap.elem_of_difference, GMap.elem_of_singleton]
    exact fun h => h.2 rfl
  refine (List.perm_ext_iff_of_nodup Hnd
    (List.nodup_cons.2 ⟨Hnin, GMap.NoDup_elements _⟩)).2 ?_
  intro z
  rw [Hmem, List.mem_cons, GMap.elem_of_elements, GMap.elem_of_difference,
    GMap.elem_of_singleton]
  constructor
  · intro h; by_cases hz : z = id
    · exact Or.inl hz
    · exact Or.inr ⟨h, hz⟩
  · rintro (rfl | ⟨h, -⟩)
    · exact Hid
    · exact h

omit [GoGlobalContext] [GoSemanticsFunctions] in
private theorem ite_of_true {α : Sort _} {c : Prop} [Decidable c] (h : c) (a b : α) :
    (if c then a else b) = a := by simp [h]

/-- Two sends in a row grow the outbox by the concatenation. -/
theorem sendMsgs_app (s0 : NState) (ms1 ms2 : List Msg) :
    sendMsgs (sendMsgs s0 ms1) ms2 = sendMsgs s0 (ms1 ++ ms2) := by
  simp [sendMsgs, List.append_assoc]

theorem sendMsgs_log (s0 : NState) (ms : List Msg) : (sendMsgs s0 ms).log = s0.log := rfl
theorem sendMsgs_logst (s0 : NState) (ms : List Msg) :
    (sendMsgs s0 ms).logst = s0.logst := rfl

end helpers

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `ownTracker` pins the voter set's cardinality (Rocq `own_tracker_cfg_size`):
`campaign` runs `make([]uint64, 0, len(idMap))` and `wp_slice_make3` needs
`0 ≤ sint.Z cap`. A pure consequence, so the tracker survives the read. -/
private theorem ownTracker_cfg_size (cfg : GSet w64) (tv : tracker.ProgressTracker) (t : Trk) :
    ownTracker (GF := GF) cfg tv t ⊢ ⌜(GMap.size cfg : Int) < 2 ^ 63⌝ := by
  iintro Hown
  unfold ownTracker
  iNamed Hown
  ipureintro
  exact Hcfg_size

theorem raft.campaign.wp_proof
    (wp_raft_becomeCandidate : raft.becomeCandidate.spec (GF := GF) (hG := hG))
    (wp_raft_becomePreCandidate : raft.becomePreCandidate.spec (GF := GF) (hG := hG))
    (wp_raft_poll : raft.poll.spec (GF := GF) (hG := hG))
    (wp_raft_send : raft.send.spec (GF := GF) (hG := hG))
    (wp_voteRespMsgType : voteRespMsgType.spec (GF := GF) (hG := hG))
    (wp_raft_promotable : raft.promotable.spec (GF := GF) (hG := hG))
    (wp_JointConfig_IDs : quorum.JointConfig.IDs.spec (GF := GF) (hG := hG))
    (wp_raftLog_lastEntryID : raftLog.lastEntryID.spec (GF := GF) (hG := hG))
    (wp_slices_Sort : slices.«Sort».spec (GF := GF) (hG := hG)) :
    raft.campaign.spec (GF := GF) (hG := hG) := by
  intro cfg r id s t Hrole Hid_cfg Hnowrap
  -- every `send` below carries `Term + 1`; `send` panics on a zero term,
  -- whence the premise.
  have Hno_wrap : s.term + W64 1 ≠ W64 0 := by word
  wp_start as Hphys
  wp_auto
  -- `promotable` is only logged: `id ∈ cfg`, but a pending snapshot makes
  -- it false. The two arms are joined.
  wp_apply wp_raft_promotable $$ [$Hphys] as %b ⟨Hphys, %Hb⟩
  wp_join at next with [Hphys r]
  · cases b
    · wp_auto
      wp_apply raft.wp_load_id $$ Hphys as Hphys
      wp_raft_log
      wp_join_done
    · wp_auto
      wp_join_done
  -- the role transition: `becomePreCandidate` and `Term + 1`, or
  -- `becomeCandidate` and the new `Term`; joined at the state each leaves
  wp_join iprop(∃ (pvs : GMap w64 Progress),
      "Hphys" ∷ ownRaftPhys cfg r id
        { campRoleState id s (decide (t = campaignPreElection)) with prvals := pvs } ∗
      "term" ∷ term_ptr ↦ (s.term + W64 1) ∗
      "voteMsg" ∷ voteMsg_ptr ↦ vreqW32 (decide (t = campaignPreElection)) ∗
      "r" ∷ r_ptr ↦ r ∗ "t" ∷ t_ptr ↦ t) with [Hphys term voteMsg r t]
  · wp_apply wp_raft_becomePreCandidate _ _ _ _ Hrole $$ [$Hphys] as Hphys
    rw [show raftpb.MsgPreVote = #MsgPreVote from rfl]
    wp_auto
    wp_apply raft.wp_load_Term $$ Hphys as Hphys
    isplitr
    · ipureintro; rfl
    iexists s.prvals
    simp only [campaignPreElection, decide_true, campRoleState, vreqW32, ↓reduceIte]
    iframe
  · wp_apply wp_raft_becomeCandidate _ _ _ _ Hrole $$ [$Hphys] as %pvs Hphys
    rw [show raftpb.MsgVote = #MsgVote from rfl]
    wp_auto
    wp_apply raft.wp_load_Term $$ Hphys as Hphys
    isplitr
    · ipureintro; rfl
    iexists pvs
    have Hne : ¬ t = campaignPreElection := Hif
    simp only [decide_eq_false Hne, campRoleState, vreqW32, Bool.false_eq_true, ↓reduceIte]
    iframe
  iintro HJ
  iNamed HJ
  generalize decide (t = campaignPreElection) = pre
  wp_auto
  -- the voter ids, as a map. `IDs` is a method of the tracker's
  -- `Config.Voters`, so it takes the tracker object; the call does not
  -- change it, and the struct is re-sealed right after.
  icases ownRaftPhys_tracker_same cfg r id _ $$ Hphys with ⟨%tv, Htrkf, Htrk, Hback⟩
  wp_apply (quorum.JointConfig.IDs.spec_tracker wp_JointConfig_IDs) $$ [$Htrkf $Htrk] as %mref %idm ⟨Htrkf, Hown, Hidm, %Hdomidm⟩
  -- `ownTracker` pins the voter set's cardinality: `campaign` runs
  -- `make([]uint64, 0, len(idMap))` and `wp_slice_make3` needs `0 ≤ cap`.
  -- (Rocq's `own_tracker_cfg_size`; here the tracker is opened and re-sealed.)
  ihave %Hcfg_fits := ownTracker_cfg_size cfg tv _ $$ Hown
  ihave Hphys := Hback $$ %tv Htrkf Hown
  wp_apply wp_map_len $$ Hidm as Hidm
  have Hszidm : GMap.size idm = GMap.size cfg := by
    rw [← Hdomidm, GMap.size_dom]
  rw [Hszidm]
  wp_apply wp_slice_make3 (V := w64) (t := go.uint64) (W64 0) (W64 (GMap.size cfg))
    (by word) as %sl ⟨Hsl, Hsl_cap, %Hslcap⟩
  simp only [List.replicate_zero]
  -- The map range appends the voter ids to `ids`, in the order `IDs` yields
  -- them. `0 ≤ i` has to be part of the invariant: `wp_map_for_range`'s
  -- body hypothesis is quantified over all `i` whose lookup succeeds, and
  -- without it `take (i+1).toNat` cannot be split.
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (keys : List w64) (i : Int) => iprop(∃ (sl' : GoSlice) (x : w64),
      "%Hi" ∷ ⌜0 ≤ i⌝ ∗
      "ids" ∷ ids_ptr ↦ sl' ∗
      "Hsl" ∷ sl' ↦* keys.take i.toNat ∗
      "Hsl_cap" ∷ ownSliceCap w64 sl' (DFrac.own 1) ∗
      "id" ∷ id_ptr ↦ x)) $$ Hidm
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [ids Hsl Hsl_cap id]
  · iexists sl, zero_val w64
    simp only [Int.toNat_zero, List.take_zero]
    iframe
    ipureintro
    omega
  isplitr
  · imodintro
    iintro %i %key %vv ⟨%Hkey, %Hvv⟩ HP
    iNamed HP
    wp_auto
    wp_apply wp_slice_literal (V := w64) [key]
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    wp_apply wp_slice_append $$ [$Hsl $Hsl_cap $Hsl2] as %sl3 ⟨Hsl, Hsl_cap, -⟩
    unfold forMapPostcondition
    iright
    ileft
    isplitr
    · ipureintro; rfl
    have Htake : keys.take (i + 1).toNat = keys.take i.toNat ++ [key] := by
      rw [show (i + 1).toNat = i.toNat + 1 by omega]
      rw [List.take_add_one, Hkey]; rfl
    iexists sl3, key
    rw [Htake]
    iframe
    ipureintro
    omega
  -- the range is over, so `ids` holds every voter id exactly once.
  iintro HP -
  iNamed HP
  rw [← Hklen, Int.toNat_natCast, List.take_length]
  wp_auto
  wp_apply wp_slices_Sort $$ [$Hsl] as %xs ⟨Hsl, %Hxs, -⟩
  have Hkeys_perm : keys ≡ₚ elements cfg := by
    refine (List.perm_ext_iff_of_nodup Hknodup (GMap.NoDup_elements cfg)).2 ?_
    intro k
    rw [Hkset, GMap.elem_of_elements, ← Hdomidm, GMap.elem_of_dom]
    cases idm !! k <;> simp
  have Hlenxs : xs.length = GMap.size cfg := by
    rw [← Hxs.length_eq, Hklen, Hszidm]
  have Hnodupxs : xs.Nodup := Hxs.nodup_iff.1 Hknodup
  ihave %Hxslen := ownSlice_len _ _ _ $$ Hsl
  ihave Hphys := ownRaftPhys_send_nil cfg r id _ $$ Hphys
  -- every request carries the log's last entry id, `L`
  ihave IH : iprop(∃ (n x : w64),
      "i" ∷ i_ptr ↦ n ∗
      "id" ∷ id_ptr ↦ x ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (xs.length : Int)⌝ ∗
      "Hphys" ∷ ownRaftPhys cfg r id
        (sendMsgs { campRoleState id s pre with prvals := pvs }
          ((xs.take (sint.Z n).toNat).map (campMsg pre id (s.term + W64 1)
            (plogLast s.logst.prev (s.logst.sents ++ s.logst.uents)))))) $$ [i id Hphys]
  · iexists W64 0, zero_val w64
    iframe
    ipureintro
    word
  wp_for IH
  wp_if_destruct
  · -- one more voter to notify
    obtain ⟨y, Hy⟩ : ∃ y, xs[(sint.Z n).toNat]? = some y :=
      ⟨_, List.getElem?_eq_getElem (by word)⟩
    rw [ite_of_true (by word)]
    wp_apply wp_load_slice_index (V := w64) (t := go.uint64) sl' (sint.Z n) xs (DFrac.own 1) y
      (by word) $$ [Hsl] as Hsl
    · iframe; ipureintro; exact Hy
    have Hylt : (sint.Z n).toNat < xs.length := (List.getElem?_eq_some_iff.1 Hy).1
    -- `y` has not been visited yet: `xs` has no duplicates
    have Hgrow : xs.take (sint.Z (n + W64 1)).toNat = xs.take (sint.Z n).toNat ++ [y] := by
      rw [show (sint.Z (n + W64 1)).toNat = (sint.Z n).toNat + 1 by word, List.take_add_one, Hy]
      rfl
    wp_apply raft.wp_load_id $$ Hphys as Hphys
    by_cases Hyid : y = id
    · -- this node's own vote: a self-addressed response
      subst Hyid
      rw [decide_eq_true rfl]
      wp_auto
      -- the response type: `wp_auto` cannot step through the call that
      -- computes the literal's `Type` field
      wp_apply wp_voteRespMsgType (vreqW32 pre) (vrespW32 pre)
        (by cases pre <;> simp [vreqW32, vrespW32])
      -- `send`'s side conditions: `From = 0` (the literal leaves it unset),
      -- and `SendOk`'s vote clause -- the type is a vote message, its
      -- `mtypeOf`, the term is nonzero (this is what the no-wrap premise
      -- buys), and -- only for a request -- the destination is not this
      -- node. The last is vacuous here: this is a response.
      wp_apply wp_raft_send _ _ _ _ _ [] [Msg.plain (vrespTy pre) y y (s.term + W64 1) false]
          (Or.inl rfl)
          (Or.inl ⟨vrespTy pre,
            by cases pre <;> simp [vrespW32],
            by cases pre <;> rfl,
            Hno_wrap,
            by cases pre <;> simp [vrespW32, MsgVote, MsgPreVote, MsgVoteResp, MsgPreVoteResp],
            by cases pre <;> rfl⟩)
        $$ [$Hphys]
      · isplitr
        · iapply ownSlice_nil
        iapply send_no_snap
        cases pre <;> simp [vrespW32, MsgSnap, MsgVoteResp, MsgPreVoteResp]
      iintro Hphys
      ihave Hphys : ownRaftPhys cfg r y
          (sendMsgs { campRoleState y s pre with prvals := pvs }
            ((xs.take (sint.Z (n + W64 1)).toNat).map (campMsg pre y (s.term + W64 1)
              (plogLast s.logst.prev (s.logst.sents ++ s.logst.uents))))) $$ [Hphys]
      · rw [Hgrow, List.map_append, ← sendMsgs_app]
        simp only [List.map_cons, List.map_nil, campMsg, ↓reduceIte]
        iexact Hphys
      wp_auto
      wp_for_post
      iframe
      iexists _, _
      iframe
      ipureintro
      word
    · -- a peer: read the last entry, log, and send it a request
      rw [decide_eq_false Hyid]
      wp_auto
      wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
      icases ownRaftPhys_log_same cfg r id _ $$ Hphys with ⟨Hlog, Hback⟩
      ihave Hlog : ownRaftLog (campRoleState id s pre).log (campRoleState id s pre).logst $$ [Hlog]
      · simp only [sendMsgs_log, sendMsgs_logst]; iexact Hlog
      wp_apply wp_raftLog_lastEntryID $$ [$Hlog] as %lastID ⟨Hlog, %HlastID⟩
      ihave Hphys := Hback $$ [Hlog]
      · simp only [sendMsgs_log, sendMsgs_logst]; iexact Hlog
      wp_apply raft.wp_load_id $$ Hphys as Hphys
      wp_apply raft.wp_load_Term $$ Hphys as Hphys
      wp_raft_log
      rw [campRoleState_logst] at HlastID
      -- `ctx` is the `campaignTransfer` marker or nil; the model does not
      -- look at a vote request's context, so both arms run the same tail.
      wp_join iprop(∃ (csl : GoSlice), ctx_ptr ↦ csl ∗ t_ptr ↦ t) with [ctx t] as ⟨%csl, ctx, t⟩
      · wp_apply wp_string_to_bytes as %csl ⟨-, -⟩
        wp_join_done
      wp_apply wp_raft_send _ _ _ _ _ [] [campReq pre id y (s.term + W64 1) lastID]
          (Or.inl rfl)
          (Or.inl ⟨vreqTy pre,
            by cases pre <;> simp [vreqW32],
            by cases pre <;> rfl,
            Hno_wrap,
            fun _ => Hyid,
            by cases pre <;> rfl⟩)
        $$ [$Hphys]
      · isplitr
        · iapply ownSlice_nil
        iapply send_no_snap
        cases pre <;> simp [vreqW32, MsgSnap, MsgVote, MsgPreVote]
      iintro Hphys
      ihave Hphys : ownRaftPhys cfg r id
          (sendMsgs { campRoleState id s pre with prvals := pvs }
            ((xs.take (sint.Z (n + W64 1)).toNat).map (campMsg pre id (s.term + W64 1)
              (plogLast s.logst.prev (s.logst.sents ++ s.logst.uents))))) $$ [Hphys]
      · rw [Hgrow, List.map_append, ← sendMsgs_app]
        simp only [List.map_cons, List.map_nil, campMsg, Hyid, ↓reduceIte, ← HlastID]
        iexact Hphys
      wp_auto
      wp_for_post
      iframe
      iexists _, _
      iframe
      ipureintro
      word
  · -- every voter has been notified
    have Hfull : (sint.Z n).toNat = xs.length := by word
    rw [Hfull, List.take_length]
    iapply HΦ $$ %(elements (cfg \ {[id]})) %pvs
    isplitr
    · ipureintro; rfl
    have Hmem : ∀ z, z ∈ xs ↔ z ∈ cfg := by
      intro z
      rw [← Hxs.mem_iff, Hkeys_perm.mem_iff, GMap.elem_of_elements]
    have Hsplit := perm_id_cons cfg id xs Hid_cfg Hnodupxs Hmem
    -- `campMsg` turns `id` into the self-addressed response and every other voter
    -- into one request each
    have Hmap : xs.map (campMsg pre id (s.term + W64 1)
          (plogLast s.logst.prev (s.logst.sents ++ s.logst.uents))) ≡ₚ
        [Msg.plain (vrespTy pre) id id (s.term + W64 1) false] ++
          (elements (cfg \ {[id]})).map (fun d => campReq pre id d (s.term + W64 1)
            (plogLast s.logst.prev (s.logst.sents ++ s.logst.uents))) := by
      refine (Hsplit.map _).trans ?_
      rw [List.map_cons]
      simp only [campMsg, ↓reduceIte, List.singleton_append]
      refine List.Perm.cons _ (List.Perm.of_eq (List.map_congr_left ?_))
      intro z hz
      have : z ≠ id := by
        rw [GMap.elem_of_elements, GMap.elem_of_difference, GMap.elem_of_singleton] at hz
        exact hz.2
      simp [campMsg, this]
    ihave Hphys := ownRaftPhys_outbox cfg r id _
      ((campRoleState id s pre).outbox ++
        ([Msg.plain (vrespTy pre) id id (s.term + W64 1) false] ++
          (elements (cfg \ {[id]})).map (fun d => campReq pre id d (s.term + W64 1)
            (plogLast s.logst.prev (s.logst.sents ++ s.logst.uents)))))
      (List.Perm.append_left _ Hmap.symm) $$ Hphys
    iapply ownRaftPhys_eq $$ Hphys
    cases pre <;> rfl

end proof

end EtcdGrove
end Perennial
