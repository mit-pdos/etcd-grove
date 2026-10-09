/- Port of election_proof/proof_RawNode__HasReady.v (857d09190).

Lean notes: Rocq's `nstate_set_same` is not needed (the record update closing the view
is definitionally `s`). The Rocq proof handles the two ways the hard-state test falls
through (empty, or equal to `prevHardSt`) with `all:`; here the shared tail is the local
macro `rest`. Rocq's `close_view`/`finish_true` are local macros of the same names;
`outboxRel_empty` is the Rocq's inline argument that the outbox is empty. -/
module

public import Spec.go_etcd_io.raft.v3.RawNode__HasReady
public import Spec.go_etcd_io.raft.v3.SoftState__equal
public import Spec.go_etcd_io.raft.v3.IsEmptyHardState
public import Spec.go_etcd_io.raft.v3.isHardStateEqual
public import Spec.go_etcd_io.raft.v3.raftLog__hasNextUnstableSnapshot
public import Spec.go_etcd_io.raft.v3.raftLog__hasNextUnstableEnts
public import Spec.go_etcd_io.raft.v3.raftLog__hasNextCommittedEnts

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

/-- An outbox related to two empty queues is empty. -/
private theorem outboxRel_empty (o : List Msg) (ms1 ms2 : List raftpb.Message) :
    ⊢ outboxRel (GF := GF) o ms1 ms2 -∗ ⌜ms1 = []⌝ -∗ ⌜ms2 = []⌝ -∗ ⌜o = []⌝ := by
  iintro Hob %H1 %H2
  subst H1 H2
  unfold outboxRel
  icases Hob with ⟨%as1, %as2, %Hp, Hb1, Hb2⟩
  ihave %Ha1 := BigSepL2.bigSepL2_length $$ Hb1
  ihave %Ha2 := BigSepL2.bigSepL2_length $$ Hb2
  ipureintro
  cases as1 with
  | cons _ _ => simp at Ha1
  | nil =>
    cases as2 with
    | cons _ _ => simp at Ha2
    | nil => simpa [absList] using Hp

set_option hygiene false in
/-- Rocq's local `close_view`: close the raft struct unchanged (`Hphys`). -/
local macro "close_view" : tactic => `(tactic| (
  ihave Hphys := Hclose $$ Hf_id Hf_Term Hf_Vote Hf_readStates Hf_raftLog Hf_state Hf_lead
    Hf_msgs Hmsgs Hmsgs_cap Hf_msgsAA HmsgsAA HmsgsAA_cap Houtbox Hlog))

set_option hygiene false in
/-- Rocq's local `finish_true`: close the view, refold `ownRawNode`, return `true`. -/
local macro "finish_true" : tactic => `(tactic| (
  close_view
  iapply HΦ
  isplitl
  · unfold ownRawNode
    iexists rnv, sv, steps
    simp only [named]
    iframe Hrn Hphys Hsoft Hsteps Hsteps_cap Hpend Hpown
    ipureintro
    exact ⟨Hasync, Hsoftv, Hhard⟩
  · ipureintro; intro Hc; cases Hc))

set_option hygiene false in
/-- The rest of `HasReady` once the hard-state test fell through (with `Hhs`): Rocq's
`all:` tail, shared by the two ways of falling through. -/
local macro "rest" : tactic => `(tactic| (
  wp_apply wp_raftLog_hasNextUnstableSnapshot $$ [Hlog] as %bsn ⟨Hlog, %Hsn⟩
  · iframe Hlog
  cases bsn
  · ihave %Hm1 := ownSlice_len _ _ _ $$ Hmsgs
    ihave %Hm2 := ownSlice_len _ _ _ $$ HmsgsAA
    wp_auto
    wp_if_destruct
    · finish_true
    have Hl1 := Hif; clear Hif
    wp_if_destruct
    · finish_true
    have Hl2 := Hif; clear Hif
    wp_apply wp_raftLog_hasNextUnstableEnts $$ [Hlog] as %bue ⟨Hlog, %Hue⟩
    · iframe Hlog
    cases bue
    · wp_auto
      wp_method_call
      wp_call
      wp_auto
      rw [Hasync]
      wp_apply wp_raftLog_hasNextCommittedEnts $$ [Hlog] as %bce ⟨Hlog, _⟩
      · iframe Hlog
      cases bce
      · wp_auto
        rw [Hrs]
        wp_auto
        ihave %Hob := outboxRel_empty _ $$ Houtbox [] []
        · ipureintro; apply List.eq_nil_of_length_eq_zero; word
        · ipureintro; apply List.eq_nil_of_length_eq_zero; word
        close_view
        iapply HΦ
        isplitl
        · unfold ownRawNode
          iexists rnv, sv, steps
          simp only [named]
          iframe Hrn Hphys Hsoft Hsteps Hsteps_cap Hpend Hpown
          ipureintro
          exact ⟨Hasync, Hsoftv, Hhard⟩
        · ipureintro
          intro _
          refine ⟨?_, Hhs, Hob, ?_⟩
          · show SoftSt.mk _ _ = _
            rw [Hsoft_eq.1, Hsoft_eq.2, Hsoftv]; rfl
          · simpa using Hue
      · wp_auto
        finish_true
    · wp_auto
      finish_true
  · wp_auto
    finish_true))

theorem RawNode.HasReady.wp_proof
    (wp_SoftState_equal : SoftState.equal.spec (GF := GF) (hG := hG))
    (wp_IsEmptyHardState : IsEmptyHardState.spec (GF := GF) (hG := hG))
    (wp_isHardStateEqual : isHardStateEqual.spec (GF := GF) (hG := hG))
    (wp_raftLog_hasNextUnstableSnapshot :
      raftLog.hasNextUnstableSnapshot.spec (GF := GF) (hG := hG))
    (wp_raftLog_hasNextUnstableEnts : raftLog.hasNextUnstableEnts.spec (GF := GF) (hG := hG))
    (wp_raftLog_hasNextCommittedEnts :
      raftLog.hasNextCommittedEnts.spec (GF := GF) (hG := hG)) :
    RawNode.HasReady.spec (GF := GF) (hG := hG) := by
  intro cfg rn id s rs
  wp_start as H
  iNamed H
  iNamed Hrn
  icases ownRaftPhys_view cfg rnv.raft' id s $$ Hphys with ⟨%rss, %sl1, %sl2, %ms1, %ms2, Hv⟩
  iNamed Hv
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  wp_apply wp_SoftState_equal $$ [$softSt $Hsoft] as ⟨softSt, _⟩
  wp_if_destruct
  rotate_left
  · finish_true
  have Hsoft_eq := Hif; clear Hif
  -- `r.hardState()`
  icases ownRaftLog_struct _ _ $$ Hlog with ⟨%lv, Hl, %Hlv, Hlb⟩
  wp_method_call
  wp_call
  wp_auto
  ihave Hlog := Hlb $$ Hl
  obtain ⟨Hcm, -⟩ := Hlv
  rw [Hcm]
  wp_apply wp_IsEmptyHardState
  wp_if_destruct
  · have Hhs : hsEmptyAbs (nodeHardstate s) = true ∨ nodeHardstate s = rs.hard := by
      left; simp [hsEmptyAbs, nodeHardstate, Hif]
    clear Hcm Hif
    rest
  · wp_apply wp_isHardStateEqual
    rw [Hhard]
    wp_if_destruct
    · have Hhs : hsEmptyAbs (nodeHardstate s) = true ∨ nodeHardstate s = rs.hard := by
        right
        obtain ⟨H1, H2, H3⟩ := Hif
        show HardSt.mk _ _ _ = _
        rw [H1, H2, H3]; rfl
      clear Hcm Hif
      rest
    · finish_true

end proof

end EtcdGrove
end Perennial
