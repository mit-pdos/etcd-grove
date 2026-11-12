/- Port of election_proof/proof_traceReceiveMessage.v.

(Q8 stage 1, slice 4, 2026-11-09) Both modes: untraced, the nil check; traced, the message's type
(lent out of the caller's resource), `time.Sleep`, and `traceEvent` with the receive hook's event and
no properties. -/
module

public import Spec.go_etcd_io.raft.v3.traceReceiveMessage
public import Spec.go_etcd_io.raft.v3.traceEvent
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetType
public import Perennial.Spec.time.Sleep

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

set_option hygiene false in
/-- A traced type's event (`ty`, `evt`): `time.Sleep`, then `traceEvent` with the caller's resource,
the receive hook's gate and no properties. -/
local macro "trm_fire " ty:term:max evt:term:max : tactic => `(tactic| (
  subst HoE
  rw [recvGate_of (ty := $ty) (evt := $evt) (by rw [Hty]; rfl) rfl]
  dsimp only [TraceFireOpt]
  try simp only [rsmReceiveAppendEntriesRequest, rsmReceiveAppendEntriesResponse,
    rsmReceiveRequestVoteRequest, rsmReceiveRequestVoteResponse]
  try wp_auto
  wp_apply wp_Sleep
  try wp_auto
  wp_apply wp_traceEvent $evt r ml map.nil (GoInterface.ok l) (some γd) _ Q R $$ [Htl Hfire HP Hback]
  · iframe Htl Hfire
    iapply (trOwn_some γd _).2
    iexists c, id, s, P, (some a), noProps
    iframe HP Hback
    isplitr
    · iapply raftReadLend_of_lend; iexact HRL
    isplitr
    · iexact HML
    isplitr
    · iapply tracingPropsRep_nil
    ipureintro
    refine ⟨by decide, fun e h hm hc h1 _ _ => sendEvOf_of_hdr a.ms $ty [] (by rw [Hty]; rfl)
      (by decide) h hm hc h1⟩
  iintro ⟨HR, HQ⟩
  try wp_auto
  iapply HΦ
  iframe HR HQ))

theorem traceReceiveMessage.wp_proof
    (wp_traceEvent : traceEvent.spec (GF := GF) (hG := hG))
    (wp_GetType : raftpb.Message.GetType.spec (GF := GF) (hG := hG))
    (wp_Sleep : time.Sleep.spec (GF := GF) (hG := hG)) :
    traceReceiveMessage.spec (GF := GF) (hG := hG) := by
  intro r ml tl tr oE Q R
  wp_start as ⟨#Htl, %Hok, Hown, Hfire⟩
  cases tl with
  | nil =>
    wp_auto
    iapply HΦ
    isplitl [Hown]
    · iapply trOwn_wand
      iframe Hown
      iintro ⟨%c, %id, %s, %P, %a, HP, -, -, -, Hb⟩
      iapply Hb $$ HP
    iapply traceFireOpt_nil $$ Hfire
  | ok l =>
    cases tr with
    | none => exact absurd (Hok rfl) (by unfold TraceLoggerOk; exact nofun)
    | some γd =>
      icases (trOwn_some γd _).1 $$ Hown with ⟨%c, %id, %s, %P, %a, HP, #HRL, #HML, %Hp, Hback⟩
      obtain ⟨Hns, HoE⟩ := Hp
      wp_auto
      ihave #HML' := HML
      iunfold MsgLend at HML'
      icases HML' $$ HP with ⟨Hm, HPb⟩
      iunfold msgArg at Hm HPb
      wp_apply wp_GetType.1 $$ [$Hm] as Hm
      ihave HP := HPb $$ Hm
      generalize Hty : a.ms.msg.Type' = t at Hns ⊢
      by_cases h7 : t = W32 7
      · subst h7; exact absurd rfl Hns
      simp only [decide_eq_false h7]
      try wp_auto
      by_cases h8 : t = W32 8
      · subst h8
        wp_auto
        trm_fire MsgType.heartbeat (W64 10)
      simp only [decide_eq_false h8]
      try wp_auto
      by_cases h3 : t = W32 3
      · subst h3
        wp_auto
        trm_fire MsgType.app (W64 10)
      simp only [decide_eq_false h3]
      try wp_auto
      by_cases h9 : t = W32 9
      · subst h9
        wp_auto
        trm_fire MsgType.heartbeatResp (W64 12)
      simp only [decide_eq_false h9]
      try wp_auto
      by_cases h4 : t = W32 4
      · subst h4
        wp_auto
        trm_fire MsgType.appResp (W64 12)
      simp only [decide_eq_false h4]
      try wp_auto
      by_cases h5 : t = W32 5
      · subst h5
        wp_auto
        trm_fire MsgType.vote (W64 14)
      simp only [decide_eq_false h5]
      try wp_auto
      by_cases h6 : t = W32 6
      · subst h6
        wp_auto
        trm_fire MsgType.voteResp (W64 16)
      simp only [decide_eq_false h6]
      try wp_auto
      -- a type the hook does not trace: nothing logged
      subst HoE
      rw [recvGate_none_of (fun ty hty => (untraced_type ⟨h3, h4, h5, h6, h7, h8, h9⟩ ty (Hty ▸ hty)).2)]
      dsimp only [TraceFireOpt]
      iapply HΦ
      iframe Hfire
      iapply (trOwn_some γd _).2
      iapply Hback $$ HP

end proof

end EtcdGrove
end Perennial
