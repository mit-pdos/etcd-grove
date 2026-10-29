/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_MsgStorageApplyResp.v
(857d09190).

`Step`'s `MsgStorageApplyResp` branch (2026-10-05), in its own file. Proof structure,
not specification: no `Module Type`, no `Parameter`; only `Proof/raft__Step.lean` may
import this module.

Lean notes: the branch lemma takes the callee specs (Rocq's functor argument
`P : STEP_POSTULATES`) as its first argument `_P : raft.Step.Postulates`, and Rocq's
section variable `c` as its second.
-/
module

public import Proof.go_etcd_io.raft.v3.raft__Step.Base
public import Proof.go_etcd_io.raft.v3.raft__Step.ReplLemmas
-- (2026-10-29, stage U5) the leave's entry decodes
public import Spec.google_golang_org.protobuf.proto.UnmarshalConfChangeV2Empty

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section branches
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

namespace StepProof

/-- `appliedTo` as a `StepCD` step (2026-10-14, stage B7): nothing the protocol sees, and in the
dynamic model `StepR.advance` to the new `applied` (A1, from `DynHyp`), which moves the
configuration index along. -/
private theorem stepCD_appliedTo (c : CfgM) (id : w64) (m : MessageM) (s : NState)
    (idx sz : w64) (Hty : m.Type' = MsgStorageApplyResp)
    (Hidx : uint.Z idx ≤ uint.Z s.logst.committed)
    (Hac : uint.Z s.logst.applied ≤ uint.Z s.logst.committed) :
    StepCD c id B m s [] { s with logst := logAppliedTo s.logst idx sz } := by
  refine ⟨by rw [toPState_logAppliedTo]; exact .refl _, fun Adm dec g hc hd => ?_⟩
  have Ha1 := hd.2.2.2.1 Hty
  refine ⟨max g.cidx (uint.nat (w64Max idx s.logst.applied)), .inr ⟨Hty, rfl⟩, ?_⟩
  have Hr : rOf { s with logst := logAppliedTo s.logst idx sz }
      { g with cidx := max g.cidx (uint.nat (w64Max idx s.logst.applied)) } =
      { rOf s g with applied := w64Max idx s.logst.applied,
                     cidx := max (rOf s g).cidx (uint.nat (w64Max idx s.logst.applied)) } := by
    unfold rOf pciR
    rw [toPState_logAppliedTo]
    simp [logAppliedTo]
  rw [Hr]
  refine StepR.advance (rOf s g) (w64Max idx s.logst.applied) ?_ ?_ Ha1
  · show uint.Z s.logst.applied ≤ uint.Z (w64Max idx s.logst.applied)
    unfold w64Max; split <;> word
  · show uint.Z (w64Max idx s.logst.applied) ≤ uint.Z s.logst.committed
    unfold w64Max; split <;> word

omit [GooseInterp] [GooseSemantics] go_gctx in
/-- `LocalFrame` composes (2026-10-29, stage U5: the advance, then the automatic leave). -/
theorem LocalFrame.trans' {s s1 s2 : NState} (h1 : LocalFrame s s1) (h2 : LocalFrame s1 s2) :
    LocalFrame s s2 := by
  obtain ⟨a1, b1, c1, d1, e1, f1, g1, h1', i1, j1, k1, l1⟩ := h1
  obtain ⟨a2, b2, c2, d2, e2, f2, g2, h2', i2, j2, k2, l2⟩ := h2
  exact ⟨a2.trans a1, Int.le_trans b1 b2, c2.trans c1, d2.trans d1, e2.trans e1, f2.trans f1,
    g2.trans g1, h2'.trans h1', i2.trans i1, j2.trans j1, k2.trans k1, Int.le_trans l1 l2⟩

omit [GooseInterp] [GooseSemantics] go_gctx in
/-- **The advance, then the automatic leave** (2026-10-29, stage U5): `appliedTo`'s `StepCD` step of
the acknowledgement (`m`, nothing received) and its leave's (`leaveMsgM`, the leave received when
appended) are one step of the acknowledgement. Dynamically, the leave's premises (`DynHyp`) come
from the acknowledgement's: no snapshot, a leader (no campaign guard), the full prefix kept, room in
the log; the configuration index moves once, by the advance. -/
theorem StepCD.trans_leave {c : CfgM} {id : w64} {B : Int} {m : MessageM} {s s1 s' : NState}
    {recv : List Msg}
    (h1 : StepCD c id B m s [] s1) (h2 : StepCD c id B leaveMsgM s1 recv s')
    (Hrl : s1.role = .leader) (Hbase : (toPState s1).base = (toPState s).base)
    (Happl : s'.logst.applied = s1.logst.applied)
    (Hbound : plogLastIndexZ (toPState s1).base (toPState s1).log + 2 ^ 61 < 2 ^ 64) :
    StepCD c id B m s recv s' := by
  refine ⟨by simpa using StepC.trans _ _ _ _ _ h1.1 h2.1, fun Adm dec g hc hd => ?_⟩
  have hty2 : leaveMsgM.Type' = MsgProp := rfl
  have hd1 : DynHyp dec m s s1 g :=
    ⟨hd.1, hd.2.1, hd.2.2.1, fun h => Happl ▸ hd.2.2.2.1 h, hd.2.2.2.2⟩
  obtain ⟨cidx1, hcm1, hr1⟩ := h1.2 Adm dec g hc hd1
  have hd2 : DynHyp dec leaveMsgM s1 s' { g with cidx := cidx1 } :=
    ⟨by rw [hty2]; w32_ne, fun h => absurd (Hrl.symm.trans h) (by decide),
     by rw [Hbase]; exact hd.2.2.1, fun h => absurd (hty2.symm.trans h) (by w32_ne),
     fun _ => Hbound⟩
  obtain ⟨cidx2, hcm2, hr2⟩ := h2.2 Adm dec { g with cidx := cidx1 } hc hd2
  have hc2 : cidx2 = cidx1 := by
    rcases hcm2 with h | ⟨h, -⟩
    · exact h
    · exact absurd (hty2.symm.trans h) (by w32_ne)
  subst hc2
  refine ⟨cidx2, ?_, by simpa using StepR.trans _ _ _ _ _ hr1 hr2⟩
  rcases hcm1 with h | ⟨h, h'⟩
  · exact .inl h
  · exact .inr ⟨h, by rw [Happl]; exact h'⟩

/-- **The automatic leave's proposal is legitimately sent** (2026-10-29, stage U5): its one entry is
a filler (an empty `ConfChangeV2`, `Filler`), whose data decodes (`ccDecodeV2_nil`), so raft's own
leave needs no client's deposit. -/
theorem isMessage_leave (γ : RaftNames) : ⊢ isMessage (GF := GF) γ leaveAbs := by
  unfold leaveAbs isMessage absMsg absMsgFrom
  isplitr
  · ipureintro
    exact ⟨rfl, List.cons_ne_nil _ _, by simp⟩
  iapply (BigSepL.bigSepL_singleton (Φ := fun _ e => propData (GF := GF) γ e)).2
  unfold propData
  iexists none
  unfold propDataIs
  ipureintro
  exact ⟨⟨rfl, .inr rfl⟩, fun h => absurd h (show W32 2 ≠ W32 1 by w32_ne), fun _ => ⟨_, ccDecodeV2_nil⟩⟩

/-- ... and carries no ticket (a filler's entry, `entTk`). -/
theorem msgTks_leave (γ : RaftNames) : ⊢ msgTks (GF := GF) γ leaveAbs := by
  unfold msgTks leaveAbs absMsg absMsgFrom
  simp only [↓reduceIte]
  iapply (BigSepL.bigSepL_singleton (Φ := fun _ e => entTk (GF := GF) γ e)).2
  unfold entTk
  rw [ite_eq_left (show Filler leaveEntM.Type' leaveEntM.Data' from ⟨rfl, .inr rfl⟩)]
  iempintro

set_option maxHeartbeats 1000000 in
/-- The local acknowledgement `RawNode.Advance` steps after the application applied a
`Ready`'s committed entries (`newStorageApplyRespMsg`: `Term = 0`, `Entries` the
entries). The term preamble is skipped; the type switch's `MsgStorageApplyResp` case
runs

    if len(m.Entries) > 0 {
        index := m.Entries[len(m.Entries)-1].Index
        r.appliedTo(index, entsSize(m.Entries))
        r.reduceUncommittedSize(payloadsSize(m.Entries))
    }

moving `applied` (`logAppliedTo`); (2026-10-29, stage U5) and a leader at a configuration it
leaves automatically proposes the leave (`appliedTo`'s `LeaveStep`), which is received (`recv`,
the leave's proposal `leaveAbs`) at the bound `B` of its entry, its receipt given back. The
premises are `appliedTo`'s: the last entry is committed, a leader's term nonzero, the last index a
word, the last index's receipt (`⧖ k0`). -/
theorem wp_Step_MsgStorageApplyResp (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (_Q : raft.Step.ReplPbPostulates (GF := GF) (hG := hG))
    (c : CfgM) (r : Loc) (id : w64) (s : NState) (ml : Loc) (m : MessageM)
    (sn : Option SnapshotM) (ctx : List w8) (rs : List Loc)
    (ents : List EntryM) (k0 : Nat) :
    m.Type' = MsgStorageApplyResp →
    m.Term' = W64 0 →
    (∀ e, ents.getLast? = some e → uint.Z e.Index' ≤ uint.Z s.logst.committed ∧
      uint.Z e.Index' ≤ uint.Z s.logst.applying) →
    NStateWf s →
    -- (2026-10-29, stage U5; until then `c.autoLeave = true → s.role ≠ .leader`) `appliedTo`'s
    -- premises for its leave's proposal
    (s.role = .leader → s.term ≠ W64 0) →
    plogLastIndexZ (toPState s).base (toPState s).log < 2 ^ 64 →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
        "Hm" ∷ msgIn ml DFrac.discard ⟨m, ents, sn, ctx, rs⟩ ∗
        "#Hrc" ∷ ⧖ k0 }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #ml))
    {{ (err : GoInterface) (s' : NState) (B : Int) (recv : List Msg), RET #err;
        "Hphys" ∷ ownRaftPhysCV c c.voters r id s' ∗
        "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
        "%Hframe" ∷ ⌜LocalFrame s s' ∧
                     ((∀ e, ents.getLast? = some e → uint.Z e.Index' ≤ uint.Z s.logst.applying) →
                      s'.logst.applying = s.logst.applying)⌝ ∗
        -- (2026-10-25, T-M M2b) a pre-candidate keeps its log and commit index (`PreKeep`)
        "%Hpk" ∷ ⌜s.role = .preCandidate → PreKeep s s'⌝ ∗
        -- (2026-10-29, stage U5) the leave's proposal received, if appended, at the bound `B`
        "%Hrecv" ∷ ⌜(∀ m' ∈ recv, m' = leaveAbs) ∧ recv.length ≤ 1⌝ ∗
        "%HBb" ∷ ⌜plogLastIndexZ (toPState s).base (toPState s).log ≤ B ∧
          B ≤ plogLastIndexZ (toPState s).base (toPState s).log + 1 ∧ B < 2 ^ 64⌝ ∗
        "Hrcb" ∷ (⌜plogLastIndexZ (toPState s).base (toPState s).log < B⌝ -∗ ⧖ (k0 + 1)) ∗
        "%Hrefines" ∷ ⌜StepCD c id B m s recv s'⌝ ∗
        -- (2026-10-14, stage B7) `applied` moves at most to the last entry's index
        "%Happ" ∷ ⌜s'.logst.applied = s.logst.applied ∨
          ∃ e, ents.getLast? = some e ∧ s'.logst.applied = w64Max e.Index' s.logst.applied⌝ ∗
        -- (D19i part 1) and at least to it
        "%Happ2" ∷ ⌜∀ e, ents.getLast? = some e → uint.Z e.Index' ≤ uint.Z s'.logst.applied⌝ ∗
        "%Herr" ∷ ⌜err = interface.nil⌝ }} := by
  intro Hty Hterm Hlast Hwf Hlnz HL
  wp_start as H
  iNamed H
  icases msgPtsC_nn _ _ _ _ _ $$ Hm with ⟨%Hnn, Hm⟩
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_apply _P.traceReceiveMessage
  try wp_auto
  wp_get _Q
  -- `m.Term = 0` (a local message), so the term preamble is skipped
  rw [decide_eq_true Hterm]
  wp_auto
  -- the type switch: not `MsgHup`, not `MsgStorageAppendResp`, but
  -- `MsgStorageApplyResp`
  wp_drive _Q
  wp_apply wp_GetEntries_ro _Q $$ [$Hm] as %es1 ⟨#Hes1, Hm⟩
  ihave %Hlen := entsPts_len $$ Hes1
  try wp_auto
  cases He : ents.getLast? with
  | none =>
    -- no entries: nothing to do
    rw [List.getLast?_eq_none_iff] at He
    subst He
    rw [decide_eq_false (by simp only [List.length_nil] at Hlen; word)]
    wp_auto
    iapply HΦ $$ %interface.nil %s %(plogLastIndexZ (toPState s).base (toPState s).log)
      %([] : List Msg)
    iframe Hphys
    isplitr
    · ipureintro; exact Hwf
    isplitr
    · ipureintro
      exact ⟨⟨rfl, Int.le_refl _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Int.le_refl _⟩, fun _ => rfl⟩
    isplitr
    · ipureintro; exact fun _ => ⟨rfl, rfl, rfl, fun h => h, Int.le_refl _⟩
    isplitr
    · ipureintro; exact ⟨by simp, by simp⟩
    isplitr
    · ipureintro; exact ⟨Int.le_refl _, by omega, HL⟩
    isplitr
    · iintro %Hlt; exact absurd Hlt (Int.lt_irrefl _)
    ipureintro
    exact ⟨StepCD.frame (.refl _) (RFrame.refl _), .inl rfl, fun _ h => by simp at h, rfl⟩
  | some e =>
    obtain ⟨es, rfl⟩ := List.getLast?_eq_some_iff.1 He
    simp only [List.length_append, List.length_singleton] at Hlen
    rw [decide_eq_true (by word)]
    wp_auto
    -- `m.GetEntries()[len(m.GetEntries())-1].GetIndex()`
    wp_apply wp_GetEntries_ro _Q $$ [$Hm] as %es2 ⟨#Hes2, Hm⟩
    wp_apply wp_GetEntries_ro _Q $$ [$Hm] as %es3 ⟨#Hes3, Hm⟩
    ihave %Hlen2 := entsPts_len $$ Hes2
    ihave %Hlen3 := entsPts_len $$ Hes3
    simp only [List.length_append, List.length_singleton] at Hlen2 Hlen3
    icases entsRO_lookup es2 (es ++ [e]) es.length e (by simp) $$ Hes2
      with ⟨%ls, %le, #Hls, #He, %Hl⟩
    try wp_auto
    rw [ite_eq_left ⟨by word, by word⟩]
    wp_apply wp_load_slice_index es2 (sint.Z (es3.len - W64 1)) ls DFrac.discard le (by word)
      $$ [Hls] with -
    · iframe Hls; ipureintro
      rw [show (sint.Z (es3.len - W64 1)).toNat = es.length by word]; exact Hl.1
    wp_apply _Q.EntryGetIndex.1 le DFrac.discard e $$ [He] with -
    · iframe He
    try wp_auto
    wp_apply wp_GetEntries_ro _Q $$ [$Hm] as %es4 ⟨#Hes4, Hm⟩
    wp_apply _P.entsSize $$ [$Hes4] as %sz -
    -- `applied ≤ applying`: `applying` stays put when the entries end at or below it
    icases ownRaftPhysC_log_same c r id s $$ Hphys with ⟨Hlog, Hback⟩
    icases ownRaftLog_ready_wf _ _ $$ Hlog with ⟨%Hrw, Hlog⟩
    icases ownRaftLog_committed _ _ $$ Hlog with ⟨%Hcm, Hlog⟩
    icases ownRaftLog_quiet _ _ $$ Hlog with ⟨%Hq0, Hlog⟩
    ihave Hphys := Hback $$ Hlog
    -- (D22 S-d2) `appliedTo` is stated on the struct in the windows
    ihave Hphys := ownRaftPhysCV_toW c r id s $$ Hphys
    wp_apply _P.appliedTo c r id s e.Index' sz k0 (Hlast e He).1
      (fun h => absurd (Hlast e He).2 (Int.not_le.2 h)) (fun _ => Hwf) Hlnz (fun _ => HL) Hq0.1
      (fun h => absurd (Hq0.2.symm.trans h) (by decide))
      (fun _ _ h => absurd (Hlast e He).2 (Int.not_le.2 h))
      (fun _ _ h => absurd (Hlast e He).2 (Int.not_le.2 h))
      (fun h => absurd (Hq0.2.symm.trans h) (by decide)) $$ [$Hphys $Hrc]
      as %s2 %B %recv ⟨Hphys, %Hls, Hrcb⟩
    try wp_auto
    wp_apply wp_GetEntries_ro _Q $$ [$Hm] as %es5 ⟨#Hes5, Hm⟩
    wp_apply _P.payloadsSize $$ [$Hes5] as %psz -
    wp_apply _P.reduceUncommittedSize $$ [$Hphys] as Hphys
    -- the state at the new `applied`, `s1`; then `appliedTo`'s leave, if any (`LeaveStep`)
    generalize Hs1 : ({ s with logst := logAppliedTo s.logst e.Index' sz } : NState) = s1 at Hls
    have Hwf1 : NStateWf s1 := by rw [← Hs1]; exact Hwf
    have Hfr1 : LocalFrame s s1 := by
      rw [← Hs1]
      exact ⟨rfl, Int.le_refl _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by
        show uint.Z s.logst.applied ≤ uint.Z (w64Max e.Index' s.logst.applied)
        unfold w64Max
        split <;> word⟩
    have Hapg1 : (∀ e0, some e = some e0 →
        uint.Z e0.Index' ≤ uint.Z s.logst.applying) →
        s1.logst.applying = s.logst.applying := by
      intro Hle
      rw [← Hs1]
      have H1 := Hle e rfl
      show w64Max s.logst.applying (w64Max e.Index' s.logst.applied) = s.logst.applying
      unfold w64Max
      split <;> split <;> word
    have Hpk1 : s.role = .preCandidate → PreKeep s s1 := by
      rw [← Hs1]
      exact fun _ => ⟨rfl, rfl, rfl, fun h => h, by
        show uint.Z s.logst.applied ≤ uint.Z (w64Max e.Index' s.logst.applied)
        unfold w64Max
        split <;> word⟩
    have Hst1 : StepCD c id B m s [] s1 := by
      rw [← Hs1]; exact stepCD_appliedTo c id m s e.Index' sz Hty (Hlast e He).1 Hcm.1.2.1
    have Happ1 : s1.logst.applied = w64Max e.Index' s.logst.applied := by rw [← Hs1]; rfl
    have Hps1 : toPState s1 = toPState s := by rw [← Hs1]; rfl
    have Hrole1 : s1.role = s.role := by rw [← Hs1]
    have Happ2' : uint.Z e.Index' ≤ uint.Z (w64Max e.Index' s.logst.applied) := by
      unfold w64Max
      split <;> word
    iapply HΦ $$ %interface.nil %s2 %B %recv
    iframe Hphys
    rcases Hls with ⟨rfl, rfl, rfl⟩ |
      ⟨-, Hrl, Hrecv, Hrl1, Hst2, Hfr2, Hapg2, Happl2, Hwf2, HB1, HB2, HB3, Hbound⟩
    · -- nothing more
      isplitr
      · ipureintro; exact Hwf1
      isplitr
      · ipureintro; exact ⟨Hfr1, Hapg1⟩
      isplitr
      · ipureintro; exact Hpk1
      isplitr
      · ipureintro; exact ⟨by simp, by simp⟩
      isplitr
      · ipureintro; rw [Hps1]; exact ⟨Int.le_refl _, by omega, HL⟩
      isplitl [Hrcb]
      · iintro %Hlt; iapply Hrcb; ipureintro; exact Hlt
      ipureintro
      refine ⟨Hst1, .inr ⟨e, by simp, Happ1⟩, fun e0 He0 => ?_, rfl⟩
      have He0' : e = e0 := by simpa using He0
      subst He0'
      rw [Happ1]; exact Happ2'
    · -- the leave proposed
      isplitr
      · ipureintro; exact Hwf2
      isplitr
      · ipureintro; exact ⟨LocalFrame.trans' Hfr1 Hfr2, fun Hle => Hapg2.trans (Hapg1 Hle)⟩
      isplitr
      · ipureintro
        exact fun h => absurd (Hrl.symm.trans (Hrole1.trans h)) (by decide)
      isplitr
      · ipureintro; exact ⟨Hrecv, Hrl1⟩
      isplitr
      · ipureintro; rw [← Hps1]; exact ⟨HB1, HB2, HB3⟩
      isplitl [Hrcb]
      · iintro %Hlt; iapply Hrcb; ipureintro; exact Hlt
      ipureintro
      refine ⟨StepCD.trans_leave Hst1 Hst2 Hrl (by rw [Hps1]) Happl2 Hbound,
        .inr ⟨e, by simp, Happl2.trans Happ1⟩, fun e0 He0 => ?_, rfl⟩
      have He0' : e = e0 := by simpa using He0
      subst He0'
      rw [Happl2, Happ1]; exact Happ2'

end StepProof

end branches

end EtcdGrove
end Perennial
