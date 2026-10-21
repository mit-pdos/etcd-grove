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

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section branches
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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
  obtain ⟨Hsn, Ha1⟩ := hd.2.2.2.1 Hty
  refine ⟨max g.cidx (uint.nat (w64Max idx s.logst.applied)), .inr ⟨Hty, rfl⟩, ?_⟩
  have Hr : rOf { s with logst := logAppliedTo s.logst idx sz }
      { g with cidx := max g.cidx (uint.nat (w64Max idx s.logst.applied)) } =
      { rOf s g with applied := w64Max idx s.logst.applied,
                     cidx := max (rOf s g).cidx (uint.nat (w64Max idx s.logst.applied)) } := by
    unfold rOf pciR
    rw [toPState_logAppliedTo]
    simp [logAppliedTo]
  rw [Hr]
  refine StepR.advance (rOf s g) (w64Max idx s.logst.applied) (by simp [rOf, Hsn]) ?_ ?_ Ha1
  · show uint.Z s.logst.applied ≤ uint.Z (w64Max idx s.logst.applied)
    unfold w64Max; split <;> word
  · show uint.Z (w64Max idx s.logst.applied) ≤ uint.Z s.logst.committed
    unfold w64Max; split <;> word

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

moving `applied` (`logAppliedTo`). Nothing the protocol sees changes: `StepC.refl`. The
premise is `appliedTo`'s: the last entry is committed. -/
theorem wp_Step_MsgStorageApplyResp (_P : raft.Step.Postulates (GF := GF) (hG := hG))
    (_Q : raft.Step.ReplPbPostulates (GF := GF) (hG := hG))
    (c : CfgM) (r : Loc) (id : w64) (s : NState) (ml : Loc) (m : MessageM)
    (sn : Option SnapshotM) (ctx : List w8) (rs : List Loc)
    (ents : List EntryM) :
    m.Type' = MsgStorageApplyResp →
    m.Term' = W64 0 →
    (∀ e, ents.getLast? = some e → uint.Z e.Index' ≤ uint.Z s.logst.committed ∧
      uint.Z e.Index' ≤ uint.Z s.logst.applying) →
    NStateWf s →
    -- (2026-10-14, stage B7) `appliedTo`'s auto-leave branch is not taken
    (c.autoLeave = true → s.role ≠ .leader) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
        "Hm" ∷ msgIn ml DFrac.discard ⟨m, ents, sn, ctx, rs⟩ }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #ml))
    {{ (err : GoInterface) (s' : NState), RET #err;
        "Hphys" ∷ ownRaftPhysCV c c.voters r id s' ∗
        "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
        "%Hframe" ∷ ⌜LocalFrame s s' ∧
                     ((∀ e, ents.getLast? = some e → uint.Z e.Index' ≤ uint.Z s.logst.applying) →
                      s'.logst.applying = s.logst.applying)⌝ ∗
        "%Hrefines" ∷ ⌜StepCD c id B m s [] s'⌝ ∗
        -- (2026-10-14, stage B7) `applied` moves at most to the last entry's index
        "%Happ" ∷ ⌜s'.logst.applied = s.logst.applied ∨
          ∃ e, ents.getLast? = some e ∧ s'.logst.applied = w64Max e.Index' s.logst.applied⌝ ∗
        -- (D19i part 1) and at least to it
        "%Happ2" ∷ ⌜∀ e, ents.getLast? = some e → uint.Z e.Index' ≤ uint.Z s'.logst.applied⌝ ∗
        "%Herr" ∷ ⌜err = interface.nil⌝ }} := by
  intro Hty Hterm Hlast Hwf Hal
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
    iapply HΦ $$ %interface.nil %s
    iframe Hphys
    ipureintro
    exact ⟨Hwf, ⟨⟨rfl, Int.le_refl _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Int.le_refl _⟩, fun _ => rfl⟩,
      StepCD.frame (.refl _) (RFrame.refl _), .inl rfl, fun _ h => by simp at h, rfl⟩
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
    wp_apply _P.appliedTo c r id s e.Index' sz (Hlast e He).1
      (fun h => absurd (Hlast e He).2 (Int.not_le.2 h)) Hal Hq0.1
      (fun h => absurd (Hq0.2.symm.trans h) (by decide))
      (fun _ _ h => absurd (Hlast e He).2 (Int.not_le.2 h))
      (fun _ _ h => absurd (Hlast e He).2 (Int.not_le.2 h))
      (fun h => absurd (Hq0.2.symm.trans h) (by decide)) $$ [$Hphys] as Hphys
    try wp_auto
    wp_apply wp_GetEntries_ro _Q $$ [$Hm] as %es5 ⟨#Hes5, Hm⟩
    wp_apply _P.payloadsSize $$ [$Hes5] as %psz -
    wp_apply _P.reduceUncommittedSize $$ [$Hphys] as Hphys
    iapply HΦ $$ %interface.nil %_
    iframe Hphys
    ipureintro
    refine ⟨Hwf, ⟨⟨rfl, Int.le_refl _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩, fun Hle => ?_⟩, ?_,
      .inr ⟨e, by simp, rfl⟩, ?_, rfl⟩
    · show uint.Z s.logst.applied ≤ uint.Z (w64Max e.Index' s.logst.applied)
      unfold w64Max
      split <;> word
    · have H1 := Hle e (by simp)
      show w64Max s.logst.applying (w64Max e.Index' s.logst.applied) = s.logst.applying
      unfold w64Max
      split <;> split <;> word
    · exact stepCD_appliedTo c id m s e.Index' sz Hty (Hlast e He).1 Hcm.1.2.1
    · intro e0 He0
      have He0' : e = e0 := by simpa using He0
      subst He0'
      show uint.Z e.Index' ≤ uint.Z (w64Max e.Index' s.logst.applied)
      unfold w64Max
      split <;> word

end StepProof

end branches

end EtcdGrove
end Perennial
