/-
The refinement of the dynamic model (2026-10-14, reconfiguration stage B5): the ghost state, in
its dynamic mode (`RaftNames.reDyn = some (DynCfg.ofFold dec c0 h0)`: the configuration of a
committed prefix is its fold from `c0`), follows `StepR` steps with configurations changing by
applied conf entries (`Adm := AdmFold dec c0`, with the snapshot prefixes' records, below).

* `DynCfg.ofFold dec c0 h0`: the mode's configurations, `cfgFold dec c0`, with `fold_adjacent`
  for the one fact the ghost state uses (`DynCfg.adj`).
* `ownRaftGhostR γ dec c0 id r`: the node's ghost state in the dynamic mode (`ownRaftGhost ... true`)
  over `r.p`, with `RInv dec c0 r` (stage B3's invariant: the configuration is the fold of the
  full log's first `cidx` entries, I1, I3, the campaign guard), the records of `r.fp` (so it is
  the ghost state's full prefix, `FullOk_unique`). (2026-10-31, durability R5: no longer a
  candidate's campaign record, which may be pending.)
* `ownRaftGhostR_env`: the step environment (`dynEnv`) the configuration-reading rules take,
  from `RInv`.
* `ownRaftGhostR_stepR`: every `StepR` derivation updates it, given the messages it consumed,
  their read credits, and the records of every snapshot prefix the derivation may restore
  (`S`, see below).

**The snapshot prefixes.** `StepR.snapRestore` takes the restored node's new full prefix `fp'`
from the rule, constrained only by `FullOk` and `Adm fp' cs'` (B3). A run whose `fp'` is not the
committed prefix the snapshot covers is not one of a real system (A3: the snapshot's
`ConfState` is its prefix's configuration, and later decoded conf entries depend on the prefix),
and the ghost state cannot follow it. The refinement therefore takes, for the derivation's
admissible prefixes `S`, their records (`□ ∀ fp, ⌜S fp⌝ -∗ logRecs γ base0 fp`): with records and
`FullOk`, `fp'` is the sender's committed prefix. The code (stage B7) chooses `fp'` from the
message's knowledge and supplies them.
-/
module

public import Proof.go_etcd_io.raft.v3.Protocol.Refinement
public import Proof.go_etcd_io.raft.v3.Protocol.StepRInv

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI GMap go_etcd_io.raft.v3

section dyn
variable [GooseExts]

/-- The dynamic configurations of a base decoder and an initial configuration with `CfgOk`: the
fold of the base decoder over the decisions witnessed (`effDec`, 2026-10-28). -/
def DynCfg.ofFold (dec : CCDec) (c0 : CCState) (h0 : CfgOk c0) : DynCfg where
  fold Md P := (cfgFold (effDec dec Md) c0 P).map (fun s => s.cfg)
  mono := by
    intro Md Md' P c hM h
    cases e : cfgFold (effDec dec Md) c0 P with
    | none => simp only [e, Option.map_none] at h; cases h
    | some s =>
      simp only [e, Option.map_some] at h
      simp only [cfgFold_mono (effDec_mono dec hM) e, Option.map_some]
      exact h
  adj := by
    intro Md P1 P2 c1 c2 hp hc h1 h2
    obtain ⟨M, rfl⟩ := hp
    cases e1 : cfgFold (effDec dec Md) c0 P1 with
    | none => rw [e1] at h1; cases h1
    | some s1 =>
      cases e2 : cfgFold (effDec dec Md) c0 (P1 ++ M) with
      | none => rw [e2] at h2; cases h2
      | some s2 =>
        rw [e1] at h1; rw [e2] at h2
        simp only [Option.map_some, Option.some.injEq] at h1 h2
        subst h1 h2
        refine fold_adjacent (effDec dec Md) (P1 ++ M) P1.length (P1 ++ M).length c0 s1 s2
          (by simp) ?_ h0 ?_ ?_
        · rw [List.take_length, List.take_left']
          · exact hc
          · rfl
        · rw [List.take_left']; exact e1; rfl
        · rw [List.take_length]; exact e2

/-- The configurations the dynamic model admits after a prefix: its fold (A3), among the
prefixes `S` (whose records the refinement takes, see the file header). -/
def AdmS (dec : CCDec) (c0 : CCState) (S : List EntryM → Prop) (l : List EntryM)
    (cs : CCState) : Prop :=
  AdmFold dec c0 l cs ∧ S l

theorem toNat_uZ (w : w64) : (uint.Z w).toNat = uint.nat w := by
  have := rUnat_eq w; omega

theorem cfgAt_of_fold {γ : RaftNames} {dec : CCDec} {M : DecMap} {c0 : CCState} {h0 : CfgOk c0}
    (HD : γ.dyn = some (DynCfg.ofFold dec c0 h0)) {P : List EntryM} {s : CCState}
    (h : cfgFold (effDec dec M) c0 P = some s) : CfgAt γ M P s.cfg :=
  CfgAt.of_dyn HD (by simp [DynCfg.ofFold, h])

/-- The base decoder is below its decisions' fold. -/
theorem effDec_base (dec : CCDec) (M : DecMap) : DecLe dec (effDec dec M) := by
  intro pre e x h
  unfold effDec; rw [h]

theorem reDyn_of {γ : RaftNames} {D : DynCfg} (HD : γ.dyn = some D) : γ.reDyn ≠ none := by
  intro h; rw [RaftNames.dyn_none h] at HD; cases HD

/-- What an `MsgApp` tells its receiver for I1 (`AppKnow`), from the sender's log `fp ++ l` the
message knows (its previous term, the batch in it, I1 at `Commit`) and log matching with the
receiver's full log (their records agree). -/
theorem appKnow_pure (r : RState) (m : Msg) (bL : entryID) (fp l : List EntryM)
    (HwR : PlogWf base0 r.full) (Hpay : AppPayloadOk m)
    (Hprev : plogTermAt bL l m.index = some m.logterm)
    (Hpre : m.entries <+: plogFrom bL l (m.index + W64 1))
    (Hfl : FullOk bL fp) (HwF : PlogWf base0 (fp ++ l))
    (HI1 : ConfI1 (fp ++ l) (uint.nat m.commit))
    (HRA : RecsAgree base0 r.full base0 (fp ++ l)) : AppKnow r m := by
  obtain ⟨hb, hle⟩ := plogTermAt_some_range _ _ _ _ Hprev
  have hfl : (fp.length : Int) = uint.Z bL.index' := Hfl.1
  have hin := rUnat_eq m.index
  obtain ⟨t, ht'⟩ := Hpre
  have hnw := Hpay.2
  have hnw1 : uint.Z (m.index + W64 1) = uint.Z m.index + 1 := by word
  unfold plogFrom at ht'
  rw [hnw1] at ht'
  have hsplit : fp ++ l = ((fp ++ l).take (uint.nat m.index) ++ m.entries) ++ t := by
    have hk : uint.nat m.index =
        fp.length + (uint.Z m.index + 1 - uint.Z bL.index' - 1).toNat := by omega
    rw [hk, List.take_length_add_append, List.append_assoc, List.append_assoc, ht',
      List.take_append_drop]
  have hiF : uint.nat m.index ≤ (fp ++ l).length := by
    unfold plogLastIndexZ at hle; rw [List.length_append]; omega
  have htl : ((fp ++ l).take (uint.nat m.index)).length = uint.nat m.index := by
    rw [List.length_take]; omega
  have hGpre : ((fp ++ l).take (uint.nat m.index) ++ m.entries) <+: fp ++ l :=
    ⟨t, hsplit.symm⟩
  refine ⟨Hpay, (fp ++ l).take (uint.nat m.index) ++ m.entries, ?_, ?_, ?_, ?_, ?_⟩
  · rw [List.length_append, htl]
  · exact List.drop_left' htl
  · have := HI1; rw [hsplit] at this; exact this.prefix
  · intro hpos
    obtain ⟨e, he⟩ : ∃ e, (fp ++ l)[uint.nat m.index - 1]? = some e :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    refine ⟨e, ?_, ?_⟩
    · rw [List.getElem?_append_left (by omega), List.getElem?_take, ite_eq_left (by omega)]
      exact he
    · have h1 := full_term_at bL fp l m.index Hfl hb
      rw [Hprev] at h1
      rw [plogTermAt_lookup base0 (fp ++ l) m.index (uint.nat m.index - 1) e he
        (by rw [base0_index]; push_cast; omega)] at h1
      exact Option.some.inj h1
  · intro k e e' h1 h2 heq
    have hkG : k < ((fp ++ l).take (uint.nat m.index) ++ m.entries).length :=
      (List.getElem?_eq_some_iff.mp h2).1
    have h2' : (fp ++ l)[k]? = some e' := by
      obtain ⟨M, hM⟩ := hGpre
      rw [← hM, List.getElem?_append_left hkG]; exact h2
    have hkR : k < r.full.length := (List.getElem?_eq_some_iff.mp h1).1
    have hrng := PlogWf_range _ _ HwR
    unfold plogLastIndexZ at hrng; rw [base0_index] at hrng
    have HW : uint.Z (W64 ((k : Int) + 1)) = (k : Int) + 1 :=
      uint_Z_W64 _ (by omega) (by omega)
    have hR : plogTermAt base0 r.full (W64 ((k : Int) + 1)) = some e.Term' :=
      plogTermAt_lookup _ _ _ k e h1 (by rw [HW, base0_index]; push_cast; omega)
    have hF : plogTermAt base0 (fp ++ l) (W64 ((k : Int) + 1)) = some e'.Term' :=
      plogTermAt_lookup _ _ _ k e' h2' (by rw [HW, base0_index]; push_cast; omega)
    have Htk := full_take_eq_pure r.full (fp ++ l) (W64 ((k : Int) + 1)) HwR HwF HRA
      (by rw [hR]; rfl) (by rw [hR, hF, heq])
    rw [HW, show ((k : Int) + 1).toNat = k + 1 by omega] at Htk
    rw [Htk, take_of_prefix hGpre (by omega)]

/-- No `MsgApp` received. -/
theorem noApp1 {dec : CCDec} {c0 : CCState} {m : Msg} (h : m.ty ≠ .app) :
    ∀ (r1 : RState) (m' : Msg), m' ∈ [m] → m'.ty = .app → RInv dec c0 r1 → AppKnow r1 m' := by
  intro r1 m' hm hty _
  rw [List.mem_singleton] at hm; subst hm; exact absurd hty h

theorem noApp0 {dec : CCDec} {c0 : CCState} :
    ∀ (r1 : RState) (m' : Msg), m' ∈ ([] : List Msg) → m'.ty = .app → RInv dec c0 r1 →
      AppKnow r1 m' := by
  intro r1 m' hm; cases hm

end dyn

section ghost
variable [GooseExts]
variable {GF : BundledGFunctors} [AllG GF] [ReceiptGS GF] [InvGS GF]

/-- A node's ghost state in the dynamic mode, with its reconfiguration state (see the file
header). -/
def ownRaftGhostR (γ : RaftNames) (dec : CCDec) (c0 : CCState) (id : w64) (r : RState) :
    IProp GF :=
  iprop(ownRaftGhost γ id r.p true ∗ ⌜RInv dec c0 r⌝ ∗ logRecs γ base0 r.fp)

/-- The step environment, from `RInv`: the full prefix, I1, the configuration index (the
commit index at a candidate, `RInv.cand_cfg`), I3 at a leader. (2026-10-28, stage U0: with no
snapshot pending; since stage U3 the configuration is the fold of the full log's prefix also with
one pending, `RInv.cfg`.) -/
theorem ownRaftGhostR_env (γ : RaftNames) (dec : CCDec) (M : DecMap) (c0 : CCState) (h0 : CfgOk c0)
    (HD : γ.dyn = some (DynCfg.ofFold dec c0 h0)) (id : w64) (r : RState)
    (HI : RInv (effDec dec M) c0 r) :
    ⊢ decLb (GF := GF) γ M -∗ logRecs γ base0 r.fp -∗
      dynEnv γ id r.cfg.cfg r.p := by
  -- PORT(durability stage II): proof (restated: no candidate campaign record (durability R5))
  sorry

/-- A node's log is well formed, with records (a persistent accessor). -/
theorem ownRaftGhost_logRecs (γ : RaftNames) (id : w64) (s : PState) (md : Bool) :
    ⊢ ownRaftGhost (GF := GF) γ id s md -∗ ⌜PlogWf s.base s.log⌝ ∗ logRecs γ s.base s.log := by
  unfold ownRaftGhost
  iintro ⟨%γv, %voted, %kl, H⟩
  iNamed H
  ihave %Hw := ownLogGhost_wf γ id s kl $$ Hlg
  icases ownLogGhost_recs γ id s kl $$ Hlg with ⟨-, #Hr⟩
  iframe Hr
  ipureintro; exact Hw

/-- What a received `MsgApp` tells the dynamic receiver (`AppKnow`), from its knowledge. -/
theorem appKnow_of_msg (γ : RaftNames) (r : RState) (m : Msg) (Hty : m.ty = .app)
    (Hdyn : γ.reDyn ≠ none) (HwR : PlogWf base0 r.full) :
    ⊢ isMessage (GF := GF) γ m -∗ logRecs γ base0 r.full -∗ ⌜AppKnow r m⌝ := by
  iintro #Hm #HrR
  icases isMessage_app_inv γ m Hty $$ Hm with
    ⟨%Hpay, -, ⟨%bL, %l, %fp, #Hp, %Hpl, #Hpf, -, -, #Hi1⟩, -⟩
  icases dynOn_elim γ _ Hdyn $$ Hi1 with %HI1
  icases lpfull_fp γ _ _ _ _ _ $$ Hpf with ⟨#Hfrp, %Hfl⟩
  icases leadPrefix_wf γ _ _ _ _ $$ Hp with ⟨-, #Hrlp⟩
  ihave #HrF := logRecs_full γ bL fp l Hfl.1 $$ Hfrp Hrlp
  icases logRecs_agree γ base0 r.full base0 (fp ++ l) $$ HrR HrF with %HRA
  ipureintro
  exact appKnow_pure r m bL fp l HwR Hpay Hpl.1 Hpl.2 Hfl.1 (full_wf _ _ _ Hfl.1 Hfl.2.1)
    (by rw [← toNat_uZ]; exact HI1) HRA


/-- The dynamic refinement (2026-10-14, stage B5): a `StepR` derivation at the dynamic
configurations (`AdmS dec c0 S`: the fold of the prefix, among `S`) updates the node's
dynamic ghost state, given the messages it consumed with their read credits and the records of
the prefixes `S` (see the file header). With the commit invariant's registry half open
(2026-10-14, stage R: `regsOwn` threaded through, for the commits). -/
theorem ownRaftGhostR_stepR_in (γ : RaftNames) (decB : CCDec) (M : DecMap) (c0 : CCState) (h0 : CfgOk c0)
    (HD : γ.dyn = some (DynCfg.ofFold decB c0 h0)) (S : List EntryM → Prop)
    (id : w64) (B : Int) (HB : B < 2 ^ 64) (r : RState) (recv : List Msg) (r' : RState) :
    StepR (AdmS (effDec decB M) c0 S) (effDec decB M) id B r recv r' →
    ⊢ ⧖ (B.toNat - γ.reBoot.length) -∗ decLb (GF := GF) γ M -∗ regsOwn γ -∗ (□ ∀ (fp : List EntryM), ⌜S fp⌝ -∗ logRecs (GF := GF) γ base0 fp) -∗
      ([∗list] m ∈ recv, isMessage γ m) -∗ rdCred γ (rdCount recv) -∗ msgsTks γ recv -∗
      ownRaftGhostR γ (effDec decB M) c0 id r ={⊤ \ ↑(raftRegN γ)}=∗
      regsOwn γ ∗ ownRaftGhostR γ (effDec decB M) c0 id r' := by
  -- PORT(durability stage II): proof (a definition or a statement it uses changed (durability I-1))
  sorry

/-- The dynamic refinement (see `ownRaftGhostR_stepR_in`), at `⊤`, given one later credit
(2026-10-14, stage R): the commit invariant's registry half opened around the step. -/
theorem ownRaftGhostR_stepR (γ : RaftNames) (decB : CCDec) (M : DecMap) (c0 : CCState) (h0 : CfgOk c0)
    (HD : γ.dyn = some (DynCfg.ofFold decB c0 h0)) (S : List EntryM → Prop)
    (id : w64) (B : Int) (HB : B < 2 ^ 64) (r : RState) (recv : List Msg) (r' : RState) :
    StepR (AdmS (effDec decB M) c0 S) (effDec decB M) id B r recv r' →
    ⊢ ⧖ (B.toNat - γ.reBoot.length) -∗ decLb (GF := GF) γ M -∗
      (□ ∀ (fp : List EntryM), ⌜S fp⌝ -∗ logRecs (GF := GF) γ base0 fp) -∗
      ([∗list] m ∈ recv, isMessage γ m) -∗ rdCred γ (rdCount recv) -∗ msgsTks γ recv -∗ £ 1 -∗
      ownRaftGhostR γ (effDec decB M) c0 id r ={⊤}=∗ ownRaftGhostR γ (effDec decB M) c0 id r' := by
  intro Hstep
  iintro #Hrc #HM #HS Hrecv Hcr Htk Hlc Hown
  ihave #Hinv : raftCommitInv γ $$ [Hown]
  · iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, -⟩
    iapply ownRaftGhost_inv_md γ id r.p $$ Hg
  iapply regs_open γ iprop(([∗list] m ∈ recv, isMessage (GF := GF) γ m) ∗
      rdCred γ (rdCount recv) ∗ msgsTks γ recv ∗ ownRaftGhostR γ (effDec decB M) c0 id r)
      (ownRaftGhostR γ (effDec decB M) c0 id r')
    $$ Hinv Hlc [] [Hrecv Hcr Htk Hown]
  · iintro Hregs ⟨Hrecv, Hcr, Htk, Hown⟩
    iapply ownRaftGhostR_stepR_in γ decB M c0 h0 HD S id B HB r recv r' Hstep $$ Hrc HM Hregs HS Hrecv
      Hcr Htk Hown
  · iframe Hrecv Hcr Htk Hown

end ghost

end EtcdGrove
end Perennial
