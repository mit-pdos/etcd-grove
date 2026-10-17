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
  the ghost state's full prefix, `FullOk_unique`), and a candidate's campaign record of its full
  log at its commit index.
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
variable [FfiSyntax]

/-- The dynamic configurations of a decoder and an initial configuration with `CfgOk`. -/
def DynCfg.ofFold (dec : CCDec) (c0 : CCState) (h0 : CfgOk c0) : DynCfg where
  fold P := (cfgFold dec c0 P).map (fun s => s.cfg)
  adj := by
    intro P1 P2 c1 c2 hp hc h1 h2
    obtain ⟨M, rfl⟩ := hp
    cases e1 : cfgFold dec c0 P1 with
    | none => rw [e1] at h1; cases h1
    | some s1 =>
      cases e2 : cfgFold dec c0 (P1 ++ M) with
      | none => rw [e2] at h2; cases h2
      | some s2 =>
        rw [e1] at h1; rw [e2] at h2
        simp only [Option.map_some, Option.some.injEq] at h1 h2
        subst h1 h2
        refine fold_adjacent dec (P1 ++ M) P1.length (P1 ++ M).length c0 s1 s2
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

theorem cfgAt_of_fold {γ : RaftNames} {dec : CCDec} {c0 : CCState} {h0 : CfgOk c0}
    (HD : γ.dyn = some (DynCfg.ofFold dec c0 h0)) {P : List EntryM} {s : CCState}
    (h : cfgFold dec c0 P = some s) : CfgAt γ P s.cfg :=
  CfgAt.of_dyn HD (by simp [DynCfg.ofFold, h])

theorem reDyn_of {γ : RaftNames} {D : DynCfg} (HD : γ.dyn = some D) : γ.reDyn ≠ none := by
  intro h; rw [RaftNames.dyn_none h] at HD; cases HD

/-- `full_take_eq`'s pure core: two full logs whose records agree (`RecsAgree`) and that have
the same term at `c` have the same first `c` entries. -/
theorem full_take_eq_pure (F1 F2 : List EntryM) (c : w64) (Hw1 : PlogWf base0 F1)
    (Hw2 : PlogWf base0 F2) (HRA : RecsAgree base0 F1 base0 F2)
    (Hs : (plogTermAt base0 F1 c).isSome) (Heq : plogTermAt base0 F1 c = plogTermAt base0 F2 c) :
    F1.take (uint.Z c).toNat = F2.take (uint.Z c).toNat := by
  have Hm : ∀ j : w64, uint.Z j ≤ uint.Z c → plogTermAt base0 F1 j = plogTermAt base0 F2 j := by
    intro j Hj
    have := uint_Z_nonneg j
    exact plog_match_down _ _ _ _ c (PlogWf_wfR _ _ Hw1) (PlogWf_wfR _ _ Hw2) HRA Hs Heq j
      (by rw [base0_index]; omega) (by rw [base0_index]; omega) Hj
  obtain ⟨x, Hx⟩ := Option.isSome_iff_exists.mp Hs
  have Hc1 := (plogTermAt_some_range _ _ _ _ Hx).2
  rw [Heq] at Hx
  have Hc2 := (plogTermAt_some_range _ _ _ _ Hx).2
  unfold plogLastIndexZ at Hc1 Hc2; rw [base0_index] at Hc1 Hc2
  apply List.ext_getElem?
  intro k
  rw [List.getElem?_take, List.getElem?_take]
  by_cases Hk : k < (uint.Z c).toNat
  · simp only [Hk, ite_true]
    obtain ⟨e1, He1⟩ : ∃ e, F1[k]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨e2, He2⟩ : ∃ e, F2[k]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    rw [He1, He2]
    have Hi1 := Hw1 _ _ He1
    have Hi2 := Hw2 _ _ He2
    rw [base0_index] at Hi1 Hi2
    have := uint_Z_lt c
    have HW : uint.Z (W64 ((k : Int) + 1)) = (k : Int) + 1 :=
      uint_Z_W64 _ (by omega) (by omega)
    have Ht := Hm (W64 ((k : Int) + 1)) (by rw [HW]; omega)
    rw [plogTermAt_lookup _ _ _ k e1 He1 (by rw [HW, base0_index]; push_cast; omega),
      plogTermAt_lookup _ _ _ k e2 He2 (by rw [HW, base0_index]; push_cast; omega)] at Ht
    simp only [Option.some.injEq] at Ht
    obtain ⟨H, -⟩ := HRA k k e1 e2 He1 He2 (by rw [base0_index]; omega)
      (by rw [base0_index]; omega) Ht (uint_Z_inj.mp (by omega))
    rw [H]
  · simp only [Hk, ite_false]

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
variable [FfiSyntax]
variable {GF : BundledGFunctors} [AllG GF] [InvGS GF]

/-- A node's ghost state in the dynamic mode, with its reconfiguration state (see the file
header). -/
def ownRaftGhostR (γ : RaftNames) (dec : CCDec) (c0 : CCState) (id : w64) (r : RState) :
    IProp GF :=
  iprop(ownRaftGhost γ id r.p true ∗ ⌜RInv dec c0 r⌝ ∗ logRecs γ base0 r.fp ∗
    (∀ (_ : r.p.role = .candidate), isCampK γ id r.p.term r.full r.p.commit))

/-- The step environment, from `RInv`: the full prefix, I1, the configuration index (the
commit index at a candidate, `RInv.cand_cfg`), I3 at a leader. -/
theorem ownRaftGhostR_env (γ : RaftNames) (dec : CCDec) (c0 : CCState) (h0 : CfgOk c0)
    (HD : γ.dyn = some (DynCfg.ofFold dec c0 h0)) (id : w64) (r : RState)
    (HI : RInv dec c0 r) :
    ⊢ logRecs (GF := GF) γ base0 r.fp -∗
      (∀ (_ : r.p.role = .candidate), isCampK γ id r.p.term r.full r.p.commit) -∗
      dynEnv γ id r.cfg.cfg r.p := by
  iintro #Hfr #Hc
  unfold dynEnv
  iright
  isplitr
  · ipureintro; exact reDyn_of HD
  have Hcl : r.cidx < 2 ^ 64 := by
    have := HI.cidx_commit; have := rUnat_eq r.p.commit; have := uint_Z_lt r.p.commit; omega
  by_cases hc : r.p.role = .candidate
  · iexists r.fp, r.p.commit
    iframe Hfr
    isplitr
    · ipureintro
      refine ⟨HI.full, ?_, Int.le_refl _, ?_, ?_, fun _ => rfl⟩
      · rw [toNat_uZ]; exact HI.i1
      · rw [toNat_uZ]; exact cfgAt_of_fold HD (HI.cand_cfg hc).1
      · intro hl; rw [hc] at hl; cases hl
    · rw [show r.fp ++ r.p.log = r.full from rfl]; iexact Hc
  · iexists r.fp, (W64 (r.cidx : Int))
    have Hw : (uint.Z (W64 (r.cidx : Int))).toNat = r.cidx := by
      rw [uint_Z_W64 _ (by omega) (by omega)]; simp
    iframe Hfr
    isplitr
    · ipureintro
      refine ⟨HI.full, ?_, ?_, ?_, ?_, fun h => absurd h hc⟩
      · rw [toNat_uZ]; exact HI.i1
      · rw [uint_Z_W64 _ (by omega) (by omega)]
        have := HI.cidx_commit; have := rUnat_eq r.p.commit; omega
      · rw [Hw]; exact cfgAt_of_fold HD HI.cfg
      · intro hl; rw [Hw]; exact HI.leader_drop_cidx hl
    · iintro %h; exact absurd h hc

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

/-- Closing a step that keeps the full prefix, and a candidate's campaign record. -/
theorem ownRaftGhostR_close (γ : RaftNames) (dec : CCDec) (c0 : CCState) (id : w64)
    (r r' : RState) :
    ⊢ ⌜RInv dec c0 r'⌝ -∗ ⌜r'.fp = r.fp⌝ -∗
      ⌜r'.p.role = .candidate →
        r.p.role = .candidate ∧ r'.p.term = r.p.term ∧ r'.p.log = r.p.log ∧
          r'.p.commit = r.p.commit⌝ -∗
      ownRaftGhost (GF := GF) γ id r'.p true -∗ logRecs γ base0 r.fp -∗
      (∀ (_ : r.p.role = .candidate), isCampK γ id r.p.term r.full r.p.commit) -∗
      ownRaftGhostR γ dec c0 id r' := by
  iintro %HI' %Hfp %Hcand Hg #Hfr #Hc
  unfold ownRaftGhostR
  iframe Hg
  isplitr; · ipureintro; exact HI'
  isplitr; · rw [Hfp]; iexact Hfr
  iintro %hc
  obtain ⟨hc0, ht, hl, hcm⟩ := Hcand hc
  ihave #Hk := Hc $$ %hc0
  unfold RState.full
  rw [Hfp, ht, hl, hcm]
  iexact Hk


/-- The dynamic refinement (2026-10-14, stage B5): a `StepR` derivation at the dynamic
configurations (`AdmS dec c0 S`: the fold of the prefix, among `S`) updates the node's
dynamic ghost state, given the messages it consumed with their read credits and the records of
the prefixes `S` (see the file header). With the commit invariant's registry half open
(2026-10-14, stage R: `regsOwn` threaded through, for the commits). -/
theorem ownRaftGhostR_stepR_in (γ : RaftNames) (dec : CCDec) (c0 : CCState) (h0 : CfgOk c0)
    (HD : γ.dyn = some (DynCfg.ofFold dec c0 h0)) (S : List EntryM → Prop)
    (id : w64) (r : RState) (recv : List Msg) (r' : RState) :
    StepR (AdmS dec c0 S) dec id r recv r' →
    ⊢ regsOwn γ -∗ (□ ∀ (fp : List EntryM), ⌜S fp⌝ -∗ logRecs (GF := GF) γ base0 fp) -∗
      ([∗list] m ∈ recv, isMessage γ m) -∗ rdCred γ (rdCount recv) -∗
      ownRaftGhostR γ dec c0 id r ={⊤ \ ↑raftRegN}=∗
      regsOwn γ ∗ ownRaftGhostR γ dec c0 id r' := by
  intro Hstep
  induction Hstep with
  | refl r =>
    iintro Hregs _ _ - Hown
    imodintro; iframe Hregs Hown
  | trans r0 m1 r1 m2 r2 _ _ IH1 IH2 =>
    iintro Hregs #HS Hrecv Hcr Hown
    icases (BigSepL.bigSepL_append (Φ := fun _ m => isMessage (GF := GF) γ m)).1 $$ Hrecv with
      ⟨Hr1, Hr2⟩
    rw [rdCount_append]
    icases (rdCred_split γ (rdCount m1) (rdCount m2)).1 $$ Hcr with ⟨Hc1, Hc2⟩
    imod IH1 $$ Hregs HS Hr1 Hc1 Hown with ⟨Hregs, Hown⟩
    iapply IH2 $$ Hregs HS Hr2 Hc2 Hown
  | higherTerm m r h1 h2 h3 =>
    iintro Hregs #HS Hrecv Hcr Hown
    iapply fupd_frame_left
    iframe Hregs
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    imod ownRaftGhost_step_higherTerm γ id m r.p h1 h2 h3 $$ Hrecv Hcr Hg with Hg
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact (HI.frame rfl rfl rfl rfl rfl rfl rfl rfl (Or.inl rfl))
    iintro %h
    exfalso
    revert h
    first
      | (simp [pbecomeFollower]; done)
      | (intro h; rw [preadRespondAll_role] at h; simp at h; simp_all)
      | (intro h; simp_all)
  | grantVote m r h1 h2 h3 h4 h5 h6 =>
    iintro Hregs #HS Hrecv Hcr Hown
    iapply fupd_frame_left
    iframe Hregs
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    imod ownRaftGhost_step_grantVote γ id m r.p h1 h2 h3 h4 h5 h6 $$ Hrecv Hcr Hg with Hg
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact (RInv_stepR (Adm := AdmS dec c0 S) (id := id) (fun _ _ h => h.1) (StepR.grantVote m r h1 h2 h3 h4 h5 h6) (noApp1 (by rw [h1]; decide)) HI)
    dsimp only [psendMsgs, RState.full, pappend]
    iexact Hc
  | rejectVote m r h1 h2 =>
    iintro Hregs #HS Hrecv Hcr Hown
    iapply fupd_frame_left
    iframe Hregs
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    imod ownRaftGhost_step_rejectVote γ id m r.p h1 h2 $$ Hrecv Hcr Hg with Hg
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact (RInv_stepR (Adm := AdmS dec c0 S) (id := id) (fun _ _ h => h.1) (StepR.rejectVote m r h1 h2) (noApp1 (by rw [h1]; decide)) HI)
    dsimp only [psendMsgs, RState.full, pappend]
    iexact Hc
  | recordVote m r h1 h2 h3 h4 =>
    iintro Hregs #HS Hrecv Hcr Hown
    iapply fupd_frame_left
    iframe Hregs
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    imod ownRaftGhost_step_recordVote γ id m r.p h1 h2 h3 h4 $$ Hrecv Hcr Hg with Hg
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact (RInv_stepR (Adm := AdmS dec c0 S) (id := id) (fun _ _ h => h.1) (StepR.recordVote m r h1 h2 h3 h4) (noApp1 (by rw [h1]; decide)) HI)
    dsimp only [psendMsgs, RState.full, pappend]
    iexact Hc
  | lose r h1 h2 =>
    iintro Hregs #HS Hrecv Hcr Hown
    iapply fupd_frame_left
    iframe Hregs
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    imod ownRaftGhost_step_lose γ r.cfg.cfg id r.p h1 h2 $$ Hrecv Hcr Hg with Hg
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact (RInv_stepR (Adm := AdmS dec c0 S) (id := id) (fun _ _ h => h.1) (StepR.lose r h1 h2) noApp0 HI)
    iintro %h
    exfalso
    revert h
    first
      | (simp [pbecomeFollower]; done)
      | (intro h; rw [preadRespondAll_role] at h; simp at h; simp_all)
      | (intro h; simp_all)
  | drain r o' h1 =>
    iintro Hregs #HS Hrecv Hcr Hown
    iapply fupd_frame_left
    iframe Hregs
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    imod ownRaftGhost_step_drain γ id r.p o' h1 $$ Hrecv Hcr Hg with Hg
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact (RInv_stepR (Adm := AdmS dec c0 S) (id := id) (fun _ _ h => h.1) (StepR.drain r o' h1) noApp0 HI)
    dsimp only [psendMsgs, RState.full, pappend]
    iexact Hc
  | takeReads r =>
    iintro Hregs #HS Hrecv Hcr Hown
    iapply fupd_frame_left
    iframe Hregs
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    imod ownRaftGhost_step_takeReads γ id r.p $$ Hrecv Hcr Hg with Hg
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact (RInv_stepR (Adm := AdmS dec c0 S) (id := id) (fun _ _ h => h.1) (StepR.takeReads r) noApp0 HI)
    dsimp only [psendMsgs, RState.full, pappend]
    iexact Hc
  | sendFree r m h1 h2 =>
    iintro Hregs #HS Hrecv Hcr Hown
    iapply fupd_frame_left
    iframe Hregs
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    imod ownRaftGhost_step_sendFree γ id r.p m h1 h2 $$ Hrecv Hcr Hg with Hg
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact (RInv_stepR (Adm := AdmS dec c0 S) (id := id) (fun _ _ h => h.1) (StepR.sendFree r m h1 h2) noApp0 HI)
    dsimp only [psendMsgs, RState.full, pappend]
    iexact Hc
  | abandon r h1 =>
    iintro Hregs #HS Hrecv Hcr Hown
    iapply fupd_frame_left
    iframe Hregs
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    imod ownRaftGhost_step_abandon γ id r.p h1 $$ Hrecv Hcr Hg with Hg
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact (RInv_stepR (Adm := AdmS dec c0 S) (id := id) (fun _ _ h => h.1) (StepR.abandon r h1) noApp0 HI)
    iintro %h
    exfalso
    revert h
    first
      | (simp [pbecomeFollower]; done)
      | (intro h; rw [preadRespondAll_role] at h; simp at h; simp_all)
      | (intro h; simp_all)
  | zeroAck r dst =>
    iintro Hregs #HS Hrecv Hcr Hown
    iapply fupd_frame_left
    iframe Hregs
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    imod ownRaftGhost_step_zeroAck γ id r.p dst $$ Hrecv Hcr Hg with Hg
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact (RInv_stepR (Adm := AdmS dec c0 S) (id := id) (fun _ _ h => h.1) (StepR.zeroAck r dst) noApp0 HI)
    dsimp only [psendMsgs, RState.full, pappend]
    iexact Hc
  | appStale m r h1 h2 h3 h4 h5 h6 =>
    iintro Hregs #HS Hrecv Hcr Hown
    iapply fupd_frame_left
    iframe Hregs
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    ihave #Hm := recv_one γ _ $$ Hrecv
    imod ownRaftGhost_step_app_stale γ id r.p m h1 h3 h4 h5 $$ Hm Hg with Hg
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact (by first | exact RInv_keep _ HI rfl rfl rfl (Or.inr rfl) | exact RInv_keep _ HI rfl rfl rfl (Or.inl rfl) | exact HI.frame rfl rfl rfl rfl rfl rfl rfl rfl (Or.inl rfl))
    iintro %h
    exfalso
    revert h
    first
      | (simp [psendMsgs, padoptLeader]; done)
      | (intro h; rw [preadRespondAll_role] at h; simp at h; simp_all)
      | (intro h; simp_all)
  | appReject m r hint hintterm h1 h2 h3 h4 h5 h6 h7 =>
    iintro Hregs #HS Hrecv Hcr Hown
    iapply fupd_frame_left
    iframe Hregs
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    ihave #Hm := recv_one γ _ $$ Hrecv
    imod ownRaftGhost_step_app_reject γ id r.p m hint hintterm h1 h3 h5 $$ Hm Hg with Hg
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact (by first | exact RInv_keep _ HI rfl rfl rfl (Or.inr rfl) | exact RInv_keep _ HI rfl rfl rfl (Or.inl rfl) | exact HI.frame rfl rfl rfl rfl rfl rfl rfl rfl (Or.inl rfl))
    iintro %h
    exfalso
    revert h
    first
      | (simp [psendMsgs, padoptLeader]; done)
      | (intro h; rw [preadRespondAll_role] at h; simp at h; simp_all)
      | (intro h; simp_all)
  | heartbeat m r cm h1 h2 h3 h4 h5 h6 =>
    iintro Hregs #HS Hrecv Hcr Hown
    iapply fupd_frame_left
    iframe Hregs
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    ihave #Hm := recv_one γ _ $$ Hrecv
    have HRI := (RInv_stepR (Adm := AdmS dec c0 S) (id := id) (fun _ _ h => h.1) (StepR.heartbeat m r cm h1 h2 h3 h4 h5 h6) (noApp1 (by rw [h1]; decide)) HI)
    rw [plogCommitTo_ite] at HRI ⊢
    imod ownRaftGhost_step_heartbeat γ id r.p m _ (ite_cm_cases cm m.commit).1 h1 h2 h4 h3 h5 h6 $$ Hm Hg with Hg
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact HRI
    iintro %h
    exfalso
    revert h
    first
      | (simp [psendMsgs, padoptLeader]; done)
      | (intro h; rw [preadRespondAll_role] at h; simp at h; simp_all)
      | (intro h; simp_all)
  | appResp m r x h1 h2 h3 h4 h5 h6 =>
    iintro Hregs #HS Hrecv Hcr Hown
    iapply fupd_frame_left
    iframe Hregs
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    ihave #Hm := recv_one γ _ $$ Hrecv
    imod ownRaftGhost_step_app_resp γ id r.p m x h1 h3 h4 h5 h6 $$ Hm Hg with Hg
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact (RInv_stepR (Adm := AdmS dec c0 S) (id := id) (fun _ _ h => h.1) (StepR.appResp m r x h1 h2 h3 h4 h5 h6) (noApp1 (by rw [h1]; decide)) HI)
    dsimp only [psendMsgs, RState.full, pappend]
    iexact Hc
  | propForward m r h1 h2 h3 =>
    iintro Hregs #HS Hrecv Hcr Hown
    iapply fupd_frame_left
    iframe Hregs
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    ihave #Hm := recv_one γ _ $$ Hrecv
    imod ownRaftGhost_step_prop_forward γ id r.p m h1 $$ Hm Hg with Hg
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact (RInv_stepR (Adm := AdmS dec c0 S) (id := id) (fun _ _ h => h.1) (StepR.propForward m r h1 h2 h3) (noApp1 (by rw [h1]; decide)) HI)
    dsimp only [psendMsgs, RState.full, pappend]
    iexact Hc
  | snapFastfwd m r cm h1 h2 h3 h4 h5 h6 h7 =>
    iintro Hregs #HS Hrecv Hcr Hown
    iapply fupd_frame_left
    iframe Hregs
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    ihave #Hm := recv_one γ _ $$ Hrecv
    have HRI := (RInv_stepR (Adm := AdmS dec c0 S) (id := id) (fun _ _ h => h.1) (StepR.snapFastfwd m r cm h1 h2 h3 h4 h5 h6 h7) (noApp1 (by rw [h1]; decide)) HI)
    cases cm
    · -- (raft#139) not committed: the stale snapshot's acknowledgement of the commit index
      simp only [Bool.false_eq_true, ↓reduceIte] at HRI ⊢
      rw [show ({ padoptLeader r.p m.src with commit := r.p.commit } : PState) = padoptLeader r.p m.src
        from rfl] at HRI ⊢
      imod ownRaftGhost_step_snap_stale γ id r.p m h1 h3 h4 h5 $$ Hm Hg with Hg
      imodintro
      iunfold ownRaftGhostR
      iframe Hg Hfr
      isplitr
      · ipureintro; exact HRI
      iintro %h
      exfalso
      revert h
      first
        | (simp [psendMsgs, padoptLeader]; done)
        | (intro h; rw [preadRespondAll_role] at h; simp at h; simp_all)
        | (intro h; simp_all)
    simp only [↓reduceIte] at HRI ⊢
    imod ownRaftGhost_step_snap_fastfwd γ id r.p m h1 h3 h4 h5 h6 h7 $$ Hm Hg with Hg
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact HRI
    iintro %h
    exfalso
    revert h
    first
      | (simp [psendMsgs, padoptLeader]; done)
      | (intro h; rw [preadRespondAll_role] at h; simp at h; simp_all)
      | (intro h; simp_all)
  | snapStale m r h1 h2 h3 h4 h5 h6 =>
    iintro Hregs #HS Hrecv Hcr Hown
    iapply fupd_frame_left
    iframe Hregs
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    ihave #Hm := recv_one γ _ $$ Hrecv
    imod ownRaftGhost_step_snap_stale γ id r.p m h1 h3 h4 h5 $$ Hm Hg with Hg
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact (RInv_stepR (Adm := AdmS dec c0 S) (id := id) (fun _ _ h => h.1) (StepR.snapStale m r h1 h2 h3 h4 h5 h6) (noApp1 (by rw [h1]; decide)) HI)
    iintro %h
    exfalso
    revert h
    first
      | (simp [psendMsgs, padoptLeader]; done)
      | (intro h; rw [preadRespondAll_role] at h; simp at h; simp_all)
      | (intro h; simp_all)
  | readState m r e h1 h2 =>
    iintro Hregs #HS Hrecv Hcr Hown
    iapply fupd_frame_left
    iframe Hregs
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    ihave #Hm := recv_one γ _ $$ Hrecv
    imod ownRaftGhost_step_read_state γ id r.p m e h1 h2 $$ Hm Hg with Hg
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact (RInv_stepR (Adm := AdmS dec c0 S) (id := id) (fun _ _ h => h.1) (StepR.readState m r e h1 h2) (noApp1 (by rw [h1]; decide)) HI)
    dsimp only [psendMsgs, RState.full, pappend]
    iexact Hc
  | beat r ms h1 h2 h3 =>
    iintro Hregs #HS Hrecv Hcr Hown
    iapply fupd_frame_left
    iframe Hregs
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    imod ownRaftGhost_step_beat γ id r.p ms h1 h2 h3 $$ Hg with Hg
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact (RInv_stepR (Adm := AdmS dec c0 S) (id := id) (fun _ _ h => h.1) (StepR.beat r ms h1 h2 h3) noApp0 HI)
    dsimp only [psendMsgs, RState.full, pappend]
    iexact Hc
  | reMatch r mt h1 h2 =>
    iintro Hregs #HS Hrecv Hcr Hown
    iapply fupd_frame_left
    iframe Hregs
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    imod ownRaftGhost_step_rematch γ id r.p mt h1 h2 $$ Hg with Hg
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact (RInv_stepR (Adm := AdmS dec c0 S) (id := id) (fun _ _ h => h.1) (StepR.reMatch r mt h1 h2) noApp0 HI)
    dsimp only [psendMsgs, RState.full, pappend]
    iexact Hc
  | readRelease r h1 h2 =>
    iintro Hregs #HS Hrecv Hcr Hown
    iapply fupd_frame_left
    iframe Hregs
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    imod ownRaftGhost_step_read_release γ id r.p h1 h2 $$ Hg with Hg
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact (RInv_stepR (Adm := AdmS dec c0 S) (id := id) (fun _ _ h => h.1) (StepR.readRelease r h1 h2) noApp0 HI)
    dsimp only [psendMsgs, RState.full, pappend]
    iexact Hc
  | readFwd m r h1 h2 h3 =>
    iintro Hregs #HS Hrecv Hcr Hown
    iapply fupd_frame_left
    iframe Hregs
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    ihave #Hm := recv_one γ _ $$ Hrecv
    rw [show rdCount [m] = 1 by simp [rdCount_singleton, h1]]
    imod ownRaftGhost_step_read_fwd γ id r.p m h1 h2 h3 $$ Hm Hcr Hg with Hg
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact (RInv_stepR (Adm := AdmS dec c0 S) (id := id) (fun _ _ h => h.1) (StepR.readFwd m r h1 h2 h3) (noApp1 (by rw [h1]; decide)) HI)
    dsimp only [psendMsgs, RState.full, pappend]
    iexact Hc
  | readPend m r pm h1 h2 h3 =>
    iintro Hregs #HS Hrecv Hcr Hown
    iapply fupd_frame_left
    iframe Hregs
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    ihave #Hm := recv_one γ _ $$ Hrecv
    rw [show rdCount [m] = 1 by simp [rdCount_singleton, h1]]
    imod ownRaftGhost_step_read_pend γ id r.p m pm h1 h2 $$ Hm Hcr Hg with Hg
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact (RInv_stepR (Adm := AdmS dec c0 S) (id := id) (fun _ _ h => h.1) (StepR.readPend m r pm h1 h2 h3) (noApp1 (by rw [h1]; decide)) HI)
    dsimp only [psendMsgs, RState.full, pappend]
    iexact Hc
  | readArrive m r h1 h2 h3 =>
    iintro Hregs #HS Hrecv Hcr Hown
    iapply fupd_frame_left
    iframe Hregs
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    ihave #Hm := recv_one γ _ $$ Hrecv
    rw [show rdCount [m] = 1 by simp [rdCount_singleton, h1]]
    imod ownRaftGhost_step_read_arrive γ id r.p m h1 h2 h3 $$ Hm Hcr Hg with Hg
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact (RInv_stepR (Adm := AdmS dec c0 S) (id := id) (fun _ _ h => h.1) (StepR.readArrive m r h1 h2 h3) (noApp1 (by rw [h1]; decide)) HI)
    dsimp only [psendMsgs, RState.full, pappend]
    iexact Hc
  | win r mt ms h1 h2 h3 h4 h5 h6 =>
    iintro Hregs #HS Hrecv Hcr Hown
    iapply fupd_frame_left
    iframe Hregs
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    ihave #Henv := ownRaftGhostR_env γ dec c0 h0 HD id r HI $$ Hfr Hc
    imod ownRaftGhost_step_win γ r.cfg.cfg id r.p mt ms h1 h2 h3 h4 h5 (fun _ => h6) $$ Henv Hg with Hg
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact (RInv_stepR (Adm := AdmS dec c0 S) (id := id) (fun _ _ h => h.1) (StepR.win r mt ms h1 h2 h3 h4 h5 h6) noApp0 HI)
    iintro %h
    exfalso
    revert h
    first
      | (simp [psendMsgs, pwinState, pappend, pbecomeLeader]; done)
      | (intro h; rw [preadRespondAll_role] at h; simp at h; simp_all)
      | (intro h; simp_all)
  | commit r n h1 h2 h3 h4 h5 =>
    iintro Hregs #HS Hrecv Hcr Hown
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    ihave #Henv := ownRaftGhostR_env γ dec c0 h0 HD id r HI $$ Hfr Hc
    imod ownRaftGhost_step_commit γ r.cfg.cfg id r.p n h1 h2 h3 h4 h5 $$ Henv Hregs Hg
      with ⟨Hregs, Hg⟩
    imodintro
    iframe Hregs
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact (RInv_stepR (Adm := AdmS dec c0 S) (id := id) (fun _ _ h => h.1) (StepR.commit r n h1 h2 h3 h4 h5) noApp0 HI)
    iintro %h
    exfalso
    revert h
    first
      | (simp [psendMsgs]; done)
      | (intro h; rw [preadRespondAll_role] at h; simp at h; simp_all)
      | (intro h; simp_all)
  | sendApps r ms h1 h2 h3 =>
    iintro Hregs #HS Hrecv Hcr Hown
    iapply fupd_frame_left
    iframe Hregs
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    ihave #Henv := ownRaftGhostR_env γ dec c0 h0 HD id r HI $$ Hfr Hc
    imod ownRaftGhost_step_send_apps γ r.cfg.cfg id r.p ms h1 h2 (fun _ => h3) $$ Henv Hg with Hg
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact (RInv_stepR (Adm := AdmS dec c0 S) (id := id) (fun _ _ h => h.1) (StepR.sendApps r ms h1 h2 h3) noApp0 HI)
    dsimp only [psendMsgs, RState.full, pappend]
    iexact Hc
  | readAck m r N h1 h2 h3 h4 h5 h6 =>
    iintro Hregs #HS Hrecv Hcr Hown
    iapply fupd_frame_left
    iframe Hregs
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    ihave #Hm := recv_one γ _ $$ Hrecv
    ihave #Henv := ownRaftGhostR_env γ dec c0 h0 HD id r HI $$ Hfr Hc
    imod ownRaftGhost_step_read_ack γ r.cfg.cfg id r.p m N h1 h2 h3 h4 h5 h6 $$ Henv Hm Hg with Hg
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact (RInv_stepR (Adm := AdmS dec c0 S) (id := id) (fun _ _ h => h.1) (StepR.readAck m r N h1 h2 h3 h4 h5 h6) (noApp1 (by rw [h1]; decide)) HI)
    iintro %h
    exfalso
    revert h
    first
      | (simp [psendMsgs]; done)
      | (intro h; rw [preadRespondAll_role] at h; simp at h; simp_all)
      | (intro h; simp_all)
  | readSingle m r h1 h2 h3 h4 =>
    iintro Hregs #HS Hrecv Hcr Hown
    iapply fupd_frame_left
    iframe Hregs
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    ihave #Hm := recv_one γ _ $$ Hrecv
    rw [show rdCount [m] = 1 by simp [rdCount_singleton, h1]]
    ihave #Henv := ownRaftGhostR_env γ dec c0 h0 HD id r HI $$ Hfr Hc
    imod ownRaftGhost_step_read_single γ r.cfg.cfg id r.p m h1 h2 h3 h4 $$ Henv Hm Hcr Hg with Hg
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact (RInv_stepR (Adm := AdmS dec c0 S) (id := id) (fun _ _ h => h.1) (StepR.readSingle m r h1 h2 h3 h4) (noApp1 (by rw [h1]; decide)) HI)
    iintro %h
    exfalso
    revert h
    intro h; rw [preadRespondAll_role, h2] at h; cases h
  | readReleaseSingle r h1 h2 h3 =>
    iintro Hregs #HS Hrecv Hcr Hown
    iapply fupd_frame_left
    iframe Hregs
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    ihave #Henv := ownRaftGhostR_env γ dec c0 h0 HD id r HI $$ Hfr Hc
    imod ownRaftGhost_step_read_release_single γ r.cfg.cfg id r.p h1 h2 h3 $$ Henv Hg with Hg
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact (RInv_stepR (Adm := AdmS dec c0 S) (id := id) (fun _ _ h => h.1) (StepR.readReleaseSingle r h1 h2 h3) noApp0 HI)
    iintro %h
    exfalso
    revert h
    intro h; rw [preadRespondAll_role] at h; simp only at h; rw [h1] at h; cases h
  | campaign r peers cl h1 h2 h3 h4 h5 h6 =>
    iintro Hregs #HS Hrecv Hcr Hown
    iapply fupd_frame_left
    iframe Hregs
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    ihave #Henv := ownRaftGhostR_env γ dec c0 h0 HD id r HI $$ Hfr Hc
    imod ownRaftGhost_step_campaign γ r.cfg.cfg id r.p peers cl h1 h2 h5 h6 $$ Henv Hrecv Hcr Hg
      with ⟨Hg, %fpc, %Hfpc, #Hfrc, #HcK⟩
    icases FullOk_unique γ r.p.base fpc r.fp Hfpc HI.full $$ Hfrc Hfr with %Heq
    subst Heq
    imodintro
    unfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro
      exact RInv_stepR (Adm := AdmS dec c0 S) (id := id) (fun _ _ h => h.1) (StepR.campaign r peers cl h1 h2 h3 h4 h5 h6) noApp0 HI
    iintro %_
    dsimp only [psendMsgs, pbecomeCandidate, RState.full]
    iexact HcK
  | propose m r cs h1 h2 h3 h4 =>
    iintro Hregs #HS Hrecv Hcr Hown
    iapply fupd_frame_left
    iframe Hregs
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    ihave #Hm := recv_one γ _ $$ Hrecv
    iunfold isMessage at Hm
    rw [h1]
    icases Hm with ⟨-, #Hed⟩
    have hrep : PropRepl m.entries (propBatch r m.entries cs).1 :=
      propConf_repl (joint := CfgM.joint r.cfg.cfg) r.applied (plastIndex r.p) r.pci m.entries cs h3
    ihave #Hed' := entData_propRepl γ _ _ hrep $$ Hed
    imod ownRaftGhost_step_propose γ id r.p (propBatch r m.entries cs).1 h2
      (by rw [hrep.length]; exact h4) $$ Hed' Hg with Hg
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact (RInv_stepR (Adm := AdmS dec c0 S) (id := id) (fun _ _ h => h.1) (StepR.propose m r cs h1 h2 h3 h4) (noApp1 (by rw [h1]; decide)) HI)
    iintro %h
    exfalso
    revert h
    first
      | (simp [psendMsgs, pappend]; done)
      | (intro h; rw [preadRespondAll_role] at h; simp at h; simp_all)
      | (intro h; simp_all)
  | propDrop m r cs h1 h2 h3 h4 =>
    iintro Hregs #HS Hrecv Hcr Hown
    iapply fupd_frame_left
    iframe Hregs
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact (RInv_stepR (Adm := AdmS dec c0 S) (id := id) (fun _ _ h => h.1) (StepR.propDrop m r cs h1 h2 h3 h4) noApp0 HI)
    dsimp only [psendMsgs, RState.full, pappend]
    iexact Hc
  | advance r a h1 h2 h3 h4 =>
    iintro Hregs #HS Hrecv Hcr Hown
    iapply fupd_frame_left
    iframe Hregs
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact (RInv_stepR (Adm := AdmS dec c0 S) (id := id) (fun _ _ h => h.1) (StepR.advance r a h1 h2 h3 h4) noApp0 HI)
    dsimp only [psendMsgs, RState.full, pappend]
    iexact Hc
  | applySnap r h1 =>
    iintro Hregs #HS Hrecv Hcr Hown
    iapply fupd_frame_left
    iframe Hregs
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact (RInv_stepR (Adm := AdmS dec c0 S) (id := id) (fun _ _ h => h.1) (StepR.applySnap r h1) noApp0 HI)
    dsimp only [psendMsgs, RState.full, pappend]
    iexact Hc
  | applyConf r k e op cs' h1 h2 h3 h4 h5 h6 h7 h8 h9 =>
    iintro Hregs #HS Hrecv Hcr Hown
    iapply fupd_frame_left
    iframe Hregs
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact (RInv_stepR (Adm := AdmS dec c0 S) (id := id) (fun _ _ h => h.1) (StepR.applyConf r k e op cs' h1 h2 h3 h4 h5 h6 h7 h8 h9) noApp0 HI)
    dsimp only [psendMsgs, RState.full, pappend]
    iexact Hc
  | snapRestore m r fp' cs' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    iintro Hregs #HS Hrecv Hcr Hown
    iapply fupd_frame_left
    iframe Hregs
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    ihave #Hm := recv_one γ _ $$ Hrecv
    imod ownRaftGhost_step_snap_restore γ id r.p m h1 h3 h4 h5 h6 h7 $$ Hm Hg with Hg
    ihave #Hfr' := HS $$ %fp' %h10.2
    imodintro
    unfold ownRaftGhostR
    iframe Hg Hfr'
    isplitr
    · ipureintro
      exact RInv_stepR (Adm := AdmS dec c0 S) (id := id) (fun _ _ h => h.1) (StepR.snapRestore m r fp' cs' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10)
        (noApp1 (by rw [h1]; decide)) HI
    iintro %h
    simp [psendMsgs, padoptLeader] at h
  | appAccept m r lastnewi es' cm h1 h2 h3 h4 h5 h6 h7 h8 h9 =>
    iintro Hregs #HS Hrecv Hcr Hown
    iapply fupd_frame_left
    iframe Hregs
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    ihave #Hm := recv_one γ _ $$ Hrecv
    -- what the message tells the receiver for I1 (`AppKnow`), from its knowledge and records
    icases ownRaftGhost_logRecs γ id r.p true $$ Hg with ⟨%HwL, #HrL⟩
    ihave #HrR : logRecs γ base0 r.full $$ []
    · unfold RState.full; iapply logRecs_full γ r.p.base r.fp r.p.log HI.full $$ Hfr HrL
    icases appKnow_of_msg γ r m h1 (reDyn_of HD) (full_wf _ _ _ HI.full HwL) $$ Hm HrR with %HK
    rw [plogCommitTo_ite]
    have hb := (ite_cm_cases cm (if uint.Z m.commit < uint.Z lastnewi then m.commit else lastnewi)).2
    have hb1 : uint.Z (if uint.Z m.commit < uint.Z lastnewi then m.commit else lastnewi) ≤ uint.Z m.commit := by split <;> omega
    have hb2 : uint.Z (if uint.Z m.commit < uint.Z lastnewi then m.commit else lastnewi) ≤ uint.Z lastnewi := by split <;> omega
    imod ownRaftGhost_step_app_accept γ id r.p m lastnewi es' (if cm = true then (if uint.Z m.commit < uint.Z lastnewi then m.commit else lastnewi) else W64 0)
      (by omega) (by omega)
      h1 h3 h4 h5 h6 h7 $$ Hm Hg with Hg
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact RInv_appAccept m lastnewi es' _ HI _ ⟨by omega, by omega⟩
        (fun hne => by
          cases cm
          · exact absurd (h9 rfl) hne
          · simp only [↓reduceIte]; split <;> omega) h7 h8 HK
    iintro %h
    exfalso
    simp [psendMsgs, padoptLeader] at h
  | stepDown r h1 h2 =>
    iintro Hregs #HS Hrecv Hcr Hown
    iapply fupd_frame_left
    iframe Hregs
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    imod ownRaftGhost_step_stepDown γ id r.p h1 $$ Hrecv Hcr Hg with Hg
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact (RInv_stepR (Adm := AdmS dec c0 S) (id := id) (fun _ _ h => h.1) (StepR.stepDown r h1 h2) noApp0 HI)
    iintro %h
    exfalso
    revert h
    simp [pbecomeFollower]

/-- The dynamic refinement (see `ownRaftGhostR_stepR_in`), at `⊤`, given one later credit
(2026-10-14, stage R): the commit invariant's registry half opened around the step. -/
theorem ownRaftGhostR_stepR (γ : RaftNames) (dec : CCDec) (c0 : CCState) (h0 : CfgOk c0)
    (HD : γ.dyn = some (DynCfg.ofFold dec c0 h0)) (S : List EntryM → Prop)
    (id : w64) (r : RState) (recv : List Msg) (r' : RState) :
    StepR (AdmS dec c0 S) dec id r recv r' →
    ⊢ (□ ∀ (fp : List EntryM), ⌜S fp⌝ -∗ logRecs (GF := GF) γ base0 fp) -∗
      ([∗list] m ∈ recv, isMessage γ m) -∗ rdCred γ (rdCount recv) -∗ £ 1 -∗
      ownRaftGhostR γ dec c0 id r ={⊤}=∗ ownRaftGhostR γ dec c0 id r' := by
  intro Hstep
  iintro #HS Hrecv Hcr Hlc Hown
  ihave #Hinv : raftCommitInv γ $$ [Hown]
  · iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, -⟩
    iapply ownRaftGhost_inv_md γ id r.p $$ Hg
  iapply regs_open γ iprop(([∗list] m ∈ recv, isMessage (GF := GF) γ m) ∗
      rdCred γ (rdCount recv) ∗ ownRaftGhostR γ dec c0 id r) (ownRaftGhostR γ dec c0 id r')
    $$ Hinv Hlc [] [Hrecv Hcr Hown]
  · iintro Hregs ⟨Hrecv, Hcr, Hown⟩
    iapply ownRaftGhostR_stepR_in γ dec c0 h0 HD S id r recv r' Hstep $$ Hregs HS Hrecv Hcr Hown
  · iframe Hrecv Hcr Hown

end ghost

end EtcdGrove
end Perennial
