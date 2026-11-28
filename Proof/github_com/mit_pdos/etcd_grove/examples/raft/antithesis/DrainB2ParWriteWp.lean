/-
Lean-first (no Rocq counterpart). #33 parity B2, driver group E: **`parWriteB2.stmt`'s proof**
(`node.parallel`'s write): the `write` report (`announce`, `writeHstepD`), the disk written
(`saveDisk`), `wrote` (`emit`, `wroteHstepD`), the storage (`storeSave`), `n.hs = hs`; a kill on the
way leaves the rest unrecorded.
- `parAnnQ`/`parWroteQ`: what the two reports give back (`report_updB2`'s `Φ`);
- `eventOwn_wrote`: the `wrote` report's struct, as `&check.Event{E: "wrote"}` allocates it.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainB2ParReqWp
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.ParallelEvents
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__storeSave

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [AntStor GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]

/-- The `wrote` report before `emit` names its node. -/
def wroteEvM : AntCheck.Event := { AntSim.evWrote 0 with node := [] }

theorem atNode_wrote (id : w64) : atNode (AntSim.nameOf id) wroteEvM = AntSim.evWrote id := rfl

/-- What a write's report gives back (`report_updB2`'s `Φ`, nothing sent). -/
def parRepQ (γ : AntNamesB2) (j : Fin γ.R.N) (q : Qp) (v' : AntSim.NodeView) (net : List Msg)
    (xnet : List XMsg) : IProp GF :=
  iprop(viewFrag γ.toAntNames j v' ∗ runLive γ q ∗
    (∃ (net' : List Msg) (xnet' : List XMsg), sentLb γ.toAntNames net' ∗ xsentLb γ.toAntNames xnet' ∗
      ⌜net <+: net' ∧ (∀ m ∈ ([] : List Msg), m ∈ net') ∧ xnet <+: xnet' ∧
        ∀ y ∈ ([] : List XMsg), y ∈ xnet'⌝))

/-- The state between the write's steps: some view, the run's liveness share, the sent lists' lower
bounds above `net`, `xnet`. -/
def parWState (γ : AntNamesB2) (j : Fin γ.R.N) (q : Qp) (net : List Msg) (xnet : List XMsg)
    (P : AntSim.NodeView → Prop) : IProp GF :=
  iprop(∃ (v' : AntSim.NodeView) (net' : List Msg) (xnet' : List XMsg),
    viewFrag γ.toAntNames j v' ∗ runLive γ q ∗ sentLb γ.toAntNames net' ∗ xsentLb γ.toAntNames xnet' ∗
    ⌜P v' ∧ net <+: net' ∧ xnet <+: xnet'⌝)

end defs

section par
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [AntStor GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

instance hsOptRO_persistentB2 (hp : Loc) (oh : Option HardStateM) :
    Persistent (hsOptRO (GF := GF) hp oh) := by
  unfold hsOptRO; infer_instance

theorem emitStep_rec_alive {d : Bool} {f : w64} (h : (emitStep d f).1 = true) : d = false := by
  cases d
  · rfl
  · rw [emitStep_dead1] at h; cases h

theorem emitStep_norec_dead {d : Bool} {f : w64} (h : (emitStep d f).1 = false) : (emitStep d f).2.1 = true := by
  cases d
  · exact emitStep_kill h
  · exact emitStep_dead2 f

theorem ite_bnot {α : Sort _} (d : Bool) (a b : α) :
    (if (!d) = true then a else b) = (if d = true then b else a) := by
  cases d <;> rfl

/-- The write's final facts (`parWriteB2.stmt`'s), at the view `v'` after it. -/
abbrev parWFin (v : AntSim.NodeView) (m : AntSim.MemRec) (dead dead' wr : Bool) (v' : AntSim.NodeView) :
    Prop :=
  (dead = true → dead' = true ∧ wr = false ∧ v' = v) ∧
  (dead' = false → wr = true ∧ v' = { parWroteV v m with undo := none, made := true }) ∧
  ((wr = false ∧ v' = v) ∨ (dead' = true ∧ v' = parWroteV v m) ∨
    (dead' = false ∧ wr = true ∧ v' = { parWroteV v m with undo := none, made := true }))

/-- A report's `Φ` closed into the write's state. -/
theorem parRepQ_state (γ : AntNamesB2) (j : Fin γ.R.N) (q : Qp) (v' : AntSim.NodeView)
    (net net₀ : List Msg) (xnet xnet₀ : List XMsg) (P : AntSim.NodeView → Prop) (hP : P v')
    (hn : net₀ <+: net) (hx : xnet₀ <+: xnet) :
    parRepQ (GF := GF) γ j q v' net xnet ⊢ parWState γ j q net₀ xnet₀ P := by
  iintro H
  iunfold parRepQ at H
  icases H with ⟨Hv, Hl, %net', %xnet', #Hlb, #Hxlb, %Hp⟩
  iunfold parWState
  iexists v', net', xnet'
  iframe Hv Hl Hlb Hxlb
  ipureintro; exact ⟨hP, hn.trans Hp.1, hx.trans Hp.2.2.1⟩

theorem parWState_intro (γ : AntNamesB2) (j : Fin γ.R.N) (q : Qp) (v : AntSim.NodeView)
    (net : List Msg) (xnet : List XMsg) (P : AntSim.NodeView → Prop) (hP : P v) :
    viewFrag (GF := GF) γ.toAntNames j v ∗ runLive γ q ∗ sentLb γ.toAntNames net ∗
      xsentLb γ.toAntNames xnet ⊢ parWState γ j q net xnet P := by
  iintro ⟨Hv, Hl, #Hlb, #Hxlb⟩
  iunfold parWState
  iexists v, net, xnet
  iframe Hv Hl Hlb Hxlb
  ipureintro; exact ⟨hP, List.prefix_refl _, List.prefix_refl _⟩

set_option maxHeartbeats 8000000 in
/-- **`parWriteB2.stmt`**. -/
theorem parWriteB2
    (h_vu : view_update.law (GF := GF))
    (h_write : AntSim.antSim_write_in.stmt) (h_wrote : AntSim.antSim_wrote_in.stmt)
    (wp_stateEv : node.stateEv.specB2 (GF := GF) (hG := hG))
    (wp_announce : node.announce.specB2 (GF := GF) (hG := hG))
    (wp_saveDisk : node.saveDisk.specB2 (GF := GF) (hG := hG))
    (wp_emit : node.emit.specB2 (GF := GF) (hG := hG))
    (wp_storeSave : node.storeSave.spec (GF := GF) (hG := hG)) :
    parWriteB2.stmt (GF := GF) (hG := hG) := by
  intro np rdp hsp wrp c n γ j I msk v m net xnet dead fuse hp hsl hs hs0 oh d dk els ms γs k old qp
    K Φ hmsk hinm has hbt hpar hnorm hsave hidx hkb hal
  iintro ⟨#Hpkg, #Hc, #Hn, Hnp, Hrdp, Hhsp, Hwrp, Hhs, #HhsR, #Hoh, #Hd, Hdisk, Hk, #Hsl, #Hbig, Hms,
    #Hlock, Hmeta, Hpre, HentsZ, Hvf, Hl, #Hlb, #Hxlb, HΦ⟩
  ihave #Hc' := Hc
  iunfold antClusterB2 at Hc'
  icases Hc' with ⟨%cfg, %r, %ns, %stop, -, -, %Hmode, -⟩
  obtain ⟨hasR, hbtR⟩ := rMd_sync_b2 Hmode.2 has hbt
  have hparR : γ.R.drv.parallel = true := by rw [Hmode.2.2.2.2.2.2]; exact hpar
  ihave #Hfx := factsExt_none (GF := GF) γ.toAntNames
  unfold github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node.parallel.writeE
  icases typedPointsto_not_null_dup _ _ _ $$ Hrdp with ⟨Hrdp, %Hrnn⟩
  iStructNamed Hrdp
  wp_auto
  -- `whs`: `hs` unless it is `n.hs`
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun w => iprop(⌜w = executeVal⌝ ∗ hsp ↦ hp ∗
      whs_ptr ↦ (if hp = hsl then null else hp)))) $$ [Hhsp whs]
  · by_cases hpe : hp = hsl
    · simp only [hpe, decide_true, Bool.not_true, ite_true]
      wp_auto
      iframe
      ipureintro; rfl
    · simp only [hpe, decide_false, Bool.not_false, ite_false]
      wp_auto
      iframe
      ipureintro; rfl
  iintro %w ⟨%Hw, Hhsp, whs⟩
  subst Hw
  wp_take_receipt as Hr1
  wp_apply +noauto wp_stateEv c γ n j go!"write" hp hs I.rd.Entries' DFrac.discard els I.es hnorm
    $$ [$Hpkg $Hc $Hn $HhsR $Hsl $Hbig] as %pe ⟨-, -, Hev, Hr2⟩
  wp_take_receipt as Hr3
  -- the `write` report
  ihave ⟨Hpre, Hres⟩ : (if (emitStep dead fuse).1 then reports γ.strm
      [atNode (AntSim.nameOf (AntSim.nodeId j)) (stateEvM go!"write" hs I.es)]
      (parWState γ j qp net xnet (fun v' => v' = parWroteV v m ∧ dead = false)) else emp) ∗
      (if (emitStep dead fuse).1 then emp else viewFrag γ.toAntNames j v ∗ runLive γ qp)
      $$ [Hvf Hl Hr1 Hr2 Hr3]
  · by_cases he : (emitStep dead fuse).1 = true
    · have hd := emitStep_rec_alive he
      obtain ⟨hmems, hsnap, hents, hev, hnums⟩ := hal hd
      rw [he, hev]
      simp only [↓reduceIte]
      isplitl
      · ihave Hrc : ⧗ (AntSim.evWrite (AntSim.nodeId j) m.term m.vote m.commit m.ents m.snap).weight
            $$ [Hr1 Hr2 Hr3]
        · rw [hsnap, evWrite_weight, hents]
          iapply (receipt_add (GF := GF) (I.es.length + 1) 1).2
          iframe Hr3
          iapply (receipt_add (GF := GF) I.es.length 1).2
          iframe Hr2 Hr1
        iapply report_updB2 h_vu c γ j qp v (parWroteV v m)
          (AntSim.evWrite (AntSim.nodeId j) m.term m.vote m.commit m.ents m.snap) net [] xnet []
          (fun G0 G => G = G0) _ hnums (by rw [hsnap]; exact evWrite_chgOk _ _ _ _ _)
          (writeHstepD h_write msk hmsk j v m [] hinm hbtR hparR hasR hmems net xnet)
        iframe Hc Hlb Hxlb Hfx Hrc Hvf Hl
        iintro H
        iapply parRepQ_state γ j qp (parWroteV v m) net net xnet xnet _ ⟨rfl, hd⟩
          (List.prefix_refl _) (List.prefix_refl _)
        iunfold parRepQ
        iexact H
      · iempintro
    · have he' : (emitStep dead fuse).1 = false := by simpa using he
      rw [he']
      simp only [Bool.false_eq_true, ↓reduceIte]
      iframe Hvf Hl
  wp_apply +noauto wp_announce c γ n j pe _ _ dead fuse $$ [$Hpkg $Hc $Hn $Hk $Hev $Hpre]
    as %b %dead1 %fuse1 ⟨Hk, %Hann, HQ⟩
  ihave Hst : parWState γ j qp net xnet (fun v' => (v' = v ∨ (v' = parWroteV v m ∧ dead = false)) ∧
      (dead1 = false → v' = parWroteV v m ∧ dead = false) ∧ (dead = true → v' = v)) $$ [HQ Hres]
  · by_cases he : (emitStep dead fuse).1 = true
    · ihave HQ := ite_true_ent he $$ HQ
      iunfold parWState at HQ
      icases HQ with ⟨%v', %net', %xnet', Hv, Hl, #Hlb', #Hxlb', %Hp⟩
      iunfold parWState
      iexists v', net', xnet'
      iframe Hv Hl Hlb' Hxlb'
      ipureintro
      obtain ⟨⟨rfl, hd⟩, h1, h2⟩ := Hp
      exact ⟨⟨.inr ⟨rfl, hd⟩, fun _ => ⟨rfl, hd⟩, fun h => by rw [hd] at h; cases h⟩, h1, h2⟩
    · have he' : (emitStep dead fuse).1 = false := by simpa using he
      ihave Hres := ite_false_ent he' $$ Hres
      icases Hres with ⟨Hv, Hl⟩
      have hd1 : dead1 = true := by
        rcases Hann.2 with ⟨-, h, -⟩ | ⟨h, -⟩
        · rw [h]; exact emitStep_norec_dead he'
        · rw [he'] at h; cases h
      iapply parWState_intro γ j qp v net xnet (fun v' => (v' = v ∨ (v' = parWroteV v m ∧ dead = false)) ∧
        (dead1 = false → v' = parWroteV v m ∧ dead = false) ∧ (dead = true → v' = v))
        ⟨.inl rfl, (fun h => by rw [hd1] at h; cases h), fun _ => rfl⟩
      iframe Hv Hl Hlb Hxlb
  iunfold parWState at Hst
  icases Hst with ⟨%v1, %net1, %xnet1, Hvf, Hl, #Hlb1, #Hxlb1, %Hp1⟩
  -- the disk
  wp_take_receipt as Hr4
  wp_apply +noauto wp_saveDisk c γ n j d dk _ oh I.rd.Entries' els I.es dead1 fuse1 hsave
    $$ [$Hpkg $Hc $Hn $Hd $Hk $Hdisk $Hoh $Hsl $Hbig] as ⟨Hk, Hdisk⟩
  wp_take_receipt as Hr5
  ihave Hev2 : eventOwn (GF := GF) «$a0_ptr» wroteEvM $$ [«$a0»]
  · iunfold eventOwn
    iexists _
    iframe «$a0»
    simp only [wroteEvM, AntSim.evWrote, AntCheck.fieldRO, AntCheck.fieldIs, AntCheck.fieldZ,
      AntCheck.fieldRel]
    isplitr
    · ipureintro
      refine ⟨trivial, trivial, trivial, ?_⟩
      simp only [AntCheck.hasBit, AntCheck.fB, AntCheck.fA, AntCheck.fBy, AntCheck.fRole, AntCheck.fTerm,
        AntCheck.fVote, AntCheck.fCommit, AntCheck.fFirst, AntCheck.fLastIndex, AntCheck.fLastTerm,
        AntCheck.fApplied, AntCheck.fSnap, AntCheck.fW, AntCheck.fMore, AntCheck.fIndex, AntCheck.fCtx]
      decide
    simp only [AntCheck.hasBit, AntCheck.fEntries, AntCheck.fVoters, AntCheck.fOutgoing, AntCheck.fMsg,
      AntCheck.fCause]
    ipureintro; decide
  have hdd : dead = true → dead1 = true := by
    intro hd
    subst hd
    rcases Hann.2 with ⟨-, h, -⟩ | ⟨h, -⟩
    · rw [h]; exact emitStep_dead2 fuse
    · rw [emitStep_dead1] at h; cases h
  -- `wrote`
  ihave ⟨Hpre2, Hres2⟩ : (if (emitStep dead1 fuse1).1 then reports γ.strm
      [atNode (AntSim.nameOf (AntSim.nodeId j)) wroteEvM]
      (parWState γ j qp net1 xnet1
        (fun v' => v' = { parWroteV v m with undo := none, made := true } ∧ dead = false)) else emp) ∗
      (if (emitStep dead1 fuse1).1 then emp else viewFrag γ.toAntNames j v1 ∗ runLive γ qp)
      $$ [Hvf Hl Hr4 Hr5]
  · by_cases he : (emitStep dead1 fuse1).1 = true
    · have hd1 := emitStep_rec_alive he
      obtain ⟨rfl, hd⟩ := Hp1.1.2.1 hd1
      rw [he, atNode_wrote]
      simp only [↓reduceIte]
      isplitl
      · ihave Hrc : ⧗ (AntSim.evWrote (AntSim.nodeId j)).weight $$ [Hr4 Hr5]
        · rw [evWrote_weight]
          iapply (receipt_add (GF := GF) 1 1).2
          iframe Hr4 Hr5
        iapply report_updB2 h_vu c γ j qp (parWroteV v m)
          { parWroteV v m with undo := none, made := true } (AntSim.evWrote (AntSim.nodeId j)) net1 []
          xnet1 [] (fun G0 G => G = G0) _ (evWrote_numsOk _) (evWrote_chgOk _)
          (wroteHstepD h_wrote msk hmsk j (parWroteV v m) hinm hparR (by simp) net1 xnet1)
        iframe Hc Hlb1 Hxlb1 Hfx Hrc Hvf Hl
        iintro H
        iapply parRepQ_state γ j qp _ net1 net1 xnet1 xnet1
          (fun v' => v' = { parWroteV v m with undo := none, made := true } ∧ dead = false) ⟨rfl, hd⟩
          (List.prefix_refl _) (List.prefix_refl _)
        iunfold parRepQ
        iexact H
      · iempintro
    · have he' : (emitStep dead1 fuse1).1 = false := by simpa using he
      rw [he']
      simp only [Bool.false_eq_true, ↓reduceIte]
      iframe Hvf Hl
  wp_apply +noauto wp_emit c γ n j «$a0_ptr» wroteEvM _ dead1 fuse1 $$ [$Hpkg $Hc $Hn $Hk $Hev2 $Hpre2]
    as %b2 ⟨Hk, %Hb2, HQ2⟩
  subst Hb2
  ihave Hfin : parWState γ j qp net xnet (parWFin v m dead (emitStep dead1 fuse1).2.1 (!dead1))
      $$ [HQ2 Hres2]
  · by_cases he : (emitStep dead1 fuse1).1 = true
    · have hd1 := emitStep_rec_alive he
      have hd2 := emitStep_rec (f := fuse1) (hd1 ▸ he)
      ihave HQ := ite_true_ent he $$ HQ2
      iunfold parWState at HQ
      icases HQ with ⟨%v', %net', %xnet', Hv, Hl, #Hlb', #Hxlb', %Hp⟩
      obtain ⟨⟨rfl, hd⟩, hn, hx⟩ := Hp
      iunfold parWState
      iexists _, net', xnet'
      iframe Hv Hl Hlb' Hxlb'
      ipureintro
      subst hd1
      refine ⟨⟨(fun h => by rw [hd] at h; cases h), fun _ => ⟨rfl, rfl⟩, .inr (.inr ⟨hd2, rfl, rfl⟩)⟩,
        Hp1.2.1.trans hn, Hp1.2.2.trans hx⟩
    · have he' : (emitStep dead1 fuse1).1 = false := by simpa using he
      have hd2 := emitStep_norec_dead he'
      ihave Hres := ite_false_ent he' $$ Hres2
      icases Hres with ⟨Hv, Hl⟩
      iunfold parWState
      iexists v1, net1, xnet1
      iframe Hv Hl Hlb1 Hxlb1
      ipureintro
      refine ⟨⟨fun h => ⟨hd2, (by rw [hdd h]; rfl), Hp1.1.2.2 h⟩, (fun h => by rw [hd2] at h; cases h), ?_⟩,
        Hp1.2.1, Hp1.2.2⟩
      cases hd1 : dead1 <;> rw [hd1] at hd2
      · exact .inr (.inl ⟨hd2, (Hp1.1.2.1 hd1).1⟩)
      · rcases Hp1.1.1 with h | h
        · exact .inl ⟨rfl, h⟩
        · exact .inr (.inl ⟨hd2, h.1⟩)
  iunfold parWState at Hfin
  icases Hfin with ⟨%v', %net', %xnet', Hvf, Hl, #Hlb', #Hxlb', %Hfin⟩
  wp_auto
  wp_apply wp_storeSave n ms γs hs0 _ oh k old I.es I.rd.Entries' DFrac.discard hidx hkb
    $$ [$Hpkg $Hms $Hlock $Hmeta $Hoh $Hpre $HentsZ] as ⟨Hms, Hmeta, HentsZ, Hpost⟩
  ihave Hrdp : (rdp ↦ I.rd : IProp GF) $$ [SoftState HardState ReadStates Entries Snapshot
      CommittedEntries Messages MustSync]
  · iapply typedPointsto_combine _ _ _ Hrnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  ihave Hdisk : diskOwn (GF := GF) d (if (!dead1) = true then saveW dk oh I.es else dk) $$ [Hdisk]
  · rw [ite_bnot]; iexact Hdisk
  iapply HΦ $$ %(emitStep dead1 fuse1).2.1 %(emitStep dead1 fuse1).2.2 %(!dead1) %v' %net' %xnet'
  iframe
  iframe Hlb' Hxlb'
  ipureintro
  exact ⟨Hfin.1.1, Hfin.1.2.1, Hfin.1.2.2, Hfin.2.1, Hfin.2.2⟩

end par

end AntHarness
end EtcdGrove
end Perennial
