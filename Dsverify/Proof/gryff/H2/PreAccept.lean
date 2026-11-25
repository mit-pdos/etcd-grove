/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H2/PreAccept.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit H2: `handlePreAccept`
-/
module

public import Dsverify.Proof.gryff.H2.Env
public import Dsverify.Proof.gryff.H2.PreAcceptModel
public import Dsverify.Proof.gryff.H2.Attr
public import Dsverify.Proof.gryff.H2a.Equal
public import Dsverify.Proof.gryff.H2a.EpAt
public import Dsverify.Proof.gryff.H2a.Reply
public import Dsverify.Proof.gryff.H2.InstOpen
public import Dsverify.Proof.gryff.Wire.Proof.Lemmas
public import Dsverify.GeneratedProof.gryff.examples.gryffnet

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.replica2

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto
open Perennial.gryff.model (RState Copy LB Proposal Msg Ev Out Cmd Deps)
open Perennial.gryff.replica (XS rowOwn nSlots)

attribute [local instance] GooseGlobalGS.gooseInvGS

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [gA : examples.gryffnet.Assumptions] [fa : src.fastrpc.Assumptions] [wire.BufioSpecs GF]
variable [binA : wire.BinaryVarintHyps GF] -- H1-R6 / N-1
variable [sortA : Perennial.gryff.replica2.SortSliceHyp GF]
variable [strconvA : strconv.Assumptions] -- N-5


set_option goose.wp.extras true

theorem msgAt_preAccept (p : Loc) (mm : model.PreAcceptM) :
    msgAt (GF := GF) p (.preAccept mm) ⊣⊢ ∃ (g : wire.gryffproto.PreAccept.Msg) (sl : GoSlice),
      p ↦ wire.gryffproto.PreAccept.goVal g sl ∗ sl ↦*□ g.Command ∗ ⌜preAcceptOf g = mm⌝ := by
  unfold msgAt; exact .rfl

/-- `handlePreAccept`'s early return: the copy is committed, accepted or executed. -/
def paEarly (s : RState) (m : model.PreAcceptM) : Prop :=
  ∃ c, s.inst m.replica m.inst = some c ∧
    (c.status = model.St.COMMITTED ∨ c.status = model.St.ACCEPTED ∨ c.status = model.St.EXECUTED)

variable [pD : GryffPartiDeps (GF := GF)]

set_option maxHeartbeats 4000000 in
theorem handlePreAccept_wp' (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r h p : Loc)
    (m : model.PreAcceptM) (t : List Ev) (s s' : RState) (outs : List Out)
    (hstep : model.stepR k s (.msg (.preAccept m)) = .ok (s', outs)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ isReplica γ ρ k r ∗
        replicaOwn ρ k r s ∗ pendingOuts γ ρ k r t outs ∗ handlerOf r h ∗
        msgAt p (.preAccept m) }}
      (App (Val (h @!! go.GoType.PointerType src.gryff.EPaxosRMWHandler.ty @!!
        go!"handlePreAccept")) (Val #p))
    {{ RET #(); replicaOwn ρ k r s' ∗ pendingOuts γ ρ k r t [] }} := by
  wp_start as ⟨Hrep, Hown, Hpend, Hh, Hmsg⟩
  icases handler_open γ ρ k r h s $$ [$Hrep $Hh $Hown] with ⟨%gR, %pa, %co, %xs, #Henv, Hparts⟩
  icases (msgAt_preAccept ..).1 $$ Hmsg with ⟨%g, %sl, Hp, #Hsl, %Hg⟩
  unfold parts
  icases Hparts with ⟨Hparti, Hval, Hcoord, Hep, Hxs, Hprop, Hscr, %Hid⟩
  icases (epaxosOwn_open ..).1 $$ Hep with ⟨%ispS, %crtS, %c1S, %isp, %msR, %pvtR, %cfs, %M, %cu, %pm,
    #HR, #HnoC, #HispS, #Hisp, #HcrtS, #Hc1S, #Hcfs, #HmsR, #HpvtR, Hcu, Hcrt, HM, HMe, Hrows, Hinsts,
    Hmono, Hconfs, Hms, Hpm, Hrest, %Hf⟩
  unfold epEnv
  icases Henv with ⟨#HgR, #Hpa, #Hco, #Hh, #HR', #HId, #HN, #HDur, #Hgen, #Hfix⟩
  simp only [model.stepR] at hstep
  obtain ⟨hcmdsOk, hbox, hcases⟩ := stepPreAccept_cases s s' outs m hstep
  clear hstep
  subst Hg
  have hbox' := hbox
  simp only [model.inBox, preAcceptOf] at hbox'
  have hbox' := of_decide_eq_true hbox'
  obtain ⟨hq0, hq3, hi0, hiS⟩ := hbox'
  wp_auto
  -- `inst := e.InstanceSpace[Replica][Instance]`
  have hqw : sint.Z (W64 (sint.Z g.Replica)) = sint.Z g.Replica := by word
  have hiw : sint.Z (W64 (sint.Z g.Instance)) = sint.Z g.Instance := by
    unfold model.SLOTS at hiS; word
  ihave %HispSlen := ownSlice_len _ _ _ $$ Hisp
  obtain ⟨sq, hsq⟩ : ∃ sq, isp[(sint.Z (W64 (sint.Z g.Replica))).toNat]? = some sq :=
    ⟨_, List.getElem?_eq_getElem (by rw [hqw, Hf.1]; omega)⟩
  rw [ite_eq_left (show 0 ≤ sint.Z (W64 (sint.Z g.Replica)) ∧
      sint.Z (W64 (sint.Z g.Replica)) < sint.Z ispS.len by
    rw [hqw]; have := HispSlen.1; rw [Hf.1] at this; word)]
  wp_apply wp_load_slice_index (t := go.GoType.SliceType (go.GoType.PointerType src.gryff.Instance.ty))
    ispS _ isp _ sq (by rw [hqw]; omega) $$ [$Hisp] as -
  · ipureintro; exact hsq
  icases rows_acc' M isp _ sq hsq $$ Hrows with ⟨Hrow, Hrows⟩
  icases (replica.rowOwn_open ..).1 $$ Hrow with ⟨%ptrs, Hrow, %Hrowf⟩
  ihave %Hrowlen := ownSlice_len _ _ _ $$ Hrow
  rw [ite_eq_left (show 0 ≤ sint.Z (W64 (sint.Z g.Instance)) ∧
      sint.Z (W64 (sint.Z g.Instance)) < sint.Z sq.len by
    rw [hiw]; have := Hrowlen.1; rw [Hrowf.1] at this; unfold nSlots at this
    unfold model.SLOTS at hiS; word)]
  obtain ⟨ip, hip⟩ : ∃ ip, ptrs[(sint.Z (W64 (sint.Z g.Instance))).toNat]? = some ip :=
    ⟨_, List.getElem?_eq_getElem (by rw [hiw, Hrowf.1]; unfold nSlots; unfold model.SLOTS at hiS; omega)⟩
  wp_apply wp_load_slice_index (t := go.GoType.PointerType src.gryff.Instance.ty)
    sq _ ptrs _ ip (by rw [hiw]; omega) $$ [$Hrow] as Hrow
  · ipureintro; exact hip
  have hMip := Hrowf.2 _ ip hip
  rw [hiw, show ((sint.Z (W64 (sint.Z g.Replica))).toNat : Int) = sint.Z g.Replica by rw [hqw]; omega,
    show ((sint.Z g.Instance).toNat : Int) = sint.Z g.Instance by omega] at hMip
  -- `maxSeq`
  icases epaxosRest_maxSeq h $$ Hrest with ⟨%ms, HmaxSeq, Hrestc⟩
  wp_auto
  wp_join iprop((∃ ms' : w32, h.[src.gryff.EPaxosRMWHandler, go!"maxSeq"] ↦ ms') ∗
      p ↦ wire.gryffproto.PreAccept.goVal g sl ∗ preAccept_ptr ↦ p ∗ e_ptr ↦ h)
    with [HmaxSeq Hp preAccept e] as ⟨⟨%ms', HmaxSeq⟩, Hp, preAccept, e⟩
  -- the early return (`inst` committed, accepted or executed)
  have hMq : M.lookup (sint.Z g.Replica, sint.Z g.Instance) = if ip = Loc.null then none else some ip := hMip
  have hinstM : ((s.inst g.Replica g.Instance).isSome = (M.lookup (sint.Z g.Replica, sint.Z g.Instance)).isSome) :=
    Hf.2.2.2.2.2.2.1 _ _ hbox
  wp_join (Q := fun v => iprop(
      (⌜v = executeVal ∧ ¬ paEarly s (preAcceptOf g)⌝ ∨
        ⌜v = returnVal #() ∧ paEarly s (preAcceptOf g)⌝) ∗
      instsRep ρ xs s M ∗ inst_ptr ↦ ip ∗ e_ptr ↦ h ∗ preAccept_ptr ↦ p ∗
      p ↦ wire.gryffproto.PreAccept.goVal g sl)) at (if: _ then _ else _)
    with [Hinsts inst e preAccept Hp] as ⟨Hv, Hinsts, inst, e, preAccept, Hp⟩
  · by_cases hip : ip = Loc.null
    · subst hip
      have hnone : s.inst g.Replica g.Instance = none := by
        simp only [hMq, ite_true, Option.isSome_none, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hinstM
        exact hinstM
      wp_auto
      iframe
      ileft; ipureintro
      refine ⟨rfl, ?_⟩
      rintro ⟨c, hc, -⟩; simp [preAcceptOf, hnone] at hc
    · obtain ⟨c, hc⟩ : ∃ c, s.inst g.Replica g.Instance = some c := by
        simp only [hMq, hip, ite_false, Option.isSome_some] at hinstM
        exact Option.isSome_iff_exists.1 hinstM
      rw [ite_eq_right_iff.2 (fun h => absurd h hip)] at hMq
      icases insts_update ρ xs s M g.Replica g.Instance ip c hMq hc $$ Hinsts with ⟨Hc, Hclose⟩
      icases (copyRep_open ..).1 $$ Hc with ⟨%iv, Hiv, Hcmds, Hlb, %Hivf⟩
      simp only [hip, decide_false, Bool.not_false]
      wp_auto
      have hst := Hivf.2.1
      repeat' (first | wp_if_destruct | wp_auto)
      all_goals
        ihave Hc := (copyRep_open ρ xs _ ip c).2 $$ [Hiv Hcmds Hlb]
        · iexists iv; iframe; ipureintro; exact Hivf
        ihave Hinsts := Hclose $$ %s %c [] Hc
        · ipureintro; exact ⟨hc, fun _ _ _ => rfl⟩
      rotate_left 3
      · iframe; ileft; ipureintro
        refine ⟨by trivial, ?_⟩
        rintro ⟨c', hc', hst'⟩
        simp only [preAcceptOf, hc, Option.some.injEq] at hc'
        subst hc'
        rw [← hst] at hst'
        rcases hst' with h1 | h1 | h1 <;> simp_all [model.St.COMMITTED, model.St.ACCEPTED, model.St.EXECUTED]
      all_goals
        wp_apply (wp_recordCommands h r gR) $$ [$HR' $HgR $HDur]
        wp_apply (wp_sync h r gR) $$ [$HR' $HgR $HDur]
        iframe; iright; ipureintro
        refine ⟨by trivial, c, by simpa [preAcceptOf] using hc, ?_⟩
        rw [← hst]
        simp_all [model.St.COMMITTED, model.St.ACCEPTED, model.St.EXECUTED]
  icases Hv with (⟨%hv, %hne⟩ | ⟨%hv, %hearly⟩)
  rotate_left
  · -- the early return: nothing changes
    subst hv
    obtain ⟨-, hss, rfl⟩ : paEarly s (preAcceptOf g) ∧ s' = s ∧ outs = [] := by
      rcases hcases with ⟨c, hc, hst, h1, h2⟩ | ⟨hne, -⟩
      · exact ⟨hearly, h1, h2⟩
      · exact absurd hearly hne
    subst s'
    wp_auto
    ihave Hrow := (replica.rowOwn_open M _ sq).2 $$ [Hrow]
    · iexists ptrs; iframe; ipureintro; exact Hrowf
    ihave Hrows := Hrows $$ %M %(fun _ _ _ => rfl) Hrow
    iapply HΦ
    iframe Hpend
    iapply handler_close γ ρ k r gR h pa co xs s
    isplitr
    · unfold epEnv; iframe #
    unfold parts
    iframe Hparti Hval Hcoord Hxs Hprop Hscr
    ihave Hrest := Hrestc $$ %ms' HmaxSeq
    isplitl
    · iapply (epaxosOwn_open ..).2
      iexists ispS, crtS, c1S, isp, msR, pvtR, cfs, M, cu, pm
      iframe # ∗
      ipureintro; exact Hf
    · ipureintro; exact Hid
  -- not early
  subst hv
  obtain ⟨-, seq, deps, ch0, hupd, hcne, hrest⟩ : ¬ paEarly s (preAcceptOf g) ∧ _ := by
    rcases hcases with ⟨c, hc, hst, -⟩ | h
    · exact absurd ⟨c, hc, hst⟩ hne
    · exact h
  wp_auto
  -- `crtInstance[Replica] = Instance + 1` if needed
  have hcrtlen := Hf.2.2.1
  obtain ⟨cq, hcq⟩ : ∃ cq, s.crtInstance[(sint.Z (W64 (sint.Z g.Replica))).toNat]? = some cq :=
    ⟨_, List.getElem?_eq_getElem (by rw [hqw, hcrtlen]; omega)⟩
  have hqn : (sint.Z (W64 (sint.Z g.Replica))).toNat = g.Replica.toNat := by
    rw [hqw]
    have h1 : uint.Z g.Replica = sint.Z g.Replica := by word
    have h2 : uint.Z g.Replica = (g.Replica.toNat : Int) := rfl
    omega
  have hcqs : cq = s.crt g.Replica := by
    rw [hqn] at hcq
    simp [model.RState.crt, List.getD_eq_getElem?_getD, hcq]
  ihave %Hcrtlen := ownSlice_len _ _ _ $$ Hcrt
  rw [ite_eq_left (show 0 ≤ sint.Z (W64 (sint.Z g.Replica)) ∧
      sint.Z (W64 (sint.Z g.Replica)) < sint.Z crtS.len by
    rw [hqw]; have := Hcrtlen.1; rw [hcrtlen] at this; word)]
  wp_apply wp_load_slice_index (t := go.int32) crtS _ _ _ cq (by rw [hqw]; omega) $$ [$Hcrt] as Hcrt
  · ipureintro; exact hcq
  wp_join iprop(crtS ↦* (paS1 s (preAcceptOf g)).crtInstance ∗
      ([∗list] q ∈ List.finRange 3, monoNatAuthOwn (ρ.crt q) 1
        (sint.Z ((paS1 s (preAcceptOf g)).crt (rid32 q))).toNat) ∗
      e_ptr ↦ h ∗ preAccept_ptr ↦ p ∗ p ↦ wire.gryffproto.PreAccept.goVal g sl)
    with [Hcrt Hmono e preAccept Hp] as ⟨Hcrt, Hmono, e, preAccept, Hp⟩
  · -- `Instance >= crtInstance[Replica]`
    have hS1 : paS1 s (preAcceptOf g) = s.setCrt g.Replica (g.Instance + 1) := by
      simp only [paS1, preAcceptOf, model.sge, model.sle, ← hcqs, Hif, decide_true, ite_true]
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 (sint.Z g.Replica)) ∧
        sint.Z (W64 (sint.Z g.Replica)) < sint.Z crtS.len by
      rw [hqw]; have := Hcrtlen.1; rw [hcrtlen] at this; word)]
    ihave >Hmono := crt_monos_update ρ s g.Replica (g.Instance + 1) ?_ $$ Hmono
    · rw [← hcqs]
      have : sint.Z (g.Instance + 1) = sint.Z g.Instance + 1 := by unfold model.SLOTS at hiS; word
      omega
    wp_apply wp_store_slice_index (t := go.int32) crtS _ _ (g.Instance + W32 1) $$ [$Hcrt] as Hcrt
    · ipureintro; rw [hqw, hcrtlen]; omega
    wp_join_done
    rw [hS1, hqn, show W32 1 = (1 : w32) from rfl]
    iframe
  · have hS1 : paS1 s (preAcceptOf g) = s := by
      simp only [paS1, preAcceptOf, model.sge, model.sle, ← hcqs, Hif, decide_false]
      rfl
    rw [hS1]
    iframe
  -- close the EPaxos part at `S1` for `updateAttributes`
  ihave Hrow := (replica.rowOwn_open M _ sq).2 $$ [Hrow]
  · iexists ptrs; iframe; ipureintro; exact Hrowf
  ihave Hrows := Hrows $$ %M %(fun _ _ _ => rfl) Hrow
  ihave Hrest := Hrestc $$ %ms' HmaxSeq
  ihave Hep : epaxosOwnAt ρ h r xs (paS1 s (preAcceptOf g)) ⟨ispS, crtS, c1S, isp, msR, pvtR, cfs, M, cu, pm⟩ $$
      [Hcu Hcrt HM HMe Hrows Hinsts Hmono Hconfs Hms Hpm Hrest]
  · simp only [epaxosOwnAt]
    have hco : committedOrExecuted (paS1 s (preAcceptOf g)) = committedOrExecuted s := by
      funext n; simp only [committedOrExecuted, model.committedCopy, paS1_inst]
    simp only [instsRep, paS1_inst, paS1_confAt, paS1_maxSeqK0]
    rw [hco]
    iframe # ∗
    ipureintro
    simpa [epFacts, paS1_len, hco] using Hf

  ihave #Hae : attrEnv k r gR h $$ []
  · unfold attrEnv; iframe #
  have hcmds : (preAcceptOf g).cmds = g.Command.map cmdOf := rfl
  wp_apply (wp_updateAttributes_at ρ k r gR h xs (paS1 s (preAcceptOf g))
    ⟨ispS, crtS, c1S, isp, msR, pvtR, cfs, M, cu, pm⟩ sl g.Command g.Seq g.Deps
    g.Replica g.Instance (seq, deps, ch0) (by rw [← hcmds]; exact hcmdsOk) ⟨hq0, hq3⟩
    (by simp [Hid]) (by rw [← hcmds]; exact hupd)) $$ [$Hae $Hep $Hsl] as %seq' %deps' %ch ⟨Hep, %Hres⟩
  simp only [Prod.mk.injEq] at Hres
  obtain ⟨rfl, hdeps, rfl⟩ := Hres
  subst hdeps
  -- Not done (the next steps, as tried on commit `H2: handlePreAccept WIP (uncommittedDeps
  -- loop)`, before G41): `changed := seq != Seq || !equal(&deps, &Deps)` (G41, a spec of
  -- `equal`), the store's tag (`wp_Replica_GetStoreMetadata`, `wp_Tag_GreaterThan`) and the base
  -- (`wp_Replica_GetCurrentValue`, joined on `paBase`), the `uncommittedDeps` loop
  -- (`wp_load_arr32` on `deps` and `CommittedUpTo`, joined on `paUnc`), the status, the slot's
  -- update through `epaxosOwn_inst_open'` (closings (a) / (b) / (c)), `updateConflicts`,
  -- `recordInstanceMetadata` / `recordCommands` / `sync`, the reply (`SendMsg.wp` with
  -- `h2Fixed`'s `preAcceptReplyRPC` / `preAcceptOKRPC`), `handler_close`.
  -- `changed := seq != Seq || !equal(&deps, &preAccept.Deps)` (G41)
  iStructNamed Hp
  wp_join (Q := fun v => iprop(⌜v = #(paCh (preAcceptOf g) seq (depsOf deps'))⌝ ∗
      deps_ptr ↦ deps' ∗ preAccept_ptr ↦ p ∗
      p.[src.gryffproto.PreAccept, go!"Deps"] ↦ (wire.gryffproto.PreAccept.goVal g sl).Deps'))
    at (if: _ then _ else _)
    with [deps preAccept Deps] as ⟨%Hchv, deps, preAccept, Deps⟩
  · wp_if_destruct
    · wp_apply (wp_equal deps_ptr _ deps' (wire.gryffproto.PreAccept.goVal g sl).Deps' _ _)
        $$ [$deps $Deps] as ⟨deps, Deps⟩
      iframe; ipureintro
      simp [paCh, preAcceptOf, wire.gryffproto.PreAccept.goVal]
    · iframe; ipureintro
      have : (seq != g.Seq) = true := by simpa using Hif
      simp [paCh, preAcceptOf, this]
  subst Hchv
  -- `base := preAccept.Base`; `tag := *e.R.GetStoreMetadata(Command[0].K).Tag`
  obtain ⟨c0, hc0⟩ : ∃ c0, g.Command[0]? = some c0 := by
    cases hg : g.Command with
    | nil => exact absurd (by simp [preAcceptOf, hg]) hcne
    | cons a _ => exact ⟨a, rfl⟩
  have hc0K : c0.K' = W64 0 := by
    have := hcmdsOk
    simp only [preAcceptOf, model.cmdsOk, List.all_eq_true, List.mem_map] at this
    have h1 := this (cmdOf c0) ⟨c0, List.mem_of_getElem? hc0, rfl⟩
    simp [model.Cmd.ok, cmdOf] at h1
    exact h1.2
  ihave %Hsllen := ownSlice_len _ _ _ $$ Hsl
  have hsl0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z sl.len := by
    have := Hsllen.1
    have : 0 < g.Command.length := by
      cases hg : g.Command with
      | nil => simp [hg] at hc0
      | cons _ _ => simp
    word
  icases ownSlice_elem_acc (sint.Z (W64 0)) c0 sl DFrac.discard g.Command (by decide) hc0 $$ Hsl
    with ⟨#Hc0, -⟩
  iStructNamed Hc0
  wp_auto
  rw [ite_eq_left hsl0]
  wp_apply (IntoValTyped.wp_load (t := src.state.Key.ty) _ _ _) $$ [$K] as -
  rw [hc0K]
  wp_apply (wp_Replica_GetStoreMetadata r pa k (paS1 s (preAcceptOf g)).tag s.ongoing)
    $$ [$Hpa Hparti] as %md ⟨%tp, %gt, %Hgt, #Htp, Hmd, Hpclose⟩
  · rw [paS1_tag]; iframe
  ihave Hparti := Hpclose $$ Hmd
  wp_apply wp_Tag_GreaterThan $$ [$tag] as tag
  rw [paS1_tag] at Hgt
  have hgtS : (paS1 s (preAcceptOf g)).tag.gt (preAcceptOf g).base.t = (tagOf gt).gt (tagOf g.Base.T') := by
    rw [paS1_tag, ← Hgt]; rfl
  generalize hb : (tagOf gt).gt (tagOf g.Base.T') = b at hgtS
  wp_join iprop(∃ bv : src.gryffproto.ValTag, base_ptr ↦ bv ∗
      changed_ptr ↦ (paBase (paS1 s (preAcceptOf g)) (preAcceptOf g)
        (paCh (preAcceptOf g) seq (depsOf deps'))).2 ∗
      ⌜vtOf bv = (paBase (paS1 s (preAcceptOf g)) (preAcceptOf g)
        (paCh (preAcceptOf g) seq (depsOf deps'))).1⌝ ∗ valOwn gR s.val ∗
      tag_ptr ↦ gt ∗ e_ptr ↦ h ∗ preAccept_ptr ↦ p ∗
      p.[src.gryffproto.PreAccept, go!"Command"] ↦ (wire.gryffproto.PreAccept.goVal g sl).Command')
    with [base changed Hval tag e preAccept Command]
    as ⟨%bv, base, changed, %Hbv, Hval, tag, e, preAccept, Command⟩
  · simp only [paBase, hgtS, Bool.false_eq_true, ite_false]
    iexists _
    iframe
    ipureintro
    rfl
  · -- the store's tag is greater: the store's value-tag is the base
    rw [ite_eq_left hsl0]
    wp_apply (IntoValTyped.wp_load (t := src.state.Key.ty) _ _ _) $$ [$K] as -
    wp_apply (wp_Replica_GetCurrentValue r gR s.val) $$ [$HgR $Hval] as Hval
    wp_join_done
    simp only [paBase, hgtS, ite_true]
    iexists _
    iframe
    ipureintro
    simp only [vtOf, model.RState.storeVT, Hgt, paS1_val, paS1_tag]
  -- `uncommittedDeps`
  simp only [epaxosOwnAt]
  icases Hep with ⟨-, -, -, -, -, -, -, -, -, Hcu, Hcrt, HM,
    HMe, Hrows, Hinsts, Hmono, Hconfs, Hms, Hpm, Hrest, %Hf2⟩
  have hcu : depsOf cu = s.committedUpTo := by rw [Hf2.2.2.2.1, paS1_committedUpTo]
  ihave %Hdl := array_len _ _ _ _ $$ deps
  ihave %Hcul := array_len _ _ _ _ $$ Hcu
  wp_join iprop(uncommittedDeps_ptr ↦ paUnc (paS1 s (preAcceptOf g)) (depsOf deps') ∗
      deps_ptr ↦ deps' ∗ h.[src.gryff.EPaxosRMWHandler, go!"CommittedUpTo"] ↦ cu ∗ e_ptr ↦ h)
    at next with [uncommittedDeps deps Hcu e q] as ⟨uncommittedDeps, deps, Hcu, e⟩
  · ihave HI : iprop(∃ qv : w64, q_ptr ↦ qv ∗ uncommittedDeps_ptr ↦ false ∗
        ⌜0 ≤ sint.Z qv ∧ sint.Z qv ≤ 3 ∧ ∀ j : Nat, (j : Int) < sint.Z qv →
          model.sgt ((depsOf deps').at j) (s.committedUpTo.at j) = false⌝) $$ [q uncommittedDeps]
    · iexists W64 0; iframe; ipureintro
      refine ⟨by decide, by decide, fun j hj => ?_⟩
      exfalso; simp at hj; omega
    wp_for HI
    icases HI with ⟨q, uncommittedDeps, %Hq⟩
    wp_auto
    have hpu : ∀ j : Nat, j < 3 → (paUnc (paS1 s (preAcceptOf g)) (depsOf deps') = true ↔
        ∃ j' : Nat, j' < 3 ∧ model.sgt ((depsOf deps').at j') (s.committedUpTo.at j') = true) := by
      intro _ _
      simp only [paUnc, paS1_committedUpTo, List.any_eq_true, List.mem_cons, List.mem_nil_iff,
        or_false]
      constructor
      · rintro ⟨x, hx, h⟩; exact ⟨x, by omega, h⟩
      · rintro ⟨j', hj', h⟩; exact ⟨j', by omega, h⟩
    wp_if_destruct
    · have hq3 : sint.Z qv < 3 := by have := go.intoVal_inj Hif; simp at this; word
      have hq5 : 0 ≤ sint.Z qv ∧ sint.Z qv < 5 := by omega
      rw [ite_eq_left hq5]
      wp_apply wire.wp_load_arr32 $$ [$deps] as deps
      · ipureintro; exact hq5
      rw [ite_eq_left hq5]
      wp_apply wire.wp_load_arr32 $$ [$Hcu] as Hcu
      · ipureintro; exact hq5
      have hat : ∀ (a : GoArray w32 5), a.arr.getD (sint.Z qv).toNat (W32 0) =
          (depsOf a).at (sint.Z qv).toNat := fun a => rfl
      rw [hat, hat, hcu]
      wp_if_destruct
      · wp_for_post
        rw [(hpu 0 (by omega)).2 ⟨(sint.Z qv).toNat, by omega, by
          simp only [model.sgt, model.slt, decide_eq_true_eq]; exact Hif⟩]
        iframe
        ipureintro; rfl
      · wp_for_post
        iframe
        iexists (qv + W64 1)
        iframe; ipureintro
        refine ⟨by word, by word, fun j hj => ?_⟩
        have : sint.Z (qv + W64 1) = sint.Z qv + 1 := by word
        rw [this] at hj
        by_cases hjq : (j : Int) < sint.Z qv
        · exact Hq.2.2 j hjq
        · have : j = (sint.Z qv).toNat := by omega
          subst this
          simp only [model.sgt, model.slt, decide_eq_false_iff_not]; exact Hif
    · have hq3 : ¬ sint.Z qv < sint.Z (W64 3) := fun h' => Hif (by rw [decide_eq_true h'])
      rw [decide_eq_false hq3]; simp only [Bool.false_eq_true, ↓reduceIte]
      have : paUnc (paS1 s (preAcceptOf g)) (depsOf deps') = false := by
        rw [← Bool.not_eq_true, hpu 0 (by omega)]
        rintro ⟨j', hj', h⟩
        rw [Hq.2.2 j' (by word)] at h; exact absurd h (by simp)
      rw [this]
      iframe
  -- the status
  generalize hbase : paBase (paS1 s (preAcceptOf g)) (preAcceptOf g)
    (paCh (preAcceptOf g) seq (depsOf deps')) = bch at *
  obtain ⟨bvt, chg⟩ := bch
  simp only at Hbv ⊢
  wp_join iprop(status_ptr ↦ (if chg then model.St.PREACCEPTED else model.St.PREACCEPTED_EQ) ∗
      changed_ptr ↦ chg) with [status changed] as ⟨status, changed⟩
  wp_join (Q := fun v => iprop((⌜v = returnVal #()⌝ ∗ replicaOwn ρ k r s' ∗ pendingOuts γ ρ k r t []) ∨
      (⌜v = executeVal⌝ ∗
        ⌜∀ c, s.inst g.Replica g.Instance = some c → model.slt g.Ballot c.ballot = false⌝ ∗
        epaxosOwn ρ h r xs ((paS1 s (preAcceptOf g)).setInst g.Replica g.Instance
          (paCopy (s.inst g.Replica g.Instance) (preAcceptOf g) seq (depsOf deps') bvt
            (if chg then model.St.PREACCEPTED else model.St.PREACCEPTED_EQ))) ∗
        pendingOuts γ ρ k r t outs ∗
        partiOwn pa (replicaIface r) k (paS1 s (preAcceptOf g)).tag s.ongoing ∗ valOwn gR s.val ∗
        coordOwn ρ co (replicaIface r) k s ∗ ghostVar ρ.xs (Qp.half 1) xs ∗
        proposeOwn ρ gR s.proposeQ ∗ scratchOwn r ∗
        e_ptr ↦ h ∗ preAccept_ptr ↦ p ∗ seq_ptr ↦ seq ∗ deps_ptr ↦ deps' ∗ base_ptr ↦ bv ∗
        status_ptr ↦ (if chg then model.St.PREACCEPTED else model.St.PREACCEPTED_EQ) ∗
        p.[src.gryffproto.PreAccept, go!"LeaderId"] ↦ (wire.gryffproto.PreAccept.goVal g sl).LeaderId' ∗
        p.[src.gryffproto.PreAccept, go!"Replica"] ↦ (wire.gryffproto.PreAccept.goVal g sl).Replica' ∗
        p.[src.gryffproto.PreAccept, go!"Instance"] ↦ (wire.gryffproto.PreAccept.goVal g sl).Instance' ∗
        p.[src.gryffproto.PreAccept, go!"Ballot"] ↦ (wire.gryffproto.PreAccept.goVal g sl).Ballot' ∗
        p.[src.gryffproto.PreAccept, go!"Command"] ↦ (wire.gryffproto.PreAccept.goVal g sl).Command' ∗
        p.[src.gryffproto.PreAccept, go!"Seq"] ↦ (wire.gryffproto.PreAccept.goVal g sl).Seq' ∗
        p.[src.gryffproto.PreAccept, go!"Base"] ↦ (wire.gryffproto.PreAccept.goVal g sl).Base' ∗
        p.[src.gryffproto.PreAccept, go!"Deps"] ↦ (wire.gryffproto.PreAccept.goVal g sl).Deps')))
    at (if: _ then _ else _)
    with [inst e preAccept LeaderId Replica Instance Ballot Command Seq Base Deps seq deps base status
      Hcu Hcrt HM HMe Hrows Hinsts Hmono Hconfs Hms Hpm Hrest Hpend Hparti Hval Hcoord Hxs Hprop Hscr]
    as HQ
  ·
    by_cases hip : ip = Loc.null
    · subst hip
      have hnone : s.inst g.Replica g.Instance = none := by
        simp only [hMq, ite_true, Option.isSome_none] at hinstM
        cases h0 : s.inst g.Replica g.Instance
        · rfl
        · rw [h0] at hinstM; simp at hinstM
      ihave Hep : epaxosOwn ρ h r xs (paS1 s (preAcceptOf g)) $$
          [Hcu Hcrt HM HMe Hrows Hinsts Hmono Hconfs Hms Hpm Hrest]
      · iapply (epaxosOwn_at ..).2
        iexists ⟨ispS, crtS, c1S, isp, msR, pvtR, cfs, M, cu, pm⟩
        simp only [epaxosOwnAt]; iframe # ∗; ipureintro; exact Hf2
      have hn1 : (paS1 s (preAcceptOf g)).inst g.Replica g.Instance = none := by rw [paS1_inst]; exact hnone
      icases epaxosOwn_inst_open' ρ h r xs _ g.Replica g.Instance hbox $$ Hep with
        ⟨%ispS', %sq', %isp', %ptrs', %p0, #HispS', #Hisp', %Hsl', Hrow', Hm, %Hxs0, Hcl⟩
      icombine HispS HispS' gives %Heq
      subst Heq
      icombine Hisp Hisp' gives %Heq2
      subst Heq2
      rw [hn1]
      icases Hm with %Hp0
      wp_auto
      rw [ite_eq_left (show 0 ≤ sint.Z (W64 (sint.Z g.Replica)) ∧
          sint.Z (W64 (sint.Z g.Replica)) < sint.Z ispS.len by
        rw [hqw]; have := HispSlen.1; rw [Hf.1] at this; word)]
      wp_apply wp_load_slice_index (t := go.GoType.SliceType (go.GoType.PointerType
        src.gryff.Instance.ty)) ispS _ isp _ sq' (by rw [hqw]; omega) $$ [$Hisp] as -
      · ipureintro; rw [hqw]; exact Hsl'.1
      ihave %Hrl' := ownSlice_len _ _ _ $$ Hrow'
      have hil : (sint.Z g.Instance).toNat < ptrs'.length := (List.getElem?_eq_some_iff.1 Hsl'.2).1
      rw [ite_eq_left (show 0 ≤ sint.Z (W64 (sint.Z g.Instance)) ∧
          sint.Z (W64 (sint.Z g.Instance)) < sint.Z sq'.len by
        rw [hiw]; have := Hrl'.1; have := Hrl'.2; have := hi0; word)]
      icases typedPointsto_not_null_dup _ _ _ $$ «$r0» with ⟨«$r0», %Hnn⟩
      have hcnc : committedOrExecuted (paS1 s (preAcceptOf g)) (sint.Z g.Replica, sint.Z g.Instance) =
          false := by
        unfold committedOrExecuted model.committedCopy
        simp only [BitVec.ofInt_toInt, paS1_inst, hnone]; split <;> rfl
      obtain ⟨hnf, hlf, hnx⟩ := Hxs0 hcnc
      ihave Hcm : cmdsRep sl (preAcceptOf g).cmds $$ []
      · unfold cmdsRep; iexists g.Command; iframe #; ipureintro; exact ⟨rfl, hcmdsOk⟩ -- H2c-R1
      ihave Hlb0 : lbRep ρ Loc.null none $$ []
      · unfold lbRep; ipureintro; rfl
      ihave Hc := (copyRep_open ρ xs (sint.Z g.Replica, sint.Z g.Instance) «$r0_ptr»
          (paCopy none (preAcceptOf g) seq (depsOf deps') bvt
            (if chg then model.St.PREACCEPTED else model.St.PREACCEPTED_EQ))).2 $$ [«$r0» Hcm Hlb0]
      · iexists _; iframe «$r0»; dsimp only; iframe; ipureintro
        have hst : (if chg = true then model.St.PREACCEPTED else model.St.PREACCEPTED_EQ) ≠
            model.St.EXECUTED := by
          split <;> simp [model.St.EXECUTED, model.St.PREACCEPTED, model.St.PREACCEPTED_EQ]
        simp [paCopy, preAcceptOf, Hbv, hnf, hlf, hst, hnx]
      iapply wp_fupd
      wp_apply wp_store_slice_index (t := go.GoType.PointerType src.gryff.Instance.ty) sq' _ ptrs'
        «$r0_ptr» $$ [$Hrow'] as Hrow'
      · ipureintro; rw [hiw]; omega
      rw [hiw]
      icases Hcl with ⟨-, Hb, -⟩
      ihave >Hep := Hb $$ %«$r0_ptr» %_ [] Hrow' Hc
      · ipureintro; exact ⟨rfl, Hnn⟩
      rw [hnone]
      iright
      isplitr
      · ipureintro; rfl
      isplitr
      · ipureintro; intro c hc'; cases hc'
      iframe
    · obtain ⟨c, hc⟩ : ∃ c, s.inst g.Replica g.Instance = some c := by
        simp only [hMq, hip, ite_false, Option.isSome_some] at hinstM
        exact Option.isSome_iff_exists.1 hinstM
      have hMq' : M.lookup (sint.Z g.Replica, sint.Z g.Instance) = some ip := by
        rw [hMq, if_neg hip]
      have hc1 : (paS1 s (preAcceptOf g)).inst g.Replica g.Instance = some c := by
        rw [paS1_inst]; exact hc
      icases insts_update ρ xs (paS1 s (preAcceptOf g)) M g.Replica g.Instance ip c hMq' hc1 $$ Hinsts
        with ⟨Hc, Hiclose⟩
      icases (copyRep_open ..).1 $$ Hc with ⟨%ivs, Hiv, Hcmds, Hlb, %Hivf⟩
      rw [decide_eq_false hip]
      wp_auto
      have hcb : ivs.ballot' = c.ballot := Hivf.1
      wp_if_destruct
      · -- an older ballot: reply FALSE with the copy's attributes
        obtain ⟨o, ho, hs', rfl⟩ : ∃ o, model.sendPeer (paS1 s (preAcceptOf g)) g.LeaderId
            (.preAcceptReply ⟨g.Replica, g.Instance, model.FALSE, c.ballot, c.seq, c.deps, c.base⟩) =
              some o ∧ s' = paS1 s (preAcceptOf g) ∧ outs = [o] := by
          rcases hrest with ⟨c', o, hc', hlt, ho, hs', ho'⟩ | ⟨hge, -⟩
          · have hc2 : s.inst (preAcceptOf g).replica (preAcceptOf g).inst = some c := hc
            rw [hc2] at hc'; obtain rfl := Option.some.inj hc'
            exact ⟨o, ho, hs', ho'⟩
          · have := hge c hc
            simp only [preAcceptOf, model.slt, decide_eq_false_iff_not] at this
            rw [← hcb] at this; exact absurd Hif (of_decide_eq_false this)
        subst hs'
        have hs2 : model.sendPeer (paS1 s (preAcceptOf g)) g.LeaderId (.preAcceptReply (preAcceptReplyOf
            ({ Replica' := g.Replica, Instance' := g.Instance, OK' := W8 0, Ballot' := ivs.ballot',
               Seq' := ivs.Seq', Deps' := ivs.Deps', CommittedDeps' := cu, Base' := ivs.Base' } :
              src.gryffproto.PreAcceptReply))) = some o := by
          rw [← ho]; congr 2
          simp only [preAcceptReplyOf, hcb, Hivf.2.2.1, Hivf.2.2.2.1, Hivf.2.2.2.2.1]; rfl
        wp_apply (wp_replyPreAccept_a γ ρ k r gR h t (paS1 s (preAcceptOf g)) (by simp [Hid])
          g.LeaderId _ «$a1_ptr» o [] hs2) $$ [$HR' $HgR $Hgen $Hfix $«$a1» $Hpend] as Hpend
        ihave Hc := (copyRep_open ρ xs _ ip c).2 $$ [Hiv Hcmds Hlb]
        · iexists ivs; iframe; ipureintro; exact Hivf
        ihave Hinsts := Hiclose $$ %(paS1 s (preAcceptOf g)) %c [] Hc
        · ipureintro; exact ⟨hc1, fun _ _ _ => rfl⟩
        ileft
        isplitr
        · ipureintro; rfl
        iframe Hpend
        iapply handler_close γ ρ k r gR h pa co xs
        isplitr
        · unfold epEnv; iframe #
        unfold parts
        have e1 : (paS1 s (preAcceptOf g)).ongoing = s.ongoing := by unfold paS1; split <;> rfl
        have e2 : (paS1 s (preAcceptOf g)).proposeQ = s.proposeQ := by unfold paS1; split <;> rfl
        rw [e1, e2, paS1_val, paS1_id]
        ihave Hcoord := coordOwn_congr ρ co _ k s (paS1 s (preAcceptOf g))
          (by unfold paS1; split <;> rfl) (by unfold paS1; split <;> rfl)
          (by unfold paS1; split <;> rfl) (by unfold paS1; split <;> rfl) $$ Hcoord
        iframe Hparti Hval Hcoord Hxs Hprop Hscr
        isplitl
        · iapply (epaxosOwn_at ..).2
          iexists ⟨ispS, crtS, c1S, isp, msR, pvtR, cfs, M, cu, pm⟩
          simp only [epaxosOwnAt]
          iframe # ∗
          ipureintro; exact Hf2
        · ipureintro; exact Hid
      · -- update the copy in place
        have hcnc : committedOrExecuted (paS1 s (preAcceptOf g)) (sint.Z g.Replica, sint.Z g.Instance) =
            false := by
          unfold committedOrExecuted model.committedCopy
          simp only [BitVec.ofInt_toInt, paS1_inst]
          split
          · rw [hc]; simp only
            rw [if_neg]; · rfl
            intro hce; apply hne; refine ⟨c, hc, ?_⟩
            rcases hce with h1 | h1 <;> simp [h1]
          · rfl
        ihave Hcm : cmdsRep sl (preAcceptOf g).cmds $$ []
        · unfold cmdsRep; iexists g.Command; iframe #; ipureintro; exact ⟨rfl, hcmdsOk⟩ -- H2c-R1
        ihave Hc := (copyRep_open ρ xs (sint.Z g.Replica, sint.Z g.Instance) ip (paCopy (some c) (preAcceptOf g) seq (depsOf deps') bvt
            (if chg then model.St.PREACCEPTED else model.St.PREACCEPTED_EQ))).2 $$ [Hiv Hcm Hlb]
        · iexists _; iframe Hiv; dsimp only; iframe; ipureintro
          obtain ⟨-, -, -, -, -, h6, h7, -, h9, h10, h11, h12, h13⟩ := Hivf
          have hnx : ¬ (sint.Z g.Replica, sint.Z g.Instance) ∈ xs.1 := by
            rw [← h13]; intro he; apply hne; exact ⟨c, hc, Or.inr (Or.inr he)⟩
          have hst : (if chg = true then model.St.PREACCEPTED else model.St.PREACCEPTED_EQ) ≠
              model.St.EXECUTED := by
            split <;> simp [model.St.EXECUTED, model.St.PREACCEPTED, model.St.PREACCEPTED_EQ]
          rw [h7] at h9; rw [h6] at h10
          simp [paCopy, preAcceptOf, Hbv, h6, h7, h9, h10, h11, h12, hst, hnx]
        have hpc : s.inst g.Replica g.Instance = some c := hc
        rw [hpc]
        generalize hcn : paCopy (some c) (preAcceptOf g) seq (depsOf deps') bvt
          (if chg then model.St.PREACCEPTED else model.St.PREACCEPTED_EQ) = cn
        ihave Hinsts := Hiclose $$ %((paS1 s (preAcceptOf g)).setInst g.Replica g.Instance cn) %cn [] Hc
        · ipureintro
          refine ⟨by simp [model.RState.setInst], fun q' i' hne' => ?_⟩
          simp only [model.RState.setInst, hne', ↓reduceIte]
        have hcn_nc : (cn.status = model.St.COMMITTED ∨ cn.status = model.St.EXECUTED) = False := by
          rw [← hcn]; simp only [paCopy]
          split <;> simp [model.St.EXECUTED, model.St.PREACCEPTED, model.St.PREACCEPTED_EQ,
            model.St.COMMITTED]
        have hco : committedOrExecuted ((paS1 s (preAcceptOf g)).setInst g.Replica g.Instance cn) =
            committedOrExecuted (paS1 s (preAcceptOf g)) := by
          funext n
          by_cases hn : n = (sint.Z g.Replica, sint.Z g.Instance)
          · subst hn
            have h1 := committedOrExecuted_setInst_self (paS1 s (preAcceptOf g)) g.Replica g.Instance
              cn hbox
            rw [hcnc]
            cases hx : committedOrExecuted ((paS1 s (preAcceptOf g)).setInst g.Replica g.Instance cn)
                (sint.Z g.Replica, sint.Z g.Instance)
            · rfl
            · exfalso; rw [hx, hcn_nc] at h1; simp at h1
          · exact committedOrExecuted_setInst _ _ _ _ n hn
        iright
        isplitr
        · ipureintro; first | rfl | trivial
        isplitr
        · ipureintro; intro c' hc'; obtain rfl := Option.some.inj hc'
          simp only [model.slt, decide_eq_false_iff_not]; rw [← hcb]; exact Hif
        iframe
        iapply (epaxosOwn_at ..).2
        iexists ⟨ispS, crtS, c1S, isp, msR, pvtR, cfs, M, cu, pm⟩
        simp only [epaxosOwnAt, hco, setInst_crtInstance, setInst_crt, setInst_confAt,
          setInst_maxSeqK0]
        iframe # ∗
        ipureintro
        refine epFacts_setInst xs _ isp cfs M M cu pm g.Replica g.Instance cn ip hbox ?_ hMq'
          (fun _ _ => rfl) ?_
        · simpa [epFacts] using Hf2
        · intro hn; exfalso
          have := Hf2.2.2.2.2.2.2.2.2.2.1 _ hn
          rw [hcnc] at this; cases this
  icases HQ with (⟨%Hv, Hown, Hpend⟩ | ⟨%Hv, %Hnb, Hep, Hpend, Hparti, Hval, Hcoord, Hxs, Hprop, Hscr, e,
    preAccept, seq, deps, base, status, LeaderId, Replica, Instance, Ballot, Command, Seq, Base, Deps⟩)
  · subst Hv
    wp_auto
    iapply HΦ; iframe
  · subst Hv
    wp_auto
    wp_apply (wp_updateConflicts ρ k r gR h xs _ sl g.Command g.Replica g.Instance g.Seq
      (by rw [← hcmds]; exact hcmdsOk) ⟨hq0, hq3⟩) $$ [$Hae $Hep $Hsl] as Hep
    -- `recordInstanceMetadata(e.InstanceSpace[Replica][Instance])`: a load of the slot
    icases (epaxosOwn_open ..).1 $$ Hep with ⟨%ispS3, %crtS3, %c1S3, %isp3, %msR3, %pvtR3, %cfs3,
      %M3, %cu3, %pm3, #HR3, #HnoC3, #HispS3, #Hisp3, #HcrtS3, #Hc1S3, #Hcfs3, #HmsR3, #HpvtR3, Hcu,
      Hcrt, HM, HMe, Hrows, Hinsts, Hmono, Hconfs, Hms, Hpm, Hrest, %Hf3⟩
    icombine HispS HispS3 gives %Heq
    subst Heq
    icombine Hisp Hisp3 gives %Heq2
    subst Heq2
    icases rows_acc' M3 isp _ sq hsq $$ Hrows with ⟨Hrow, Hrows⟩
    icases (replica.rowOwn_open ..).1 $$ Hrow with ⟨%ptrs3, Hrow, %Hrowf3⟩
    ihave %Hrl3 := ownSlice_len _ _ _ $$ Hrow
    obtain ⟨pp, hpp⟩ : ∃ pp, ptrs3[(sint.Z (W64 (sint.Z g.Instance))).toNat]? = some pp :=
      ⟨_, List.getElem?_eq_getElem (by rw [hiw, Hrowf3.1]; unfold nSlots; unfold model.SLOTS at hiS; omega)⟩
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 (sint.Z g.Replica)) ∧
        sint.Z (W64 (sint.Z g.Replica)) < sint.Z ispS.len by
      rw [hqw]; have := HispSlen.1; rw [Hf.1] at this; word)]
    wp_apply wp_load_slice_index (t := go.GoType.SliceType (go.GoType.PointerType
      src.gryff.Instance.ty)) ispS _ isp _ sq (by rw [hqw]; omega) $$ [$Hisp] as -
    · ipureintro; exact hsq
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 (sint.Z g.Instance)) ∧
        sint.Z (W64 (sint.Z g.Instance)) < sint.Z sq.len by
      rw [hiw]; have := Hrl3.1; have := Hrl3.2; rw [Hrowf3.1] at *; unfold nSlots at *
      unfold model.SLOTS at hiS; word)]
    wp_apply wp_load_slice_index (t := go.GoType.PointerType src.gryff.Instance.ty) sq _ ptrs3 _ pp
      (by rw [hiw]; omega) $$ [$Hrow] as Hrow
    · ipureintro; exact hpp
    wp_apply (wp_recordInstanceMetadata h r gR) $$ [$HR' $HgR $HDur]
    ihave Hrow := (replica.rowOwn_open M3 _ sq).2 $$ [Hrow]
    · iexists ptrs3; iframe; ipureintro; exact Hrowf3
    ihave Hrows := Hrows $$ %M3 %(fun _ _ _ => rfl) Hrow
    wp_apply (wp_recordCommands h r gR) $$ [$HR' $HgR $HDur]
    wp_apply (wp_sync h r gR) $$ [$HR' $HgR $HDur]
    -- the reply's condition (`changed || uncommittedDeps || Replica != LeaderId || !isInitialBallot`)
    obtain ⟨o, hs'eq, rfl, hsend⟩ : ∃ o, s' = model.updateConflicts
        ((paS1 s (preAcceptOf g)).setInst g.Replica g.Instance
          (paCopy (s.inst g.Replica g.Instance) (preAcceptOf g) seq (depsOf deps') bvt
            (if chg then model.St.PREACCEPTED else model.St.PREACCEPTED_EQ)))
          (preAcceptOf g).cmds g.Replica g.Instance g.Seq ∧ outs = [o] ∧
        (if paReplyCond (paS1 s (preAcceptOf g)) (preAcceptOf g) (depsOf deps') chg then
          model.sendPeer s' g.LeaderId (.preAcceptReply
            ⟨g.Replica, g.Instance, model.TRUE, g.Ballot, seq, depsOf deps', bvt⟩) = some o
         else model.sendPeer s' g.LeaderId (.preAcceptOK ⟨g.Instance⟩) = some o) := by
      rcases hrest with ⟨c, o, hc', hlt, -⟩ | ⟨-, hr⟩
      · have := Hnb c hc'
        have h2 : model.slt (preAcceptOf g).ballot c.ballot = false := this
        rw [h2] at hlt; cases hlt
      · exact hr
    have hsf : s'.id = s.id ∧ s'.tag = (paS1 s (preAcceptOf g)).tag ∧ s'.ongoing = s.ongoing ∧
        s'.val = s.val ∧ s'.proposeQ = s.proposeQ ∧ s'.maxN = s.maxN ∧ s'.rops = s.rops ∧
        s'.wops = s.wops ∧ s'.ongoingReqs = s.ongoingReqs := by
      subst hs'eq; rw [updateConflicts_eq]
      split <;> simp only [ucStep, model.RState.setInst] <;> unfold paS1 <;> split <;>
        simp [model.RState.setCrt]
    have hid' : s'.id = rid32 k := by rw [hsf.1, Hid]
    have hrc_eq : paReplyCond (paS1 s (preAcceptOf g)) (preAcceptOf g) (depsOf deps') chg =
        (((chg.or (paUnc (paS1 s (preAcceptOf g)) (depsOf deps'))).or
          (decide (g.Replica ≠ g.LeaderId))).or (!model.isInitialBallot g.Ballot)) := rfl
    generalize hunc : paUnc (paS1 s (preAcceptOf g)) (depsOf deps') = unc at hrc_eq
    wp_if_destruct
    · wp_if_destruct
      · wp_if_destruct
        · wp_apply wp_isInitialBallot
          cases hib : model.isInitialBallot g.Ballot
          · wp_auto
            rw [if_pos (by rw [hrc_eq]; simp_all)] at hsend
            try wp_auto
            wp_apply (wp_replyPreAccept_a γ ρ k r gR h t s' hid' g.LeaderId _ «$a1_ptr» o [] ?_)
              $$ [$HR' $HgR $Hgen $Hfix $«$a1» $Hpend] as Hpend
            · rw [← hsend]; congr 2
              simp only [preAcceptReplyOf, Hbv]; rfl
            ihave Hep := (epaxosOwn_open ..).2 $$ [Hcu Hcrt HM HMe Hrows Hinsts Hmono Hconfs Hms Hpm Hrest]
            · iexists ispS, crtS3, c1S3, isp, msR3, pvtR3, cfs3, M3, cu3, pm3; iframe # ∗; ipureintro; exact Hf3
            iapply HΦ; iframe Hpend
            iapply handler_close γ ρ k r gR h pa co xs
            isplitr
            · unfold epEnv; iframe #
            unfold parts
            obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8⟩ := hsf
            rw [e1, e2, e3, e4]
            ihave Hcoord := coordOwn_congr ρ co _ k s s' e5 e6 e7 e8 $$ Hcoord
            iframe Hparti Hval Hcoord Hxs Hprop Hscr
            isplitl
            · rw [hs'eq, hcmds]; (try simp only [Bool.false_eq_true, ↓reduceIte]); iexact Hep
            · ipureintro; exact hid'
          · wp_auto
            rw [if_neg (by rw [hrc_eq]; simp_all)] at hsend
            obtain ⟨d, rfl, hld, hdk⟩ := sendPeer_some s' k hid' g.LeaderId _ o hsend
            icases h2Fixed_pok k gR h $$ Hfix with ⟨#HbOE, %cPAO, #HcPAO, #HrcPAO⟩
            wp_auto
            ihave Hm : msgAt «$r0_ptr» (.preAcceptOK ⟨g.Instance⟩) $$ [«$r0»]
            · unfold msgAt; iexists ({ Instance' := g.Instance } : src.epaxosproto.PreAcceptOK); iframe
              ipureintro; rfl
            have hsend' := Replica.SendMsg.wp γ ρ k d r gR h t
              (.preAcceptOK ⟨g.Instance⟩) «$r0_ptr» cPAO [] hdk
            simp only [msgKind, msgTy] at hsend'
            rw [hld]
            wp_method_call
            wp_auto
            wp_apply hsend' $$ [$Hgen $HgR $HrcPAO $Hm $Hpend] as ⟨-, Hpend⟩
            ihave Hep := (epaxosOwn_open ..).2 $$ [Hcu Hcrt HM HMe Hrows Hinsts Hmono Hconfs Hms Hpm Hrest]
            · iexists ispS, crtS3, c1S3, isp, msR3, pvtR3, cfs3, M3, cu3, pm3; iframe # ∗; ipureintro; exact Hf3
            iapply HΦ; iframe Hpend
            iapply handler_close γ ρ k r gR h pa co xs
            isplitr
            · unfold epEnv; iframe #
            unfold parts
            obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8⟩ := hsf
            rw [e1, e2, e3, e4]
            ihave Hcoord := coordOwn_congr ρ co _ k s s' e5 e6 e7 e8 $$ Hcoord
            iframe Hparti Hval Hcoord Hxs Hprop Hscr
            isplitl
            · rw [hs'eq, hcmds]; (try simp only [Bool.false_eq_true, ↓reduceIte]); iexact Hep
            · ipureintro; exact hid'
        ·
          rw [if_pos (by rw [hrc_eq]; simp_all)] at hsend
          try wp_auto
          wp_apply (wp_replyPreAccept_a γ ρ k r gR h t s' hid' g.LeaderId _ «$a1_ptr» o [] ?_)
            $$ [$HR' $HgR $Hgen $Hfix $«$a1» $Hpend] as Hpend
          · rw [← hsend]; congr 2
            simp only [preAcceptReplyOf, Hbv]; rfl
          ihave Hep := (epaxosOwn_open ..).2 $$ [Hcu Hcrt HM HMe Hrows Hinsts Hmono Hconfs Hms Hpm Hrest]
          · iexists ispS, crtS3, c1S3, isp, msR3, pvtR3, cfs3, M3, cu3, pm3; iframe # ∗; ipureintro; exact Hf3
          iapply HΦ; iframe Hpend
          iapply handler_close γ ρ k r gR h pa co xs
          isplitr
          · unfold epEnv; iframe #
          unfold parts
          obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8⟩ := hsf
          rw [e1, e2, e3, e4]
          ihave Hcoord := coordOwn_congr ρ co _ k s s' e5 e6 e7 e8 $$ Hcoord
          iframe Hparti Hval Hcoord Hxs Hprop Hscr
          isplitl
          · rw [hs'eq, hcmds]; (try simp only [Bool.false_eq_true, ↓reduceIte]); iexact Hep
          · ipureintro; exact hid'
      ·
        rw [if_pos (by rw [hrc_eq]; simp_all)] at hsend
        try wp_auto
        wp_apply (wp_replyPreAccept_a γ ρ k r gR h t s' hid' g.LeaderId _ «$a1_ptr» o [] ?_)
          $$ [$HR' $HgR $Hgen $Hfix $«$a1» $Hpend] as Hpend
        · rw [← hsend]; congr 2
          simp only [preAcceptReplyOf, Hbv]; rfl
        ihave Hep := (epaxosOwn_open ..).2 $$ [Hcu Hcrt HM HMe Hrows Hinsts Hmono Hconfs Hms Hpm Hrest]
        · iexists ispS, crtS3, c1S3, isp, msR3, pvtR3, cfs3, M3, cu3, pm3; iframe # ∗; ipureintro; exact Hf3
        iapply HΦ; iframe Hpend
        iapply handler_close γ ρ k r gR h pa co xs
        isplitr
        · unfold epEnv; iframe #
        unfold parts
        obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8⟩ := hsf
        rw [e1, e2, e3, e4]
        ihave Hcoord := coordOwn_congr ρ co _ k s s' e5 e6 e7 e8 $$ Hcoord
        iframe Hparti Hval Hcoord Hxs Hprop Hscr
        isplitl
        · rw [hs'eq, hcmds]; (try simp only [Bool.false_eq_true, ↓reduceIte]); iexact Hep
        · ipureintro; exact hid'
    ·
      rw [if_pos (by rw [hrc_eq]; simp_all)] at hsend
      try wp_auto
      wp_apply (wp_replyPreAccept_a γ ρ k r gR h t s' hid' g.LeaderId _ «$a1_ptr» o [] ?_)
        $$ [$HR' $HgR $Hgen $Hfix $«$a1» $Hpend] as Hpend
      · rw [← hsend]; congr 2
        simp only [preAcceptReplyOf, Hbv]; rfl
      ihave Hep := (epaxosOwn_open ..).2 $$ [Hcu Hcrt HM HMe Hrows Hinsts Hmono Hconfs Hms Hpm Hrest]
      · iexists ispS, crtS3, c1S3, isp, msR3, pvtR3, cfs3, M3, cu3, pm3; iframe # ∗; ipureintro; exact Hf3
      iapply HΦ; iframe Hpend
      iapply handler_close γ ρ k r gR h pa co xs
      isplitr
      · unfold epEnv; iframe #
      unfold parts
      obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8⟩ := hsf
      rw [e1, e2, e3, e4]
      ihave Hcoord := coordOwn_congr ρ co _ k s s' e5 e6 e7 e8 $$ Hcoord
      iframe Hparti Hval Hcoord Hxs Hprop Hscr
      isplitl
      · rw [hs'eq, hcmds]; (try simp only [Bool.false_eq_true, ↓reduceIte]); iexact Hep
      · ipureintro; exact hid'

end

end Perennial.gryff.replica2
