/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H2b/Propose.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit H2b: `handlePropose` and `HandleRMW`

`handlePropose(propose)`: a batch of `len(ProposeChan) + 1` proposals (at most `MAX_BATCH`), the
later ones received from `ProposeChan` (owned by the lock: `proposeOwn`, `wp_Len_own`,
`wp_receive_own`), the instance number `crtInstance[Id]++`, then `startPhase1`.
-/
module

public import Dsverify.Proof.gryff.H2b.Phase1
public import Dsverify.Proof.gryff.H2b.Chan
public import Dsverify.GeneratedProof.gryff.examples.gryffnet

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.replica2.h2b

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto
open Perennial.gryff.replica2
open Perennial.gryff.model (RState Copy LB Proposal Msg Ev Out Cmd Deps)
open Perennial.gryff.replica (XS rowOwn nSlots)

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- `handlePropose`'s batch size (`len(ProposeChan) + 1`, at most `MAX_BATCH`). -/
def hpBatch (s : RState) : w64 :=
  let b : w64 := BitVec.ofNat 64 (s.proposeQ.length + 1)
  if model.sgt b model.MAX_BATCH then model.MAX_BATCH else b

/-- The state `startPhase1` starts from in `handlePropose`. -/
def hpS2 (s : RState) : RState :=
  { s.setCrt s.id (s.crt s.id + 1) with proposeQ := s.proposeQ.drop ((hpBatch s).toNat - 1) }

/-- The batch. -/
def hpProps (s : RState) (p : Proposal) : List Proposal := p :: s.proposeQ.take ((hpBatch s).toNat - 1)

theorem hpBatch_props (s : RState) (hq : s.proposeQ.length + 1 < 2 ^ 63) :
    1 ≤ (hpBatch s).toNat ∧ (hpBatch s).toNat ≤ s.proposeQ.length + 1 ∧
      sint.Z (hpBatch s) = (hpBatch s).toNat := by
  unfold hpBatch model.sgt model.slt
  by_cases hc : sint.Z model.MAX_BATCH < sint.Z (BitVec.ofNat 64 (s.proposeQ.length + 1))
  · simp only [hc, decide_true, ↓reduceIte]
    have h1 : sint.Z (BitVec.ofNat 64 (s.proposeQ.length + 1)) = s.proposeQ.length + 1 := by
      rw [show BitVec.ofNat 64 (s.proposeQ.length + 1) = W64 ((s.proposeQ.length + 1 : Nat) : Int)
        from rfl]; word
    rw [h1] at hc
    have : sint.Z model.MAX_BATCH = 5000 := rfl
    refine ⟨by decide, ?_, rfl⟩
    have : model.MAX_BATCH.toNat = 5000 := rfl
    omega
  · simp only [hc, decide_false, Bool.false_eq_true, ↓reduceIte]
    have h1 : (BitVec.ofNat 64 (s.proposeQ.length + 1)).toNat = s.proposeQ.length + 1 := by
      simp only [BitVec.toNat_ofNat]; omega
    rw [h1]
    refine ⟨by omega, Nat.le_refl _, ?_⟩
    rw [show BitVec.ofNat 64 (s.proposeQ.length + 1) = W64 ((s.proposeQ.length + 1 : Nat) : Int)
      from rfl]
    word

theorem set_app_replicate {α : Type} (l : List α) (m : Nat) (z x : α) :
    (l ++ List.replicate (m + 1) z).set l.length x = (l ++ [x]) ++ List.replicate m z := by
  induction l with
  | nil => simp [List.replicate_succ]
  | cons a l ih => simp [ih]

theorem take_succ_of_getElem? {α : Type} (l : List α) (j : Nat) (x : α) (h : l[j]? = some x) :
    l.take (j + 1) = l.take j ++ [x] := by
  rw [List.take_succ, h]; rfl

/-- `handlePropose`'s guards (H2b-R2, H2b-R3) hold at a successful step, which is then
`startPhase1` at `hpS2`. -/
theorem handlePropose_ok {s : RState} {p : Proposal} {r : RState × List Out}
    (h : model.handlePropose s p = .ok r) :
    s.proposeQ.length + 1 < 2 ^ 63 ∧
    committedOrExecuted s (sint.Z s.id, sint.Z (s.crt s.id)) = false ∧
    model.startPhase1 (hpS2 s) s.id (s.crt s.id) 0 (hpProps s p)
      ((hpProps s p).map Proposal.cmd) = .ok r := by
  obtain ⟨h1, h2, h⟩ := model.handlePropose_ok h
  refine ⟨h1, ?_, h⟩
  unfold committedOrExecuted model.committedCopy
  simp only [BitVec.ofInt_toInt]
  split <;> try rfl
  unfold model.slotDecided at h2
  cases hi : s.inst s.id (s.crt s.id) with
  | none => rfl
  | some c => simp only [hi] at h2; simp_all

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [gA : examples.gryffnet.Assumptions] [fa : src.fastrpc.Assumptions] [wire.BufioSpecs GF]
variable [binA : wire.BinaryVarintHyps GF] -- H1-R6 / N-1
variable [strconvA : strconv.Assumptions] -- N-5


set_option goose.wp.extras true

theorem proposeOwn_open (ρ : Repl2Names) (gR : Loc) (ps : List Proposal) :
    proposeOwn (GF := GF) ρ gR ps ⊣⊢ ∃ (ch : Loc) (pps : List Loc),
      gR.[src.genericsmr.Replica, go!"ProposeChan"] ↦□ ch ∗
      isChan ch (ρ.chans "propose") Loc ∗ ownChan (ρ.chans "propose") Loc (.Buffered pps) ∗
      ⌜pps.length = ps.length⌝ ∗
      [∗list] i ↦ pp ∈ pps, ∃ pr, ⌜ps[i]? = some pr⌝ ∗ proposalRep ρ pp pr := by
  unfold proposeOwn; exact .rfl

theorem proposalRep_open (ρ : Repl2Names) (pp : Loc) (pr : Proposal) :
    proposalRep (GF := GF) ρ pp pr ⊣⊢ ∃ (gp : src.genericsmr.Propose) (inner : src.genericsmrproto.Propose),
      pp ↦□ gp ∗ gp.Propose' ↦□ inner ∗ writerIs ρ pr.client gp.Reply' ∗
      ⌜inner.CommandId' = pr.cmdId ∧ cmdOf inner.Command' = pr.cmd ∧ pr.cmd.ok = true⌝ := by
  unfold proposalRep; exact .rfl

instance writerIs_persistent (ρ : Repl2Names) (cid : w32) (w : Loc) :
    Persistent (writerIs ρ cid w : IProp GF) := by
  unfold writerIs; infer_instance

instance proposalRep_persistent (ρ : Repl2Names) (pp : Loc) (pr : Proposal) :
    Persistent (proposalRep ρ pp pr : IProp GF) := by
  unfold proposalRep; infer_instance

theorem props_rep (ρ : Repl2Names) (pp : Loc) (p0 : Proposal) (pps : List Loc) (Q : List Proposal)
    (n : Nat) :
    proposalRep ρ pp p0 ∗ ([∗list] i ↦ x ∈ pps, ∃ pr, ⌜Q[i]? = some pr⌝ ∗ proposalRep ρ x pr) ⊢
      ([∗list] i ↦ x ∈ pp :: pps.take n, ∃ pr, ⌜(p0 :: Q.take n)[i]? = some pr⌝ ∗
        proposalRep ρ x pr : IProp GF) := by
  iintro ⟨Hp, Hs⟩
  iapply BigSepL.bigSepL_cons.2
  isplitl [Hp]
  · iexists p0; iframe; ipureintro; rfl
  ihave Hs := (BigSepL.bigSepL_take_drop (n := n)).1 $$ Hs
  icases Hs with ⟨Hs, -⟩
  iapply BigSepL.bigSepL_mono ?_ $$ Hs
  intro i x hx
  iintro ⟨%pr, %hpr, H⟩
  iexists pr; iframe H; ipureintro
  have hi : i < n := by
    have := (List.getElem?_eq_some_iff.1 hx).1; simp at this; omega
  simp only [List.getElem?_cons_succ, List.getElem?_take, hi, ↓reduceIte, hpr]

theorem props_drop (ρ : Repl2Names) (pps : List Loc) (Q : List Proposal) (n : Nat) :
    ([∗list] i ↦ x ∈ pps, ∃ pr, ⌜Q[i]? = some pr⌝ ∗ proposalRep ρ x pr) ⊢
      ([∗list] i ↦ x ∈ pps.drop n, ∃ pr, ⌜(Q.drop n)[i]? = some pr⌝ ∗
        proposalRep ρ x pr : IProp GF) := by
  iintro Hs
  ihave Hs := (BigSepL.bigSepL_take_drop (n := n)).1 $$ Hs
  icases Hs with ⟨-, Hs⟩
  iapply BigSepL.bigSepL_mono ?_ $$ Hs
  intro i x _
  iintro ⟨%pr, %hpr, H⟩
  iexists pr; iframe H; ipureintro
  simpa [List.getElem?_drop] using hpr

variable [pD : GryffPartiDeps (GF := GF)] in
/-- `handlePropose(propose)` (`hslot`: the new instance's slot is free, H2b-R2; `hq`: the queue's
length fits an `int` batch size, H2b-R3). -/
theorem handlePropose_wp (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r gR h pa co : Loc)
    (xs : XS) (t : List Ev) (s s' : RState) (outs rest : List Out) (pp : Loc) (p0 : Proposal)
    (hstep : model.handlePropose s p0 = .ok (s', outs)) (hid : s.id = rid32 k)
    (hslot : committedOrExecuted s (sint.Z s.id, sint.Z (s.crt s.id)) = false)
    (hq : s.proposeQ.length + 1 < 2 ^ 63) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ epEnv γ ρ k r gR h pa co ∗
        epaxosOwn ρ h r xs s ∗ partiOwn pa (replicaIface r) k s.tag s.ongoing ∗
        valOwn gR s.val ∗ proposeOwn ρ gR s.proposeQ ∗ proposalRep ρ pp p0 ∗
        pendingOuts γ ρ k r t (outs ++ rest) }}
      (App (Val (h @!! go.GoType.PointerType src.gryff.EPaxosRMWHandler.ty @!! go!"handlePropose"))
        (Val #pp))
    {{ RET #(); epaxosOwn ρ h r xs s' ∗ partiOwn pa (replicaIface r) k s'.tag s'.ongoing ∗
        valOwn gR s'.val ∗ proposeOwn ρ gR s'.proposeQ ∗ pendingOuts γ ρ k r t rest }} := by
  replace hstep := (handlePropose_ok hstep).2.2
  wp_start as ⟨#Henv, Hep, Hparti, Hval, Hprop, #Hpp, Hpend⟩
  ihave #Henv' := Henv
  unfold epEnv
  icases Henv' with ⟨#HgR, #Hpa, #Hco, #Hh, #HR, #HId, #HN, #HDur, #Hgen, #Hfix⟩
  icases (proposeOwn_open ..).1 $$ Hprop with ⟨%ch, %pps, #HPC, #Hch, Hoc, %Hpps, #Hpps⟩
  wp_auto
  wp_func_call
  wp_call
  wp_apply (wp_Len_own (t := src.genericsmr.Propose.ty.PointerType) ch (ρ.chans "propose") pps)
    $$ [$Hch $Hoc] as Hoc
  have hbw : (W64 (pps.length : Int) + W64 1) = BitVec.ofNat 64 (s.proposeQ.length + 1) := by
    rw [Hpps]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]
  rw [hbw]
  wp_join iprop(batchSize_ptr ↦ hpBatch s) with [batchSize] as batchSize
  · have hm : sint.Z (W64 5000) = sint.Z model.MAX_BATCH := rfl
    rw [show hpBatch s = W64 5000 by
      have hc : decide (sint.Z model.MAX_BATCH < sint.Z (BitVec.ofNat 64 (s.proposeQ.length + 1)))
          = true := by rw [← hm]; simpa using Hif
      unfold hpBatch; simp only [model.sgt, model.slt, hc, ↓reduceIte]; rfl]
    iframe
  · have hm : sint.Z (W64 5000) = sint.Z model.MAX_BATCH := rfl
    rw [show hpBatch s = BitVec.ofNat 64 (s.proposeQ.length + 1) by
      have hc : decide (sint.Z model.MAX_BATCH < sint.Z (BitVec.ofNat 64 (s.proposeQ.length + 1)))
          = false := by rw [← hm]; simpa using Hif
      unfold hpBatch; simp only [model.sgt, model.slt, hc, Bool.false_eq_true, ↓reduceIte]]
    iframe
  -- `instNo := crtInstance[Id]; crtInstance[Id]++`
  obtain ⟨seq, deps, ch0, hupd, hne, hbox, hs', hbc⟩ :=
    startPhase1_cases _ _ _ _ _ _ _ _ hstep
  have hb' := of_decide_eq_true hbox
  obtain ⟨-, -, hi0, hiS⟩ := hb'
  icases (epaxosOwn_open ..).1 $$ Hep with ⟨%ispS, %crtS, %c1S, %isp, %msR, %pvtR, %cfs, %M, %cu,
    %pm, #HR', #HnoC, #HispS, #Hisp, #HcrtS, #Hc1S, #Hcfs, #HmsR, #HpvtR, Hcu, Hcrt, HM, HMe,
    Hrows, Hinsts, Hmono, Hconfs, Hms, Hpm, Hrest, %Hf⟩
  have hcrtlen := Hf.2.2.1
  have hkw : sint.Z (W64 (sint.Z (rid32 k))) = k.val := by
    have := k.isLt; simp only [rid32]; word
  have hkn : (rid32 k).toNat = k.val := by
    have := k.isLt; simp only [rid32]; word
  have hcq : s.crtInstance[k.val]? = some (s.crt s.id) := by
    rw [hid]; simp only [model.RState.crt, hkn, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_getElem (by rw [hcrtlen]; exact k.isLt)]; rfl
  ihave %Hcrtlen := ownSlice_len _ _ _ $$ Hcrt
  have hb2 : 0 ≤ sint.Z (W64 (sint.Z (rid32 k))) ∧ sint.Z (W64 (sint.Z (rid32 k))) < sint.Z crtS.len := by
    rw [hkw]; have := Hcrtlen.1; rw [hcrtlen] at this; have := k.isLt; word
  wp_auto
  rw [ite_eq_left hb2]
  wp_apply wp_load_slice_index (t := go.int32) crtS _ _ _ (s.crt s.id) (by rw [hkw]; omega)
    $$ [$Hcrt] as Hcrt
  · ipureintro; rw [hkw]; exact hcq
  rw [ite_eq_left hb2]
  wp_auto
  rw [ite_eq_left hb2]
  wp_apply wp_load_slice_index (t := go.int32) crtS _ _ _ (s.crt s.id) (by rw [hkw]; omega)
    $$ [$Hcrt] as Hcrt
  · ipureintro; rw [hkw]; exact hcq
  wp_apply wp_store_slice_index (t := go.int32) crtS _ _ (s.crt s.id + W32 1) $$ [$Hcrt] as Hcrt
  · ipureintro; rw [hkw, hcrtlen]; exact ⟨by omega, by have := k.isLt; omega⟩
  have hcrt1 : sint.Z (s.crt s.id + 1) = sint.Z (s.crt s.id) + 1 := by unfold model.SLOTS at hiS; word
  ihave >Hmono := crt_monos_update ρ s s.id (s.crt s.id + 1) ?_ $$ Hmono
  · rw [hcrt1]; omega
  rw [hkw, show W32 1 = (1 : w32) from rfl]
  -- the two `dlog.Printf`s
  ihave #Hdlog : globalAddr gryff.src.dlog.DLOG ↦□ false $$ []
  · iapply replica.dlog_init_access; iPkgInit
  wp_apply wp_slice_literal (V := GoInterface) _
  isplitr
  · ipureintro; rfl
  iintro %_ ⟨-, -⟩
  wp_auto
  wp_apply replica.wp_dlog_Printf $$ [$Hdlog]
  wp_apply wp_slice_literal (V := GoInterface) _
  isplitr
  · ipureintro; rfl
  iintro %_ ⟨-, -⟩
  wp_auto
  wp_apply replica.wp_dlog_Printf $$ [$Hdlog]
  -- `cmds`, `proposals`; the first proposal
  obtain ⟨hn1, hnQ, hnZ⟩ := hpBatch_props s hq
  wp_apply (wp_slice_make2 (V := src.state.Command) (hpBatch s)) as %csl ⟨Hcsl, -⟩
  · ipureintro; omega
  wp_apply (wp_slice_make2 (V := Loc) (hpBatch s)) as %psl ⟨Hpsl, -⟩
  · ipureintro; omega
  icases (proposalRep_open ..).1 $$ Hpp with ⟨%gp, %inner, #Hgp, #Hin, #Hw, %Hpf⟩
  iStructNamed Hgp
  iStructNamed Hin
  wp_apply (IntoValTyped.wp_load (t := src.genericsmrproto.Propose.ty.PointerType) _ _ _)
    $$ [$Propose] as -
  ihave %HcslL := ownSlice_len _ _ _ $$ Hcsl
  ihave %HpslL := ownSlice_len _ _ _ $$ Hpsl
  have hb0c : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z csl.len := by
    have := HcslL.1; simp only [List.length_replicate, sint.nat] at this; word
  have hb0p : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z psl.len := by
    have := HpslL.1; simp only [List.length_replicate, sint.nat] at this; word
  rw [ite_eq_left hb0c]
  wp_apply wp_store_slice_index (t := src.state.Command.ty) csl _ _ inner.Command' $$ [$Hcsl] as Hcsl
  · ipureintro; simp only [List.length_replicate, sint.nat] at HcslL ⊢; word
  rw [ite_eq_left hb0p]
  wp_apply wp_store_slice_index (t := src.genericsmr.Propose.ty.PointerType) psl _ _ pp $$ [$Hpsl]
    as Hpsl
  · ipureintro; simp only [List.length_replicate, sint.nat] at HpslL ⊢; word
  iclear Propose Reply CommandId Command Timestamp
  -- the batch's later proposals, from `ProposeChan`
  have hB : sint.nat (hpBatch s) = (hpBatch s).toNat := by simp only [sint.nat, hnZ]; omega
  rw [hB] at HcslL HpslL ⊢
  generalize hBdef : (hpBatch s).toNat = B at hn1 hnQ hnZ HcslL HpslL ⊢
  ihave HI : (∃ j : Nat, "%Hj" ∷ ⌜1 ≤ j ∧ j ≤ B⌝ ∗ "i" ∷ i_ptr ↦ W64 (j : Int) ∗
      "Hoc" ∷ ownChan (ρ.chans "propose") Loc (.Buffered (pps.drop (j - 1))) ∗
      "Hcsl" ∷ (∃ gcs : List src.state.Command, csl ↦* (gcs ++ List.replicate (B - j) (zero_val _)) ∗
        ⌜gcs.length = j ∧ gcs.map cmdOf = ((hpProps s p0).take j).map Proposal.cmd ∧
          model.cmdsOk (gcs.map cmdOf) = true⌝) ∗
      "Hpsl" ∷ psl ↦* ((pp :: pps).take j ++ List.replicate (B - j) (zero_val Loc)) : IProp GF)
    $$ [i Hoc Hcsl Hpsl]
  · iexists 1
    iframe i
    isplitr
    · ipureintro; omega
    obtain ⟨B', rfl⟩ : ∃ B', B = B' + 1 := ⟨B - 1, by omega⟩
    simp only [List.replicate_succ, List.set_cons_zero, Nat.sub_zero, List.drop_zero,
      List.take_succ_cons, List.take_zero, Nat.add_sub_cancel, Nat.sub_self, List.cons_append,
      List.nil_append]
    iframe Hoc Hpsl
    iexists [inner.Command']
    simp only [List.cons_append, List.nil_append]
    iframe Hcsl
    ipureintro
    simp only [hpProps, List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, Hpf.2.1]
    refine ⟨rfl, trivial, ?_⟩
    simp [model.cmdsOk, Hpf.2.1, Hpf.2.2]

  wp_for HI
  wp_if_destruct
  · have hjB : j < B := by
      rw [hnZ] at Hif; word
    obtain ⟨pj, hpj⟩ : ∃ pj, pps[j - 1]? = some pj :=
      ⟨_, List.getElem?_eq_getElem (by rw [Hpps]; omega)⟩
    have hlt : j - 1 < pps.length := by rw [Hpps]; omega
    have hdrop : pps.drop (j - 1) = pj :: pps.drop j := by
      rw [List.drop_eq_getElem_cons hlt]
      have : pps[j - 1] = pj := by simpa [List.getElem?_eq_getElem hlt] using hpj
      rw [this, show j - 1 + 1 = j by omega]
    rw [hdrop]
    wp_apply (wp_receive_own (t := src.genericsmr.Propose.ty.PointerType) ch (ρ.chans "propose")
      pj (pps.drop j)) $$ [$Hch $Hoc] as Hoc
    ihave Hpj := BigSepL.bigSepL_lookup (Φ := fun i pp => iprop(∃ pr, ⌜s.proposeQ[i]? = some pr⌝ ∗
      proposalRep ρ pp pr)) hpj $$ Hpps
    icases Hpj with ⟨%prj, %hprj, Hprj⟩
    icases (proposalRep_open ..).1 $$ Hprj with ⟨%gpj, %innerj, #Hgpj, #Hinj, #Hwj, %Hpfj⟩
    iStructNamed Hgpj
    iStructNamed Hinj
    wp_auto
    wp_apply wp_slice_literal (V := GoInterface) _
    isplitr
    · ipureintro; rfl
    iintro %_ ⟨-, -⟩
    wp_auto
    wp_apply replica.wp_dlog_Printf $$ [$Hdlog]
    have hjw : sint.Z (W64 (j : Int)) = j := by word
    have hbc : 0 ≤ sint.Z (W64 (j : Int)) ∧ sint.Z (W64 (j : Int)) < sint.Z csl.len := by
      rw [hjw]; have h1 := HcslL.1; have h2 := HcslL.2; rw [List.length_replicate] at h1
      have h3 : ((sint.nat csl.len : Nat) : Int) = sint.Z csl.len := Int.toNat_of_nonneg h2
      constructor <;> omega
    have hbp : 0 ≤ sint.Z (W64 (j : Int)) ∧ sint.Z (W64 (j : Int)) < sint.Z psl.len := by
      rw [hjw]; have h1 := HpslL.1; have h2 := HpslL.2; rw [List.length_replicate] at h1
      have h3 : ((sint.nat psl.len : Nat) : Int) = sint.Z psl.len := Int.toNat_of_nonneg h2
      constructor <;> omega
    icases Hcsl with ⟨%gcs, Hcsl, %Hgcs⟩
    rw [ite_eq_left hbc]
    wp_apply wp_store_slice_index (t := src.state.Command.ty) csl _ _ innerj.Command' $$ [$Hcsl]
      as Hcsl
    · ipureintro; rw [hjw, List.length_append, List.length_replicate, Hgcs.1]; omega
    rw [ite_eq_left hbp]
    wp_apply wp_store_slice_index (t := src.genericsmr.Propose.ty.PointerType) psl _ _ pj $$ [$Hpsl]
      as Hpsl
    · ipureintro
      rw [hjw, List.length_append, List.length_replicate, List.length_take, List.length_cons, Hpps]
      omega
    wp_for_post
    iframe
    iexists (j + 1)
    rw [show W64 ((j + 1 : Nat) : Int) = W64 (j : Int) + W64 1 by word]
    iframe i
    isplitr
    · ipureintro; omega
    rw [show j + 1 - 1 = j by omega, hjw, show (j : Int).toNat = j by omega]
    iframe Hoc
    have hBj : B - j = (B - (j + 1)) + 1 := by omega
    have hp1 : (pp :: pps)[j]? = some pj := by
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      simpa using hpj
    have hp2 : (hpProps s p0)[j]? = some prj := by
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      simp only [hpProps, List.getElem?_cons_succ]
      rw [List.getElem?_take_of_lt (by omega)]
      simpa using hprj
    isplitl [Hcsl]
    · iexists gcs ++ [innerj.Command']
      rw [hBj, ← Hgcs.1, set_app_replicate, Hgcs.1]
      iframe Hcsl
      ipureintro
      refine ⟨by simp [Hgcs.1], ?_, ?_⟩
      · rw [take_succ_of_getElem? _ _ _ hp2, List.map_append, List.map_append, Hgcs.2.1]
        simp [Hpfj.2.1]
      · have := Hgcs.2.2
        simp only [model.cmdsOk, List.all_eq_true, List.map_append, List.mem_append, List.mem_map] at this ⊢
        rintro c (hc | hc)
        · exact this c hc
        · obtain ⟨g, hg, rfl⟩ := hc; simp at hg; subst hg; rw [Hpfj.2.1]; exact Hpfj.2.2
    · have hlen : ((pp :: pps).take j).length = j := by
        simp only [List.length_take, List.length_cons]; omega
      have hL : ((pp :: pps).take j ++ List.replicate (B - j) (zero_val Loc)).set j pj =
          (pp :: pps).take (j + 1) ++ List.replicate (B - (j + 1)) (zero_val Loc) := by
        have e := set_app_replicate ((pp :: pps).take j) (B - (j + 1)) (zero_val Loc) pj
        rw [hlen] at e
        rw [hBj, e, take_succ_of_getElem? _ _ _ hp1]
      rw [← hL]
      iexact Hpsl
  · have hjB : B = j := by
      rw [hnZ] at Hif; have := Hj.2; word
    subst hjB
    icases Hcsl with ⟨%gcs, Hcsl, %Hgcs⟩
    simp only [Nat.sub_self, List.replicate_zero, List.append_nil]
    ihave >#Hgs := ownSlice_persist csl _ gcs $$ Hcsl
    have hlenP : (hpProps s p0).length = B := by
      simp only [hpProps, List.length_cons, List.length_take, hBdef]; omega
    have hmap : gcs.map cmdOf = (hpProps s p0).map Proposal.cmd := by
      rw [Hgcs.2.1, List.take_of_length_le (by omega)]
    ihave #Hcr : cmdsRep csl ((hpProps s p0).map Proposal.cmd) $$ []
    · iapply (cmdsRep_open ..).2; iexists gcs; iframe Hgs; ipureintro
      refine ⟨hmap, ?_⟩; rw [← hmap]; exact Hgcs.2.2
    obtain ⟨B', rfl⟩ : ∃ B', B = B' + 1 := ⟨B - 1, by omega⟩
    ihave >#Hpsl := ownSlice_persist psl _ _ $$ Hpsl -- H2b-R1
    ihave #Hprs : proposalsRep ρ psl (hpProps s p0) $$ []
    · unfold proposalsRep
      iexists pp :: pps.take B'
      simp only [List.take_succ_cons]
      iframe Hpsl
      isplitr
      · ipureintro; simp only [hpProps, List.length_cons, List.length_take, hBdef]; omega
      simp only [hpProps, hBdef, Nat.add_sub_cancel]
      isplitr
      · ipureintro; intro hnil; cases hnil -- H2c-R2: a batch is non-empty
      iapply props_rep $$ [Hpp Hpps]
      iframe Hpp Hpps
    -- close the EPaxos part at `hpS2 s`
    have hcrtI : (hpS2 s).crtInstance = s.crtInstance.set k.val (s.crt s.id + 1) := by
      simp only [hpS2, model.RState.setCrt, hid, hkn]
    have hcrtEq : ∀ x, (hpS2 s).crt x = (s.setCrt s.id (s.crt s.id + 1)).crt x := fun _ => rfl
    have hinstEq : (hpS2 s).inst = s.inst := rfl
    have hcoEq : committedOrExecuted (hpS2 s) = committedOrExecuted s := rfl
    have hconfEq : ∀ q, (hpS2 s).confAt q = s.confAt q := fun _ => rfl
    have hmsEq : (hpS2 s).maxSeqK0 = s.maxSeqK0 := rfl
    ihave Hep : epaxosOwn ρ h r xs (hpS2 s) $$ [Hcu Hcrt HM HMe Hrows Hinsts Hmono Hconfs Hms Hpm Hrest]
    · iapply (epaxosOwn_open ..).2
      iexists ispS, crtS, c1S, isp, msR, pvtR, cfs, M, cu, pm
      simp only [hcrtI, hcrtEq, hcoEq, hconfEq, hmsEq, instsRep, hinstEq, Int.toNat_natCast]
      iframe # ∗
      ipureintro
      unfold epFacts
      refine ⟨Hf.1, Hf.2.1, by rw [hcrtI, List.length_set]; exact Hf.2.2.1, Hf.2.2.2⟩
    -- `startPhase1`
    have hstep' : model.startPhase1 (hpS2 s) (rid32 k) (s.crt s.id) (W32 0) (hpProps s p0)
        ((hpProps s p0).map Proposal.cmd) = .ok (s', outs) := by rw [← hid]; exact hstep
    have hokP : model.cmdsOk ((hpProps s p0).map Proposal.cmd) = true := by
      rw [← hmap]; exact Hgcs.2.2
    have hslot2 : committedOrExecuted (hpS2 s) (sint.Z (rid32 k), sint.Z (s.crt s.id)) = false := by
      rw [← hid]; exact hslot
    have hspec := startPhase1_wp γ ρ k r gR h pa co xs t (hpS2 s) s' outs rest (rid32 k) (s.crt s.id)
      (W32 0) psl (hpProps s p0) csl ((hpProps s p0).map Proposal.cmd) (hpBatch s) hstep' hid hokP hslot2
    have htag : (hpS2 s).tag = s.tag := rfl
    have hong : (hpS2 s).ongoing = s.ongoing := rfl
    have hval : (hpS2 s).val = s.val := rfl
    simp only [htag, hong, hval] at hspec
    ihave #HenvF : epEnv γ ρ k r gR h pa co $$ []
    · unfold epEnv; iexact Henv
    wp_apply hspec $$ [$HenvF $Hep $Hparti $Hval $Hprs $Hcr $Hpend] as ⟨Hep, Hparti, Hval, Hpend⟩
    -- the post
    have hs'f : s'.tag = s.tag ∧ s'.ongoing = s.ongoing ∧ s'.val = s.val ∧
        s'.proposeQ = s.proposeQ.drop B' := by
      rw [hs']
      obtain ⟨cf, ms, hsh⟩ := updateConflicts_shape ((hpS2 s).setInst s.id (s.crt s.id)
        (sp1Copy s.id (s.crt s.id) 0 (hpProps s p0) (List.map Proposal.cmd (hpProps s p0)) seq deps
          (hpS2 s).storeVT)) (List.map Proposal.cmd (hpProps s p0)) s.id (s.crt s.id) seq
      rw [hsh]
      simp only [model.RState.setInst, hpS2, model.RState.setCrt, hBdef, Nat.add_sub_cancel,
        _root_.and_self]

    iapply HΦ
    rw [hs'f.1, hs'f.2.1, hs'f.2.2.1, hs'f.2.2.2]
    iframe Hep Hparti Hval Hpend
    iapply (proposeOwn_open ..).2
    iexists ch, pps.drop B'
    simp only [Nat.add_sub_cancel]
    iframe HPC Hch Hoc
    isplitr
    · ipureintro; simp [Hpps]
    iapply props_drop $$ Hpps

/-- **H2b-R2** (hub request): a new proposal's slot `(Id, crtInstance[Id])` holds no copy. Not
derivable from `stepSpec`'s precondition (any `s` with `stepR k s e = .ok`); the requested model
guard (`model.handlePropose`: `dead` when the slot is occupied) makes it a consequence of the step's
success. -/
theorem handlePropose_slot_free (k : Fin 3) (s s' : RState) (p : Proposal) (outs : List Out)
    (h : model.handlePropose s p = .ok (s', outs)) :
    committedOrExecuted s (sint.Z s.id, sint.Z (s.crt s.id)) = false :=
  (handlePropose_ok h).2.1

/-- **H2b-R3** (hub request): `ProposeChan`'s contents fit an `int` batch size. -/
theorem proposeQ_small (k : Fin 3) (s s' : RState) (p : Proposal) (outs : List Out)
    (h : model.handlePropose s p = .ok (s', outs)) : s.proposeQ.length + 1 < 2 ^ 63 :=
  (handlePropose_ok h).1

/-- The model's RMW request step: the guards, then `handlePropose` at the ghost-updated state. -/
theorem stepRMW_cases (k : Fin 3) (s s' : RState) (g : src.gryffproto.RMW) (outs : List Out)
    (h : model.stepR k s (rmwEvOf g) = .ok (s', outs)) :
    g.K' = 0 ∧ model.handlePropose { s with nReqs := s.nReqs + 1, used := (g.ClientId', g.RequestId') :: s.used }
      { cmdId := g.RequestId', client := g.ClientId',
        cmd := { op := model.opCAS, k := g.K', v := g.NewValue', oldV := g.OldValue' } } =
      .ok (s', outs) := by
  simp only [model.stepR, rmwEvOf, model.stepClientRMW] at h
  split at h
  · cases h
  · next hc =>
    split at h
    · cases h
    · split at h
      · cases h
      · refine ⟨?_, h⟩
        have hc' : (g.K' == 0 && model.slt (depOf g.D').key 0 && model.sge g.ClientId' 0) = true := by
          cases hb : (g.K' == 0 && model.slt (depOf g.D').key 0 && model.sge g.ClientId' 0)
          · simp only [Bool.not_eq_true'] at hc; exact absurd hb hc
          · rfl
        simp only [Bool.and_eq_true, beq_iff_eq] at hc'
        exact hc'.1.1

variable [pD : GryffPartiDeps (GF := GF)] in
/-- **`HandleRMW(rmw)`** (the frozen `HandleRMW.wp`'s statement). -/
theorem HandleRMW_wp' (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r h p w : Loc)
    (g : src.gryffproto.RMW) :
    stepSpec γ ρ k r (App (epM h go!"HandleRMW") (Val #p))
      iprop(handlerOf r h ∗ p ↦ g ∗ writerIs ρ g.ClientId' w) (rmwEvOf g) := by
  intro t s s' outs hstep
  obtain ⟨hK, hstep⟩ := stepRMW_cases k s s' g outs hstep
  simp only [epM]
  wp_start as ⟨Hrep, Hown, Hpend, ⟨Hh, Hg, #Hw⟩⟩
  generalize hs1 : ({ s with nReqs := s.nReqs + 1, used := (g.ClientId', g.RequestId') :: s.used }
    : RState) = s1 at hstep
  ihave Hown : replicaOwn ρ k r s1 $$ [Hown]
  · unfold replicaOwn
    icases Hown with ⟨%xs, Hown⟩
    iexists xs
    rw [← hs1]
    iapply replicaOwnX_ghost $$ Hown
  icases handler_open γ ρ k r h s1 $$ [$Hrep $Hh $Hown] with ⟨%gR, %pa, %co, %xs, #Henv, Hparts⟩
  unfold parts
  icases Hparts with ⟨Hparti, Hval, Hcoord, Hep, Hxs, Hprop, Hscr, %Hid⟩
  ihave #Henv' := Henv
  unfold epEnv
  icases Henv' with ⟨#HgR, #Hpa, #Hco, #Hh, #HR, #HId, #HN, #HDur, #Hgen, #Hfix⟩
  wp_auto
  ihave #Hdlog : globalAddr gryff.src.dlog.DLOG ↦□ false $$ []
  · iapply replica.dlog_init_access; iPkgInit
  wp_apply wp_slice_literal (V := GoInterface) _
  isplitr
  · ipureintro; rfl
  iintro %_ ⟨-, -⟩
  wp_auto
  wp_apply replica.wp_dlog_Printf $$ [$Hdlog]
  wp_method_call
  wp_auto
  have hspec := Replica.GetClientWriter.wp γ ρ k r gR h g.ClientId' w
  simp only [genM] at hspec
  wp_apply hspec $$ [$Hgen $Hw]
  -- the proposal, persistent
  irename «$r0» => Hgp
  irename «$v0» => Hin
  imod (typedPointsto_dfractional _ _).dfractional_persist (DFrac.own 1) $$ Hgp with #Hgp
  imod (typedPointsto_dfractional _ _).dfractional_persist (DFrac.own 1) $$ Hin with #Hin
  let c0 : Cmd := { op := model.opCAS, k := g.K', v := g.NewValue', oldV := g.OldValue' }
  let p0 : Proposal := { cmdId := g.RequestId', client := g.ClientId', cmd := c0 }
  ihave #Hpp : proposalRep ρ «$r0_ptr» p0 $$ []
  · iapply (proposalRep_open ..).2
    iexists _, _
    iframe Hgp Hin Hw
    ipureintro
    refine ⟨rfl, rfl, ?_⟩
    simp [p0, c0, model.Cmd.ok, hK]
  have hslot := handlePropose_slot_free k s1 s' p0 outs hstep
  have hq := proposeQ_small k s1 s' p0 outs hstep
  rw [← List.append_nil outs]
  ihave #HenvF : epEnv γ ρ k r gR h pa co $$ []
  · unfold epEnv; iexact Henv
  wp_apply (handlePropose_wp γ ρ k r gR h pa co xs t s1 s' outs [] «$r0_ptr» p0 hstep Hid hslot hq)
    $$ [$HenvF $Hep $Hparti $Hval $Hprop $Hpp $Hpend] as ⟨Hep, Hparti, Hval, Hprop, Hpend⟩
  -- the parts back at `s'`
  have hsh : s'.maxN = s1.maxN ∧ s'.rops = s1.rops ∧ s'.wops = s1.wops ∧
      s'.ongoingReqs = s1.ongoingReqs ∧ s'.id = s1.id := by
    replace hstep := (handlePropose_ok hstep).2.2
    obtain ⟨_, _, _, _, _, _, hs', _⟩ := startPhase1_cases _ _ _ _ _ _ _ _ hstep
    rw [hs']
    obtain ⟨cf, ms, hsh⟩ := updateConflicts_shape ((hpS2 s1).setInst s1.id (s1.crt s1.id) _) _ _ _ _
    rw [hsh]
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  ihave Hcoord := coordOwn_congr ρ co _ k s1 s' hsh.1 hsh.2.1 hsh.2.2.1 hsh.2.2.2.1 $$ Hcoord
  iapply HΦ
  iframe Hpend
  iapply handler_close γ ρ k r gR h pa co xs s'
  iframe HenvF
  unfold parts
  iframe
  ipureintro; rw [hsh.2.2.2.2]; exact Hid

end

end Perennial.gryff.replica2.h2b
