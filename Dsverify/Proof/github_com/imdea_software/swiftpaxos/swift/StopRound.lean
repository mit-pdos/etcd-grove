/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/StopRound.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
**`stopDescs`' round, ghost steps** (round 18, sv-swb; notes/prove-swift.md §24): what the
`IterCb` closure of a round does to an entry `k ↦ v` of `cmdDescs` it visits (under the shard's
read lock: `IterCbVP`'s pin `cmapPin`), and the reset after the round's `Wait`.

* `swift.descInv_lend`: before reading `desc.active` (a non-atomic read: Go's race semantics
  need the location's ownership across the read), the closure takes the entry's state
  `entS` out of the invariant, leaving the lent marker (`γb`'s token);
* `swift.descInv_return`: after the reads (and the signal's ghost step, if any), it puts the
  state back; the pin keeps `k ↦ v` in the view, and the state's whole `seq` shows the entry
  is the lent one;
* `swift.goA_signal` (round 37, D37/G-lend): the signal's ghost step on a running, unsignalled
  descriptor's lent state (`goA`), with the element of its key the lend deposited at `false`: the
  element at `true`, half to the request (with the signal token), half to the entry;
* `swift.round_reset`: after `Wait`, the round's elements give the authority back at `∅`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.StopDescs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.orcaman.concurrent_map.IterCbP

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section lemmas
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions]

instance swift.descIs_persistent (γd : GName) (d : Loc) (x : sp.CmdId) :
    Persistent (swift.descIs γd d x) := by
  unfold swift.descIs; infer_instance

theorem swift.descN_cmap_sub :
    ↑github_com.orcaman.concurrent_map.cmapN ⊆ (⊤ \ ↑swift.descN : CoPset) := by
  have h : ↑swift.descN ## (↑github_com.orcaman.concurrent_map.cmapN : CoPset) := by
    unfold swift.descN github_com.orcaman.concurrent_map.cmapN
    exact ndot_ne_disjoint nroot (by decide)
  intro e he
  rw [LawfulSet.mem_diff]
  exact ⟨CoPset.mem_full, fun h' => h e ⟨h', he⟩⟩

theorem swift.descN_sub :
    ↑swift.descN ⊆ (⊤ \ ↑github_com.orcaman.concurrent_map.cmapN : CoPset) := by
  have h : ↑swift.descN ## (↑github_com.orcaman.concurrent_map.cmapN : CoPset) := by
    unfold swift.descN github_com.orcaman.concurrent_map.cmapN
    exact ndot_ne_disjoint nroot (by decide)
  intro e he
  rw [LawfulSet.mem_diff]
  exact ⟨CoPset.mem_full, fun h' => h e ⟨he, h'⟩⟩

/-- A whole points-to of a `bool` and any other share of it: impossible. -/
theorem swift.bool_pt_excl (l : Loc) (a b : Bool) (q : Qp) :
    typedPointsto l a (DFrac.own 1) ∗ typedPointsto l b (DFrac.own q) ⊢ (False : IProp netDistGF) := by
  simp only [typedPointsto_unseal, typedPointstoWrap, typedPointstoDef_heap]
  iintro ⟨⟨N1', -⟩, ⟨N2', -⟩⟩
  icombine N1' N2' gives %Hv
  exfalso; have := DFrac.valid_own_op Hv.1; simp at this

/-- Two states of one descriptor: impossible (each holds its `seq`'s outer half, the first a
further share: a home's half, a running goroutine's quarter, a sequential state's half). -/
theorem swift.entS_excl (γ : sp.Names) (DR : Loc → IProp netDistGF)
    (Run Sq : Loc → swift.CommandId → IProp netDistGF)
    (MP : swift.CommandId → GoInterface → IProp netDistGF)
    (hRunSeq : ∀ d y, Run d y ⊢
      typedPointsto (swift.dfld d go!"seq") false (DFrac.own (1 : Qp).half.half) ∗ True)
    (hSq : swift.sqOk γ DR Sq MP)
    (d : Loc) (y y' : swift.CommandId) :
    swift.entS γ DR Run Sq MP d y ∗ swift.entS γ DR Run Sq MP d y' ⊢ False := by
  iintro ⟨H1, H2⟩
  iunfold swift.entS at H1 H2
  icases H1 with ⟨%s, %m1, Hs, -, Hh⟩
  icases H2 with ⟨%s2, %m2, Hs2, -, -⟩
  iunfold swift.entI at Hh
  ihave ⟨%hs, Hw⟩ := typedPointsto_half_combine _ s s2 (1 : Qp) $$ [Hs Hs2]
  · iframe
  subst hs
  ihave ⟨%s3, %q, Hin⟩ : ∃ (s3 : Bool) (q : Qp),
      typedPointsto (swift.dfld d go!"seq") s3 (DFrac.own q) $$ [Hh]
  · icases Hh with (⟨-, Hh⟩ | ⟨%Hs0, Hr⟩ | ⟨%Hs0, Hq⟩)
    · iunfold swift.descHomeS at Hh
      icases Hh with ⟨%m, %sc, %sl, %fa, %a, -, -, -, -, -, -, -, -, Hq, -, -⟩
      iexists s, _; iexact Hq
    · ihave ⟨Hq, -⟩ := hRunSeq d y $$ Hr
      iexists false, _; iexact Hq
    · ihave ⟨%qs, Hq, -⟩ := hSq.2.1 d y $$ Hq
      iexists true, qs; iexact Hq
  iapply swift.bool_pt_excl _ s s3 q $$ [Hw Hin]
  iframe

/-- A refutation under a fupd ends any fupd (round 38). -/
theorem swift.fupd_false_elim (E E' : CoPset) (P : IProp netDistGF) :
    (|={E}=> (False : IProp netDistGF)) ⊢ |={E, E'}=> P := by
  iintro H
  imod H with %h
  exact h.elim

theorem swift.mkOk_desc_inj (d d' : Loc)
    (h : interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #d =
      interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #d') : d = d' := by
  simp only [interface.mkOk] at h
  injection h with h1
  injection h1 with _ h2
  exact go.intoVal_inj h2

/-- **The lend** (see the file header; round 37, D37 and table rev 8 G-lend): the entry `k ↦ v`
(pinned at `π`) gives its state out; it keeps half of the pin, `γb`'s half at `some π` and the
round's element of `k` at `false` (inserted: `k` is not yet in the round's map). -/
theorem swift.descInv_lend (γ : sp.Names) (γd γn γout : GName) (g : swift.DescG) (ep : swift.EpN)
    (DR : Loc → IProp netDistGF) (Run : Loc → swift.CommandId → IProp netDistGF)
    (str : swift.CommandId → GoString) (k : GoString) (v : GoInterface)
    (π : github_com.orcaman.concurrent_map.PinD) (S : GMap GoString Bool) (hS : S !! k = none) :
    inv swift.descN (swift.descInv γ γd γn γout g ep DR Run str) ∗
      ghostVar g.γst (1 : Qp).half false ∗
      github_com.orcaman.concurrent_map.cmapPin g.γdc k v π ∗
      ghostVar g.γb 1 (none : Option github_com.orcaman.concurrent_map.PinD) ∗
      ghostMapAuth g.γs 1 S ∗ £ 1 ⊢
    |={⊤}=> ghostVar g.γst (1 : Qp).half false ∗
      github_com.orcaman.concurrent_map.cmapPin g.γdc k v π.half ∗
      ghostVar g.γb (1 : Qp).half (some π) ∗ ghostMapAuth g.γs 1 (S.insert k false) ∗
      ∃ (d : Loc) (y : swift.CommandId),
        ⌜v = interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #d ∧ k = str y⌝ ∗
        swift.entS γ DR Run (swift.sqE g) g.mp d y := by
  iintro ⟨#HI, Hst, Hpin, Hb, HS, Hlc⟩
  iinv HI with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑swift.descN) $$ Hlc Hi with Hi
  iunfold swift.descInv at Hi
  icases Hi with ⟨%st, Hst2, Hrest⟩
  icombine Hst Hst2 gives %Hc
  obtain ⟨-, Heq⟩ := Hc
  subst Heq
  simp only [Bool.false_eq_true, ↓reduceIte]
  icases Hrest with ⟨%Mc, Hrest⟩
  icases Hrest with ⟨%q0, Hrest⟩
  icases Hrest with ⟨%L, Hrest⟩
  icases Hrest with ⟨%dm1, Hrest⟩
  icases Hrest with ⟨%W, Hview, HW, %HWd, Hents, HK, Hpool, Hrec, Hled, Hrca⟩
  imod github_com.orcaman.concurrent_map.cmapPin_lookup g.γdc k v π Mc (⊤ \ ↑swift.descN)
    swift.descN_cmap_sub $$ [Hpin Hview] with ⟨%Hk, Hpin, Hview⟩
  · iframe
  icases (BigSepM.bigSepM_delete Hk).1 $$ Hents with ⟨He, Hents⟩
  iunfold swift.descEnt at He
  icases He with ⟨%d, %y, %Hv, Hs⟩
  -- round 38 (table rev 9 T18l): a lock-lent entry holds its lender's token: our pin refutes it
  cases hW : W !! k with
  | some o =>
    obtain ⟨t, ρ, v'⟩ := o
    unfold swift.entW
    icases Hs with ⟨-, Hs⟩
    iunfold swift.entL at Hs
    icases Hs with ⟨%s, %m, -, -, -, Hlk, -, -⟩
    iapply swift.fupd_false_elim
    iapply github_com.orcaman.concurrent_map.cmapLocked_pin_false (⊤ \ ↑swift.descN)
      swift.descN_cmap_sub g.γdc k (some v) t v π Mc $$ [Hlk Hpin Hview]
    iframe
  | none =>
  unfold swift.entW
  icases Hs with (Hs | ⟨%π', Hb2, -, -⟩)
  rotate_left
  · icombine Hb Hb2 gives %Hc
    exact (swift.qp_one_add_le _ Hc.1).elim
  imod ghostVar_update (some π) g.γb none $$ Hb with Hb
  icases (ghostVar_split_half g.γb 1 (some π)).1 $$ Hb with ⟨Hb1, Hb2⟩
  icases (github_com.orcaman.concurrent_map.cmapPin_split g.γdc k v π).1 $$ Hpin with ⟨Hp1, Hp2⟩
  imod ghost_map_insert (GF := netDistGF) (γ := g.γs) k false hS $$ HS with ⟨HS, Hel⟩
  imod Hclose $$ [Hst2 Hview HW Hents HK Hpool Hrec Hled Hrca Hb2 Hp2 Hel] with -
  · inext
    iunfold swift.descInv
    iexists false
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe Hst2
    iexists Mc, q0, L, dm1, W
    iframe Hview HW HK Hpool Hrec Hled Hrca
    isplitr
    · ipureintro; exact HWd
    iapply (BigSepM.bigSepM_delete Hk).2
    iframe Hents
    iunfold swift.descEnt
    iexists d, y
    isplitr
    · ipureintro; exact Hv
    rw [hW]
    unfold swift.entW
    iright; iexists π; iframe Hb2 Hp2 Hel
  imodintro
  iframe Hst Hp1 Hb1 HS
  iexists d, y
  iframe Hs
  ipureintro; exact Hv

/-- **The return** (see the file header; round 37, D37 and G-lend): the lent state `R` (a form of
the entry's state, `hR`) goes back, changed by `upd` with the deposited element of `k` (a plain
return gives the element out; a signal turns it into the request's half and the entry's half);
the pin and `γb` come back whole. -/
theorem swift.descInv_return (γ : sp.Names) (γd γn γout : GName) (g : swift.DescG) (ep : swift.EpN)
    (DR : Loc → IProp netDistGF) (Run : Loc → swift.CommandId → IProp netDistGF)
    (str : swift.CommandId → GoString)
    (hRunSeq : ∀ d y, Run d y ⊢
      typedPointsto (swift.dfld d go!"seq") false (DFrac.own (1 : Qp).half.half) ∗ True)
    (hSq : swift.sqOk γ DR (swift.sqE g) g.mp)
    (k : GoString) (v : GoInterface) (π : github_com.orcaman.concurrent_map.PinD)
    (d : Loc) (y : swift.CommandId)
    (Hv : v = interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #d ∧ k = str y)
    (R X : IProp netDistGF) (hR : R ⊢ swift.entS γ DR Run (swift.sqE g) g.mp d y) :
    inv swift.descN (swift.descInv γ γd γn γout g ep DR Run str) ∗
      ghostVar g.γst (1 : Qp).half false ∗
      github_com.orcaman.concurrent_map.cmapPin g.γdc k v π.half ∗
      ghostVar g.γb (1 : Qp).half (some π) ∗ £ 1 ∗ R ∗
      iprop(R -∗ ghostMapElem g.γs k (DFrac.own 1) false -∗
        |={⊤ \ ↑swift.descN}=> swift.entS γ DR Run (swift.sqE g) g.mp d y ∗ X) ⊢
    |={⊤}=> ghostVar g.γst (1 : Qp).half false ∗
      github_com.orcaman.concurrent_map.cmapPin g.γdc k v π ∗
      ghostVar g.γb 1 (none : Option github_com.orcaman.concurrent_map.PinD) ∗ X := by
  iintro ⟨#HI, Hst, Hpin, Hb, Hlc, HR, Hupd⟩
  iinv HI with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑swift.descN) $$ Hlc Hi with Hi
  iunfold swift.descInv at Hi
  icases Hi with ⟨%st, Hst2, Hrest⟩
  icombine Hst Hst2 gives %Hc
  obtain ⟨-, Heq⟩ := Hc
  subst Heq
  simp only [Bool.false_eq_true, ↓reduceIte]
  icases Hrest with ⟨%Mc, Hrest⟩
  icases Hrest with ⟨%q0, Hrest⟩
  icases Hrest with ⟨%L, Hrest⟩
  icases Hrest with ⟨%dm1, Hrest⟩
  icases Hrest with ⟨%W, Hview, HW, %HWd, Hents, HK, Hpool, Hrec, Hled, Hrca⟩
  imod github_com.orcaman.concurrent_map.cmapPin_lookup g.γdc k v π.half Mc (⊤ \ ↑swift.descN)
    swift.descN_cmap_sub $$ [Hpin Hview] with ⟨%Hk, Hpin, Hview⟩
  · iframe
  icases (BigSepM.bigSepM_delete Hk).1 $$ Hents with ⟨He, Hents⟩
  iunfold swift.descEnt at He
  icases He with ⟨%d', %y', %Hv', Hs⟩
  have hd : d' = d := swift.mkOk_desc_inj d' d (Hv'.1.symm.trans Hv.1)
  subst hd
  cases hW : W !! k with
  | some o =>
    obtain ⟨t, ρ, v'⟩ := o
    unfold swift.entW
    icases Hs with ⟨-, Hs⟩
    iunfold swift.entL at Hs
    icases Hs with ⟨%s, %m, -, -, -, Hlk, -, -⟩
    iapply swift.fupd_false_elim
    iapply github_com.orcaman.concurrent_map.cmapLocked_pin_false (⊤ \ ↑swift.descN)
      swift.descN_cmap_sub g.γdc k (some v) t v π.half Mc $$ [Hlk Hpin Hview]
    iframe
  | none =>
  unfold swift.entW
  icases Hs with (Hs | ⟨%π', Hb2, Hp2, Hel⟩)
  · iexfalso
    ihave HS := hR $$ HR
    iapply swift.entS_excl γ DR Run (swift.sqE g) g.mp hRunSeq hSq d' y y' $$ [HS Hs]
    iframe
  ihave %Hπ := ghostVar_agree g.γb (some π) (1 : Qp).half (some π') (1 : Qp).half $$ Hb Hb2
  cases Hπ
  ihave Hu := Hupd $$ HR Hel
  imod Hu with ⟨HS, HX⟩
  ihave Hb : ghostVar g.γb 1 (some π) $$ [Hb Hb2]
  · iapply (ghostVar_split_half g.γb 1 (some π)).2; iframe
  imod ghostVar_update (none : Option github_com.orcaman.concurrent_map.PinD) g.γb (some π)
    $$ Hb with Hb
  imod Hclose $$ [Hst2 Hview HW Hents HK Hpool Hrec Hled Hrca HS] with -
  · inext
    iunfold swift.descInv
    iexists false
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe Hst2
    iexists Mc, q0, L, dm1, W
    iframe Hview HW HK Hpool Hrec Hled Hrca
    isplitr
    · ipureintro; exact HWd
    iapply (BigSepM.bigSepM_delete Hk).2
    iframe Hents
    iunfold swift.descEnt
    iexists d', y
    isplitr
    · ipureintro; exact ⟨Hv'.1, Hv.2⟩
    rw [hW]
    unfold swift.entW
    ileft; iexact HS
  imodintro
  iframe Hst Hb HX
  iapply (github_com.orcaman.concurrent_map.cmapPin_split g.γdc k v π).2
  iframe

/-- **An active goroutine's lent state at its stop channel's names** (round 37; table rev 8
G-lend): `entS`'s running disjunct with `active = true`, as `entS_view` hands it to the signal. -/
def swift.goAn (γn : GName) (g : swift.DescG) (str : swift.CommandId → GoString) (d : Loc)
    (y : swift.CommandId) (sc : Loc) (γc : ChanNames) (γsg : GName) : IProp netDistGF :=
  iprop(typedPointsto (swift.dfld d go!"seq") false (DFrac.own (1 : Qp).half) ∗
    ∃ (j : Nat) (qj : Qp) (m : Loc),
    ghostMapElem γn j (DFrac.own qj) false ∗
    (∃ γi : GName, swift.incW g γi γsg ∗ ghostVar γi (1 : Qp).half.half (str y, d) ∗
      ghostMapElem g.γj γi (DFrac.own (1 : Qp).half) (j, qj)) ∗
    typedPointsto (swift.dfld d go!"active") true (DFrac.own (1 : Qp).half) ∗
    typedPointsto (swift.dfld d go!"seq") false (DFrac.own (1 : Qp).half.half) ∗
    typedPointsto (swift.dfld d go!"msgs") m (DFrac.own (1 : Qp).half) ∗ swift.bagW m (g.mp y) ∗
    swift.stopBag γc sc (swift.stopMP g.γs γsg (str y) d sc) ∗
    (swift.sgTok γsg ∨ ghostMapElem g.γs (str y) (DFrac.own (1 : Qp).half) true) ∗
    typedPointsto (swift.dfld d go!"stopChan") sc (DFrac.own (1 : Qp).half))

/-- `goAn` at some names. -/
def swift.goA (γn : GName) (g : swift.DescG) (str : swift.CommandId → GoString) (d : Loc)
    (y : swift.CommandId) : IProp netDistGF :=
  iprop(∃ (sc : Loc) (γc : ChanNames) (γsg : GName), swift.goAn γn g str d y sc γc γsg)

theorem swift.goAn_entS (γ : sp.Names) (DR : Loc → IProp netDistGF) (γn : GName)
    (g : swift.DescG) (str : swift.CommandId → GoString) (d : Loc) (y : swift.CommandId)
    (sc : Loc) (γc : ChanNames) (γsg : GName) :
    swift.goAn γn g str d y sc γc γsg ⊢
      swift.entS γ DR (swift.descGo γn g str) (swift.sqE g) g.mp d y := by
  iintro H
  iunfold swift.goAn at H
  icases H with ⟨Hs, %j, %qj, %m, Hel, ⟨%γi, #Hw, Hv, Hr⟩, Ha, Hsq, Hms, #Hmb, #Hbag, Hsig, Hsc⟩
  icases (typedPointsto_half_split _ _ _).1 $$ Hms with ⟨Hmo, Hms⟩
  iunfold swift.entS
  iexists false, m
  iframe Hs Hmo
  iunfold swift.entI
  iright; ileft
  isplitr
  · ipureintro; rfl
  iunfold swift.descGo
  iexists j, qj, true, sc, γc, γsg, m, γi
  iframe Hel Hw Hv Hr Hsq Hms Hmb Hbag
  iunfold swift.goSt
  ileft
  simp only [↓reduceIte]
  iframe Ha Hsig Hsc

/-- The lent goroutine's `stopChan` share (to read the field before the send) and its stop bag. -/
theorem swift.goAn_sc (γn : GName) (g : swift.DescG) (str : swift.CommandId → GoString) (d : Loc)
    (y : swift.CommandId) (sc : Loc) (γc : ChanNames) (γsg : GName) :
    swift.goAn γn g str d y sc γc γsg ⊢
      typedPointsto (swift.dfld d go!"stopChan") sc (DFrac.own (1 : Qp).half) ∗
      swift.stopBag γc sc (swift.stopMP g.γs γsg (str y) d sc) ∗
      (typedPointsto (swift.dfld d go!"stopChan") sc (DFrac.own (1 : Qp).half) -∗
        swift.goAn γn g str d y sc γc γsg) := by
  iintro H
  iunfold swift.goAn at H
  icases H with ⟨Hs, %j, %qj, %m, Hel, Hrci, Ha, Hsq, Hms, #Hmb, #Hbag, Hsig, Hsc⟩
  iframe Hsc Hbag
  iintro Hsc
  iunfold swift.goAn
  iframe Hs
  iexists j, qj, m
  iframe Hel Hrci Ha Hsq Hms Hmb Hbag Hsig Hsc

/-- **The signal's ghost step** (round 37, G-lend/G-req): with the deposited element of `k` at
`false`, an unsignalled goroutine is signalled: the element is `true`, half to the request (with
the signal token), half to the entry; an already signalled one is refuted (its half at `true`). -/
theorem swift.goA_signal (γn : GName) (g : swift.DescG) (str : swift.CommandId → GoString) (d : Loc)
    (y : swift.CommandId) (sc : Loc) (γc : ChanNames) (γsg : GName) (S : GMap GoString Bool)
    (E : CoPset) :
    swift.goAn γn g str d y sc γc γsg ∗ ghostMapAuth g.γs 1 (S.insert (str y) false) ∗
      ghostMapElem g.γs (str y) (DFrac.own 1) false ⊢
    |={E}=> swift.goAn γn g str d y sc γc γsg ∗ ghostMapAuth g.γs 1 (S.insert (str y) true) ∗
      swift.sgTok γsg ∗ ghostMapElem g.γs (str y) (DFrac.own (1 : Qp).half) true := by
  iintro ⟨H, HS, Hel⟩
  iunfold swift.goAn at H
  icases H with ⟨Hs, %j, %qj, %m, Hgel, Hrci, Ha, Hsq, Hms, #Hmb, #Hbag, Hsig, Hsc⟩
  icases Hsig with (Hsg | Hh)
  rotate_left
  · icombine Hel Hh gives %Hc
    exfalso; have := DFrac.valid_own_op Hc.1; simp at this
  ihave Hu := ghost_map_update (γ := g.γs) true $$ HS Hel
  imod Hu with ⟨HS, Hel⟩
  rw [GMap.insert_insert]
  icases (ghostMapElem_halves g.γs (str y) true).1 $$ Hel with ⟨He1, He2⟩
  imodintro
  iframe HS Hsg He2
  iunfold swift.goAn
  iframe Hs
  iexists j, qj, m
  iframe Hgel Hrci Ha Hsq Hms Hmb Hbag Hsc
  iright; iexact He1

/-- **The round's reset** (see the file header). -/
theorem swift.round_reset (γs : GName) : ∀ S : GMap GoString Bool,
    ghostMapAuth γs 1 S ∗ ([∗map] k ↦ _v ∈ S, ghostMapElem γs k (DFrac.own 1) true) ⊢
      |==> ghostMapAuth γs 1 (∅ : GMap GoString Bool) := by
  apply GMap.map_ind
  · iintro ⟨Ha, -⟩; imodintro; iexact Ha
  · intro k v m hk ih
    iintro ⟨Ha, Hm⟩
    icases (BigSepM.bigSepM_insert hk).1 $$ Hm with ⟨Hx, Hm⟩
    imod ghost_map_delete (γ := γs) $$ Ha Hx with Ha
    rw [GMap.delete_insert m k v hk]
    iapply ih
    iframe

/-- **A lent state, read** (`stopDescs`' closure): a share of `active` (value `a`) and the
outer half of `seq` (value `s`); given back, the state again, or (`a ∧ ¬s`: a running goroutine)
its active form `goA` for the signal (round 37). Round 40 (table rev 10 T18v, P39-1; plan R10.2
(1)): with the run loop's authority over the round's elements at `k ↦ false` (T18l's), which
refutes a stopping goroutine's entry (its element's half at `true`). -/
theorem swift.entS_view (γ : sp.Names) (DR : Loc → IProp netDistGF) (γn : GName)
    (g : swift.DescG) (str : swift.CommandId → GoString) (hSq : swift.sqOk γ DR (swift.sqE g) g.mp) (d : Loc)
    (y : swift.CommandId) (S : GMap GoString Bool) (k : GoString) (hk : k = str y) :
    swift.entS γ DR (swift.descGo γn g str) (swift.sqE g) g.mp d y ∗
      ghostMapAuth g.γs 1 (S.insert k false) ⊢
      ghostMapAuth g.γs 1 (S.insert k false) ∗
      ∃ (a s : Bool) (qa : Qp), typedPointsto (swift.dfld d go!"active") a (DFrac.own qa) ∗
        typedPointsto (swift.dfld d go!"seq") s (DFrac.own (1 : Qp).half) ∗
        (typedPointsto (swift.dfld d go!"active") a (DFrac.own qa) -∗
          typedPointsto (swift.dfld d go!"seq") s (DFrac.own (1 : Qp).half) -∗
          if a && !s then swift.goA γn g str d y
          else swift.entS γ DR (swift.descGo γn g str) (swift.sqE g) g.mp d y) := by
  iintro ⟨H, HA⟩
  iunfold swift.entS at H
  icases H with ⟨%s, %mo, Hs, Hmo, Hh⟩
  iunfold swift.entI at Hh
  icases Hh with (⟨%Hsh, Hh⟩ | ⟨%Hs0, Hr⟩ | ⟨%Hs0, Hq⟩)
  rotate_left
  rotate_left
  · -- a sequential state: `active` is true, nothing to signal
    subst Hs0
    iframe HA
    ihave ⟨%qa, Ha, Hback⟩ := hSq.1 d y $$ Hq
    iexists true, true, qa
    iframe Ha Hs
    iintro Ha Hs
    simp only [Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
    iunfold swift.entS
    iexists true, mo
    iframe Hs Hmo
    iunfold swift.entI
    iright; iright
    isplitr
    · ipureintro; rfl
    iapply Hback $$ Ha
  · iframe HA
    iunfold swift.descHomeS at Hh
    icases Hh with ⟨%m, %sc, %sl, %fa, %a, Hm, #Hmb0, Hsc, Hsl, Hfa, Hfs, Hff, Ha, Hs1, %Has, HDR⟩
    iexists a, s, (1 : Qp)
    iframe Ha Hs
    iintro Ha Hs
    have hc : (a && !s) = false := by cases a <;> cases s <;> simp_all
    rw [hc]
    simp only [Bool.false_eq_true, ↓reduceIte]
    iunfold swift.entS
    iexists s, mo
    iframe Hs Hmo
    iunfold swift.entI
    ileft
    isplitr
    · ipureintro; exact Hsh
    iunfold swift.descHomeS
    iexists m, sc, sl, fa, a
    iframe
    iframe Hmb0
    ipureintro; exact Has
  · subst Hs0
    iunfold swift.descGo at Hr
    icases Hr with ⟨%j, %qj, %a, %sc, %γc, %γsg, %m, %γi, Hel, #Hw, Hv, Hrc, Hsq, Hms, #Hmb, #Hbag,
      Hst⟩
    iunfold swift.goSt at Hst
    icases Hst with (⟨Ha, Hst⟩ | ⟨Hel2, -, -⟩)
    rotate_left
    · -- stopping (P39-1): its element's half at `true` against the authority's `false`
      iexfalso
      ihave %Hl := ghost_map_lookup $$ HA Hel2
      subst hk
      have h2 : (S.insert (str y) false).lookup (str y) = some false := GMap.lookup_insert _ _ _
      rw [h2] at Hl
      cases Hl
    iframe HA
    iexists a, false, (1 : Qp).half
    iframe Ha Hs
    iintro Ha Hs
    cases a
    · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      iunfold swift.entS
      iexists false, mo
      iframe Hs Hmo
      iunfold swift.entI
      iright; ileft
      isplitr
      · ipureintro; rfl
      iunfold swift.descGo
      iexists j, qj, false, sc, γc, γsg, m, γi
      iframe Hel Hw Hv Hrc Hsq Hms Hmb Hbag
      iunfold swift.goSt
      ileft
      simp only [Bool.false_eq_true, ↓reduceIte]
      iframe Ha Hst
    · simp only [Bool.not_false, Bool.and_self, ↓reduceIte]
      icases Hst with ⟨Hsig, Hsc⟩
      ihave ⟨-, Hms⟩ := typedPointsto_half_combine _ mo m (1 : Qp).half $$ [Hmo Hms]
      · iframe
      iunfold swift.goA
      iexists sc, γc, γsg
      iunfold swift.goAn
      iframe Hs
      iexists j, qj, m
      iframe Hel Ha Hsq Hms Hmb Hbag Hsig Hsc
      iexists γi
      iframe Hw Hv Hrc

end lemmas

end Perennial.github_com.imdea_software.swiftpaxos
