/-
`(*Replica).executeCommands()` (epaxos.go): `wp_executeCommands : ExecuteCommandsSpecX (GF := GF)`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.ExecuteCommands
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.Strongconnect
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.RunSpec

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs
open model epaxosProof

attribute [local instance] GooseGlobalGS.gooseInvGS

variable [GooseExts]

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS]
variable [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions] [TH : TreemapHyp GF]

/-- What the executor holds under the instance lock during a scan and does not touch: the lock
itself and the pieces of `ownRep` other than the instances, `crtInstance`, `ExecedUpTo` and the
store, at `σ`, the state when the executor last took the lock (fix E1-opt1: it takes the lock
again after each root's search, so `σ` is per acquisition, not per pass). -/
def scanHeld (γ : EpNames) (i : Nat) (r lp : Loc) (σ : RState) : IProp GF :=
  iprop(sync.ownMutex lp ∗ ⌜cutBounds σ.committedUpTo⌝ ∗
    repRowArr r go!"CommittedUpTo" σ.committedUpTo ∗
    repConf r σ.conflicts ∗ repMsk r σ.maxSeqPerKey ∗
    repRowArr r go!"lastScan" σ.lastScan ∗ repRowArr r go!"lastPut" σ.lastPut ∗
    efld r go!"maxSeq" ↦ σ.maxSeq ∗ efld r go!"IsLeader" ↦ σ.isLeader ∗
    efld r go!"maxRecvBallot" ↦ σ.maxRecvBallot ∗ repPeer r i σ.peerOrder ∗
    ([∗list] to ∈ List.range nR, outboxFrag γ i to []))

/-- The executor's Tarjan stack (`execStackOwn` without the persistent `r.exec`). -/
abbrev scanStack (e : Loc) : IProp GF :=
  iprop(∃ (s : GoSlice) (xs : List Loc), structFieldRef epaxos.Exec go!"stack" e ↦ s ∗
    s ↦* xs ∗ ownSliceCap Loc s (DFrac.own 1) ∗ ⌜0 < sint.Z s.cap⌝)

/-- Taking the instance lock (at the start of a pass, and again after each root's search): the
lock's invariant at some state `σ`, opened into the scan's pieces, with the scan's facts at `σ`
(`ep_scanOk`, one credit). Nothing about `σ` is known beyond the invariant: whatever the run loop
did while the lock was free is in it. -/
theorem scan_unpack (γ : EpNames) (i : Nat) (r e lp : Loc) (hi : i < nR) :
    ⊢ inv protoN (epInv (GF := GF) γ) -∗ efld r go!"exec" ↦□ e -∗ sync.ownMutex lp -∗ instLockInv γ i r -∗
      £ 1 ={⊤}=∗
      ∃ σ : RState, scanHeld γ i r lp σ ∗ repRowArr r go!"crtInstance" σ.crtInstance ∗
        repInsts γ i r σ.inst ∗ repRowArr r go!"ExecedUpTo" σ.execedUpTo ∗ repStore r σ.store ∗
        repFrag γ i σ ∗ pendFrag γ i none ∗ curFrag γ i [] 0 ∗ scanStack e ∗
        ⌜ScanOk σ ∧ instBounds σ.inst⌝ := by
  iintro #Hinv #He Hlocked HL Hlc
  unfold instLockInv
  icases HL with ⟨⟨%σ0, Hrep, Hfrag, Hidle⟩, Hstack⟩
  imod (ep_scanOk γ ⊤ i σ0 (by simp) hi) $$ Hinv Hfrag Hlc with ⟨Hfrag, %Hok0⟩
  rw [ownRep_unseal]; unfold ownRepDef
  icases Hrep with ⟨%Hib0, %Hcb0, Hins, Hcrt, Hcut, Heut, Hconf, Hmsk, Hlsc, Hlpt, Hms, Hil, Hmrb, Hstore, Hpeer⟩
  unfold repIdle
  icases Hidle with ⟨Hout, Hpend, Hcur⟩
  unfold execStackOwn
  icases Hstack with ⟨%e', %s0, %xs0, #He', Hst, Hs, Hcap, %Hcap0⟩
  icombine He He' gives %He'e
  subst He'e
  ihave Hstk : scanStack e $$ [Hst Hs Hcap]
  · unfold scanStack; iexists s0, xs0; iframe; ipureintro; exact Hcap0
  imodintro
  iexists σ0
  isplitl [Hlocked Hcut Hconf Hmsk Hlsc Hlpt Hms Hil Hmrb Hpeer Hout]
  · unfold scanHeld; iframe; ipureintro; exact Hcb0
  iframe
  ipureintro; exact ⟨Hok0, Hib0⟩

/-- Releasing the instance lock (after each root's search, and at the end of a pass): the scan's
pieces at `σ`, a state of the scan since the lock was taken at `σ0` (`ScanRel`), give the lock's
invariant at `σ`. Every unexecuted instance's search index is 0 here: that is `repInsts`'s
`ownInst`, which `executeCommand`'s postcondition gives back (`findSCC` resets the ones left on the
stack), so no search state spans the release. -/
theorem scan_pack (γ : EpNames) (i : Nat) (r e lp : Loc) (σ0 σ : RState) (hrel : ScanRel σ0 σ)
    (hib : instBounds σ.inst) :
    ⊢ efld r go!"exec" ↦□ e -∗ scanHeld (GF := GF) γ i r lp σ0 -∗
      repRowArr r go!"crtInstance" σ0.crtInstance -∗
      repInsts γ i r σ.inst -∗ repRowArr r go!"ExecedUpTo" σ.execedUpTo -∗ repStore r σ.store -∗
      repFrag γ i σ -∗ pendFrag γ i none -∗ curFrag γ i [] 0 -∗ scanStack e -∗
      sync.ownMutex lp ∗ instLockInv γ i r := by
  obtain ⟨I, st, eu, rfl⟩ := hrel
  iintro #He Hrest Hcrt Hins Heut Hstore Hfrag Hpend Hcur Hstk
  unfold scanHeld
  icases Hrest with ⟨Hlocked, %Hcb, Hcut, Hconf, Hmsk, Hlsc, Hlpt, Hms, Hil, Hmrb, Hpeer, Hout⟩
  iframe Hlocked
  unfold instLockInv
  isplitr [Hstk]
  · iexists { σ0 with inst := I, store := st, execedUpTo := eu }
    rw [ownRep_unseal]; unfold ownRepDef repIdle
    iframe Hfrag Hout Hpend Hcur
    iframe
    ipureintro; exact ⟨hib, Hcb⟩
  · unfold execStackOwn scanStack
    icases Hstk with ⟨%s, %xs, Hst, Hs, Hcap, %Hcap1⟩
    iexists e, s, xs
    iframe
    isplitr
    · iexact He
    ipureintro; exact Hcap1

set_option maxHeartbeats 4000000 in
theorem wp_executeCommands (hEx : state.Command.Execute.spec (GF := GF))
    (hRP : replica.Replica.ReplyProposeTS.spec (GF := GF)) : ExecuteCommandsSpecX (GF := GF) := by
  intro γ i r rr L p Rext e ch γc
  wp_start as ⟨#Hisr, #Hrr, #Hfw, #He, #Her, #Hch, #Hbag⟩
  ihave #Hro := isReplicaFw_ro _ _ _ _ _ _ $$ Hfw
  ihave ⟨#HN, -, -, -, -, -, -, -, -, #HSh, -, -, -, %HLn⟩ := fwRO_fields _ _ _ _ _ $$ Hro
  ihave #HM := isReplicaFw_lock _ _ _ _ _ _ $$ Hfw
  have hL : L.length = 5 := HLn.1
  rw [hL]
  wp_auto
  wp_apply (wp_slice_make2 (V := w32) (W64 5)) as %pis ⟨Hpis, -⟩
  · ipureintro; decide
  wp_apply (wp_slice_make2 (V := w64) (W64 5)) as %tos ⟨Htos, -⟩
  · ipureintro; decide
  -- `problemInstance[q] = -1; timeout[q] = 0`
  ihave HI : (∃ k : Nat, "q" ∷ q_ptr ↦ W64 (k : Int) ∗ "%Hk" ∷ ⌜k ≤ 5⌝ ∗
      "Hpis" ∷ (∃ l : List w32, pis ↦* l ∗ ⌜l.length = 5⌝) ∗
      "Htos" ∷ (∃ l : List w64, tos ↦* l ∗ ⌜l.length = 5⌝) : IProp GF) $$ [q Hpis Htos]
  · iexists 0; iframe q
    isplitr; · ipureintro; omega
    isplitl [Hpis]
    · iexists _; iframe Hpis; ipureintro; rfl
    · iexists _; iframe Htos; ipureintro; rfl
  wp_for HI
  wp_if_destruct
  · have hk5 : k < 5 := by word
    icases Hpis with ⟨%l1, Hpis, %Hl1⟩
    icases Htos with ⟨%l2, Htos, %Hl2⟩
    ihave %Hs1 := ownSlice_len _ _ _ $$ Hpis
    ihave %Hs2 := ownSlice_len _ _ _ $$ Htos
    have hb1 : 0 ≤ sint.Z (W64 (k : Int)) ∧ sint.Z (W64 (k : Int)) < sint.Z pis.len := by
      have := Hs1.1; have := Hs1.2; rw [Hl1] at *; constructor <;> word
    have hb2 : 0 ≤ sint.Z (W64 (k : Int)) ∧ sint.Z (W64 (k : Int)) < sint.Z tos.len := by
      have := Hs2.1; have := Hs2.2; rw [Hl2] at *; constructor <;> word
    simp only [hb1, _root_.and_self, ↓reduceIte]
    wp_apply wp_store_slice_index $$ [$Hpis] as Hpis
    · ipureintro; rw [Hl1]; constructor <;> word
    simp only [hb2, _root_.and_self, ↓reduceIte]
    wp_apply wp_store_slice_index $$ [$Htos] as Htos
    · ipureintro; rw [Hl2]; constructor <;> word
    wp_for_post
    iframe
    iexists k + 1
    rw [show W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) by push_cast; word]
    iframe q
    isplitr; · ipureintro; omega
    isplitl [Hpis]
    · iexists _; iframe Hpis; ipureintro; simp [Hl1]
    · iexists _; iframe Htos; ipureintro; simp [Hl2]
  -- the passes
  rw [isReplica_unseal]; unfold isReplicaDef
  icases Hisr with ⟨%rr', %L', %p', -, -, -, #Hro', ⟨%lp, #Hlp, #Hlock⟩, #Hinv, -⟩
  ihave HO : ("Hpis" ∷ (∃ l : List w32, pis ↦* l ∗ ⌜l.length = 5⌝) ∗
      "Htos" ∷ (∃ l : List w64, tos ↦* l ∗ ⌜l.length = 5⌝) : IProp GF) $$ [Hpis Htos]
  · iframe
  clear Hk Hif k
  wp_for HO
  wp_apply (lc := 1) sync.Mutex.wp_Lock $$ [$Hlock] as ⟨Hlocked, HL⟩
  have hi : i < nR := by have := HLn.2; rw [hL] at this; exact this
  iapply fupd_wp
  imod (scan_unpack γ i r e lp hi) $$ Hinv He Hlocked HL Hlc1
    with ⟨%σS, Hrest, Hcrt, Hins, Heut, Hstore, Hfrag, Hpend, Hcur, Hstk, %HokS⟩
  imodintro
  ihave #Hctx : exCtx γ i r e rr L p Rext $$ []
  · unfold exCtx epROFields
    icases Hro' with ⟨-, -, -, -, -, -, -, -, -, #Htc⟩
    iframe #
    iPkgInit
    all_goals solve_pkg_init
  -- the scan: rows `q = 0 .. N-1`
  ihave HQ : (∃ (k : Nat) (σ0 σ : RState), "q" ∷ q_ptr ↦ W32 (k : Int) ∗ "%Hk" ∷ ⌜k ≤ 5⌝ ∗
      "Hins" ∷ repInsts γ i r σ.inst ∗ "Heut" ∷ repRowArr r go!"ExecedUpTo" σ.execedUpTo ∗
      "Hcrt" ∷ repRowArr r go!"crtInstance" σ0.crtInstance ∗ "Hrest" ∷ scanHeld γ i r lp σ0 ∗
      "Hstore" ∷ repStore r σ.store ∗
      "Hstk" ∷ (∃ (s : GoSlice) (xs : List Loc), structFieldRef epaxos.Exec go!"stack" e ↦ s ∗
        s ↦* xs ∗ ownSliceCap Loc s (DFrac.own 1) ∗ ⌜0 < sint.Z s.cap⌝) ∗
      "Hfrag" ∷ repFrag γ i σ ∗ "Hpend" ∷ pendFrag γ i none ∗ "Hcur" ∷ curFrag γ i [] 0 ∗
      "%Hσ" ∷ ⌜ScanRel σ0 σ ∧ ScanOk σ ∧ instBounds σ.inst⌝ ∗
      "Hpis" ∷ (∃ l : List w32, pis ↦* l ∗ ⌜l.length = 5⌝) ∗
      "Htos" ∷ (∃ l : List w64, tos ↦* l ∗ ⌜l.length = 5⌝) ∗
      "executed" ∷ (∃ b : Bool, executed_ptr ↦ b) ∗
      "Htr" ∷ (∃ (sl : GoSlice) (ptrs : List Loc), toRecover_ptr ↦ sl ∗ sl ↦* ptrs ∗
        ownSliceCap Loc sl (DFrac.own 1) ∗ [∗list] x ∈ ptrs, exRecoverReq γ i x) : IProp GF)
      $$ [q Hins Heut Hcrt Hrest Hstore Hstk Hfrag Hpend Hcur Hpis Htos executed toRecover]
  · iexists 0, σS, σS
    iframe q Hins Heut Hcrt Hrest Hstore Hstk Hfrag Hpend Hcur Hpis Htos
    isplitr; · ipureintro; omega
    isplitr; · ipureintro; exact ⟨ScanRel.refl σS, HokS.1, HokS.2⟩
    isplitl [executed]; · iexists false; iexact executed
    iexists slice.nil, []
    iframe toRecover
    isplitl; · iapply ownSlice_nil
    isplitl; · iapply ownSliceCap_nil
    iapply BigSepL.bigSepL_nil.2; iempintro
  wp_for HQ
  wp_if_destruct
  · -- row `k`
    have hk5 : k < 5 := by
      have : sint.Z (W32 (sint.Z (W64 (5 : Nat)))) = 5 := by decide
      rw [this] at Hif; word
    obtain ⟨Hrel, Hok, Hib⟩ := Hσ
    have hkn : k < nR := hk5
    have hzk : sint.Z (W32 (k : Int)) = k := by word
    have hidx : sint.Z (W64 (sint.Z (W32 (k : Int)))) = k := by rw [hzk]; word
    unfold repRowArr
    icases Heut with ⟨%eut, #Heutf, Heut⟩
    icases Hcrt with ⟨%crt, #Hcrtf, Hcrt⟩
    ihave %Heutl := ownSlice_len _ _ _ $$ Heut
    ihave %Hcrtl := ownSlice_len _ _ _ $$ Hcrt
    simp only [List.length_map, List.length_range] at Heutl Hcrtl
    have heutl : sint.Z eut.len = 5 := by
      have h1 := Heutl.1; have h2 := Heutl.2; simp only [sint.nat, sint.Z, nR] at h1 h2 ⊢; omega
    have hcrtl : sint.Z crt.len = 5 := by
      have h1 := Hcrtl.1; have h2 := Hcrtl.2; simp only [sint.nat, sint.Z, nR] at h1 h2 ⊢; omega
    have hbe : 0 ≤ sint.Z (W64 (sint.Z (W32 (k : Int)))) ∧
        sint.Z (W64 (sint.Z (W32 (k : Int)))) < sint.Z eut.len := by
      rw [hidx, heutl]; omega
    have hbc : 0 ≤ sint.Z (W64 (sint.Z (W32 (k : Int)))) ∧
        sint.Z (W64 (sint.Z (W32 (k : Int)))) < sint.Z crt.len := by
      rw [hidx, hcrtl]; omega
    have hgk : ∀ f : Nat → w32, ((List.range nR).map f)[(sint.Z (W64 (sint.Z (W32 (k : Int))))).toNat]? = some (f k) := by
      intro f; rw [hidx]; simp [hkn]
    wp_auto
    simp only [hbe, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index eut _ _ _ (σ.execedUpTo k) hbe.1 $$ [$Heut] as Heut
    · ipureintro; exact hgk _
    have hcrtk : -1 ≤ zz (σ0.crtInstance k) ∧ toN (σ0.crtInstance k) + 1 < MAX_INSTANCE := by
      have h := Hok.2 k hkn; rwa [Hrel.crt] at h
    -- the row's instances `ExecedUpTo[q]+1 ..= crtInstance[q]`
    ihave HJ : (∃ (c : w32) (σ0 σ' : RState), "inst" ∷ inst_ptr ↦ c ∗ "%Hc" ∷ ⌜0 ≤ zz c⌝ ∗
        "Hins" ∷ repInsts γ i r σ'.inst ∗ "Heut" ∷ eut ↦* (List.range nR).map σ'.execedUpTo ∗
        "Hcrt" ∷ crt ↦* (List.range nR).map σ0.crtInstance ∗ "Hrest" ∷ scanHeld γ i r lp σ0 ∗
        "Hstore" ∷ repStore r σ'.store ∗
        "Hstk" ∷ (∃ (s : GoSlice) (xs : List Loc), structFieldRef epaxos.Exec go!"stack" e ↦ s ∗
          s ↦* xs ∗ ownSliceCap Loc s (DFrac.own 1) ∗ ⌜0 < sint.Z s.cap⌝) ∗
        "Hfrag" ∷ repFrag γ i σ' ∗ "Hpend" ∷ pendFrag γ i none ∗ "Hcur" ∷ curFrag γ i [] 0 ∗
        "%Hσ" ∷ ⌜ScanRel σ0 σ' ∧ ScanOk σ' ∧ instBounds σ'.inst⌝ ∗
        "Hpis" ∷ (∃ l : List w32, pis ↦* l ∗ ⌜l.length = 5⌝) ∗
        "Htos" ∷ (∃ l : List w64, tos ↦* l ∗ ⌜l.length = 5⌝) ∗
        "executed" ∷ (∃ b : Bool, executed_ptr ↦ b) ∗
        "Htr" ∷ (∃ (sl : GoSlice) (ptrs : List Loc), toRecover_ptr ↦ sl ∗ sl ↦* ptrs ∗
          ownSliceCap Loc sl (DFrac.own 1) ∗ [∗list] x ∈ ptrs, exRecoverReq γ i x) : IProp GF)
        $$ [inst Hins Heut Hcrt Hrest Hstore Hstk Hfrag Hpend Hcur Hpis Htos executed Htr]
    · iexists σ.execedUpTo k + W32 1, σ0, σ
      iframe
      ipureintro
      refine ⟨?_, Hrel, Hok, Hib⟩
      have := (Hok.1.exLo k hkn); unfold MAX_INSTANCE at this
      simp only [zz] at *; word
    clear Hrel Hok Hib hcrtk
    wp_for HJ
    obtain ⟨Hrel, Hok, Hib⟩ := Hσ
    have hcrtk : -1 ≤ zz (σ0.crtInstance k) ∧ toN (σ0.crtInstance k) + 1 < MAX_INSTANCE := by
      have h := Hok.2 k hkn; rwa [Hrel.crt] at h
    simp only [hbc, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index crt _ _ _ (σ0.crtInstance k) hbc.1 $$ [$Hcrt] as Hcrt
    · ipureintro; exact hgk _
    wp_if_destruct
    · -- an instance of the row
      have hcle : zz c ≤ zz (σ0.crtInstance k) := by
        simp only [zz]; exact of_decide_eq_true (go.intoVal_inj Hif)
      have hcz : (toN c : Int) = zz c := by simp only [toN, zz] at *; omega
      have hcn : toN c + 1 < MAX_INSTANCE := by
        have := hcrtk.2; simp only [toN, zz] at *; omega
      icases repInsts_acc γ i r σ'.inst ⟨k, toN c⟩ hkn (by show toN c < MAX_INSTANCE; omega) $$ Hins
        with ⟨%iss, %rows, %row, %ptrs, %ptr, #Hiss, #Hrows, %Hrow, Hptrs, %Hptr, Hx, Hclose⟩
      ihave %Hrlen := ownSlice_len _ _ _ $$ Hrows
      ihave %Hplen := ownSlice_len _ _ _ $$ Hptrs
      have hrk : k < rows.length := (List.getElem?_eq_some_iff.mp Hrow).1
      have h1 : 0 ≤ sint.Z (W64 (sint.Z (W32 (k : Int)))) ∧
          sint.Z (W64 (sint.Z (W32 (k : Int)))) < sint.Z iss.len := by
        rw [hidx]; have := Hrlen.1; have := Hrlen.2; simp only [sint.nat, sint.Z] at *; omega
      have hcidx : sint.Z (W64 (sint.Z c)) = zz c := by
        have := hcrtk.2; unfold MAX_INSTANCE at *; simp only [toN, zz] at *; word
      have h2 : 0 ≤ sint.Z (W64 (sint.Z c)) ∧ sint.Z (W64 (sint.Z c)) < sint.Z row.len := by
        rw [hcidx]; have := Hplen.1; have := Hplen.2; have := Hptr.2
        simp only [sint.nat, toN, zz, sint.Z] at *; omega
      have hrowk : rows[(sint.Z (W64 (sint.Z (W32 (k : Int))))).toNat]? = some row := by
        rw [hidx]; exact Hrow
      have hptrc : ptrs[(sint.Z (W64 (sint.Z c))).toNat]? = some ptr := by
        rw [hcidx]; exact Hptr.1
      have hpset : ptrs.set (toN c) ptr = ptrs := by
        have := List.getElem?_eq_some_iff.mp Hptr.1
        rw [← this.2]; exact List.set_getElem_self this.1
      wp_auto
      simp only [h1, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index iss _ rows _ row h1.1 $$ [$Hrows] as -
      · ipureintro; exact hrowk
      simp only [h2, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index row _ ptrs _ ptr h2.1 $$ [$Hptrs] as Hptrs
      · ipureintro; exact hptrc
      rcases hx : σ'.inst ⟨k, toN c⟩ with _ | w
      · -- no instance
        unfold instAt; icases Hx with %Hnull
        have hdn : decide (ptr = null) = true := decide_eq_true Hnull
        simp only [hdn]
        wp_auto
        simp only [h1, _root_.and_self, ↓reduceIte]
        wp_apply wp_load_slice_index iss _ rows _ row h1.1 $$ [$Hrows] as -
        · ipureintro; exact hrowk
        simp only [h2, _root_.and_self, ↓reduceIte]
        wp_apply wp_load_slice_index row _ ptrs _ ptr h2.1 $$ [$Hptrs] as Hptrs
        · ipureintro; exact hptrc
        simp only [hdn]
        wp_auto
        ihave Hins := Hclose $$ %ptr %none [Hptrs] []
        · rw [hpset]; iexact Hptrs
        · ipureintro; exact Hnull
        rw [upd_self _ _ _ hx]
        -- PROBLEM
        icases Hpis with ⟨%l1, Hpis, %Hl1⟩
        icases Htos with ⟨%l2, Htos, %Hl2⟩
        ihave %Hs1 := ownSlice_len _ _ _ $$ Hpis
        ihave %Hs2 := ownSlice_len _ _ _ $$ Htos
        have hb1 : 0 ≤ sint.Z (W64 (sint.Z (W32 (k : Int)))) ∧
            sint.Z (W64 (sint.Z (W32 (k : Int)))) < sint.Z pis.len := by
          rw [hidx]; have := Hs1.1; have := Hs1.2; simp only [sint.nat, sint.Z] at *; omega
        have hb2 : 0 ≤ sint.Z (W64 (sint.Z (W32 (k : Int)))) ∧
            sint.Z (W64 (sint.Z (W32 (k : Int)))) < sint.Z tos.len := by
          rw [hidx]; have := Hs2.1; have := Hs2.2; simp only [sint.nat, sint.Z] at *; omega
        have hkt : (sint.Z (W64 (sint.Z (W32 (k : Int))))).toNat = k := by rw [hidx]; simp
        obtain ⟨pv, hpv⟩ : ∃ pv, l1[k]? = some pv := ⟨_, List.getElem?_eq_getElem (by omega)⟩
        obtain ⟨tv, htv⟩ : ∃ tv, l2[k]? = some tv := ⟨_, List.getElem?_eq_getElem (by omega)⟩
        simp only [hb1, _root_.and_self, ↓reduceIte]
        wp_apply wp_load_slice_index pis _ l1 _ pv hb1.1 $$ [$Hpis] as Hpis
        · ipureintro; rw [hkt]; exact hpv
        wp_if_destruct
        · -- the same problem instance: its timeout grows
          have hcpv : c = pv := Hif
          simp only [hb2, _root_.and_self, ↓reduceIte]
          wp_auto
          simp only [hb2, _root_.and_self, ↓reduceIte]
          wp_apply wp_load_slice_index tos _ l2 _ tv hb2.1 $$ [$Htos] as Htos
          · ipureintro; rw [hkt]; exact htv
          wp_apply wp_store_slice_index $$ [$Htos] as Htos
          · ipureintro; rw [Hl2, hidx]; omega
          have hl2' : (l2.set k (tv + W64 1000000)).length = 5 := by simp [Hl2]
          simp only [hb2, _root_.and_self, ↓reduceIte]
          rw [hkt]
          wp_apply wp_load_slice_index tos _ _ _ (tv + W64 1000000) hb2.1 $$ [$Htos] as Htos
          · ipureintro; rw [hkt]; exact List.getElem?_set_self (by omega)
          wp_if_destruct
          · -- the grace period is over: ask for the recovery of `inst ..= crtInstance[q]`
            ihave ⟨Hfrag, #Hlb⟩ := crtLb_get γ i k σ' $$ Hfrag
            have hcq : σ'.crtInstance k = σ0.crtInstance k := by rw [Hrel.crt]
            simp only [hb1, _root_.and_self, ↓reduceIte]
            wp_apply wp_load_slice_index pis _ l1 _ pv hb1.1 $$ [$Hpis] as Hpis
            · ipureintro; rw [hkt]; exact hpv
            ihave HK : (∃ kv : w32, "kk" ∷ k_ptr ↦ kv ∗ "%Hkv" ∷ ⌜0 ≤ zz kv⌝ ∗
                "Htr" ∷ (∃ (sl : GoSlice) (ptrs : List Loc), toRecover_ptr ↦ sl ∗ sl ↦* ptrs ∗
                  ownSliceCap Loc sl (DFrac.own 1) ∗ [∗list] x ∈ ptrs, exRecoverReq γ i x) :
                IProp GF) $$ [k Htr]
            · iexists pv; iframe; ipureintro; rw [← hcpv]; exact Hc
            wp_for HK
            simp only [hbc, _root_.and_self, ↓reduceIte]
            wp_apply wp_load_slice_index crt _ _ _ (σ0.crtInstance k) hbc.1 $$ [$Hcrt] as Hcrt
            · ipureintro; exact hgk _
            wp_if_destruct
            · -- append `&instanceId{q, k}`
              icases Htr with ⟨%sl, %ptrsr, Htrp, Hsl, Hslcap, Hreqs⟩
              wp_auto
              wp_bind (App (Val (GoInstruction (CompositeLiteral
                (go.SliceType (go.PointerType epaxos.instanceId.ty))))) (Val (LiteralValueV _)))
              iapply wp_slice_literal (V := Loc) (t := go.PointerType epaxos.instanceId.ty) [«$sl0_ptr»]
              wp_auto
              isplitl []
              · ipureintro; rfl
              iintro %lit_ptr ⟨Hlit, -⟩
              wp_apply wp_slice_append (V := Loc) sl ptrsr _ [«$sl0_ptr»] (DFrac.own 1)
                $$ [$Hsl $Hslcap $Hlit] as %sl2 ⟨Hsl2, Hsl2cap, -⟩
              have hkle : zz kv ≤ zz (σ0.crtInstance k) := by
                simp only [zz]; exact of_decide_eq_true (go.intoVal_inj Hif)
              wp_for_post
              iframe
              iexists kv + W32 1
              iframe
              isplitr
              · ipureintro
                have := hcrtk.2; unfold MAX_INSTANCE at this; simp only [toN, zz] at *; word
              iexists sl2, ptrsr ++ [«$sl0_ptr»]
              iframe
              iapply BigSepL.bigSepL_singleton.2
              unfold exRecoverReq
              iexists k, toN kv, σ0.crtInstance k
              rw [show W32 ((toN kv : Nat) : Int) = kv by simp only [toN, zz] at *; word]
              iframe
              isplitl
              · rw [← hcq]; iexact Hlb
              ipureintro; refine ⟨hkn, ?_⟩; simp only [toN, zz] at *; omega
            · have hnot : decide (sint.Z kv ≤ sint.Z (σ0.crtInstance k)) = false := by
                cases h : decide (sint.Z kv ≤ sint.Z (σ0.crtInstance k))
                · rfl
                · rw [h] at Hif; exact absurd rfl Hif
              simp only [hnot, Bool.false_eq_true, ↓reduceIte]
              wp_auto
              simp only [hb2, _root_.and_self, ↓reduceIte]
              wp_apply wp_store_slice_index $$ [$Htos] as Htos
              · ipureintro; rw [hl2', hidx]; omega
              wp_for_post
              wp_for_post
              iframe
              iexists k + 1, σ0, σ'
              rw [show W32 (k : Int) + W32 1 = W32 ((k + 1 : Nat) : Int) by push_cast; word]
              iframe
              isplitr; · ipureintro; omega
              isplitl [Heut]
              · iexists eut; iframe Heutf Heut
              isplitl [Hcrt]
              · iexists crt; iframe Hcrtf Hcrt
              isplitr; · ipureintro; exact ⟨Hrel, Hok, Hib⟩
              isplitl [Hpis]
              · iexists _; iframe Hpis; ipureintro; simp [Hl1]
              iexists _; iframe Htos; ipureintro; simp [Hl2]
          · wp_for_post
            wp_for_post
            iframe
            iexists k + 1, σ0, σ'
            rw [show W32 (k : Int) + W32 1 = W32 ((k + 1 : Nat) : Int) by push_cast; word]
            iframe
            isplitr; · ipureintro; omega
            isplitl [Heut]
            · iexists eut; iframe Heutf Heut
            isplitl [Hcrt]
            · iexists crt; iframe Hcrtf Hcrt
            isplitr; · ipureintro; exact ⟨Hrel, Hok, Hib⟩
            isplitl [Hpis]
            · iexists _; iframe Hpis; ipureintro; simp [Hl1]
            iexists _; iframe Htos; ipureintro; exact hl2'
        · -- a new problem instance
          simp only [hb1, _root_.and_self, ↓reduceIte]
          wp_apply wp_store_slice_index $$ [$Hpis] as Hpis
          · ipureintro; rw [Hl1]; rw [hidx]; omega
          simp only [hb2, _root_.and_self, ↓reduceIte]
          wp_apply wp_store_slice_index $$ [$Htos] as Htos
          · ipureintro; rw [Hl2]; rw [hidx]; omega
          wp_for_post
          wp_for_post
          iframe
          iexists k + 1, σ0, σ'
          rw [show W32 (k : Int) + W32 1 = W32 ((k + 1 : Nat) : Int) by push_cast; word]
          iframe
          isplitr; · ipureintro; omega
          isplitl [Heut]
          · iexists eut; iframe Heutf Heut
          isplitl [Hcrt]
          · iexists crt; iframe Hcrtf Hcrt
          isplitr; · ipureintro; exact ⟨Hrel, Hok, Hib⟩
          isplitl [Hpis]
          · iexists _; iframe Hpis; ipureintro; simp [Hl1]
          iexists _; iframe Htos; ipureintro; simp [Hl2]
      · -- an instance: its status
        unfold instAt ownInst
        icases Hx with ⟨%y, Hy, %Hyf, #Hyid, Hycmds, Hydeps, Hylb⟩
        ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hy
        have hdn : decide (ptr = null) = false := decide_eq_false Hnn
        simp only [hdn, Bool.not_false]
        wp_auto
        simp only [h1, _root_.and_self, ↓reduceIte]
        wp_apply wp_load_slice_index iss _ rows _ row h1.1 $$ [$Hrows] as -
        · ipureintro; exact hrowk
        simp only [h2, _root_.and_self, ↓reduceIte]
        wp_apply wp_load_slice_index row _ ptrs _ ptr h2.1 $$ [$Hptrs] as Hptrs
        · ipureintro; exact hptrc
        wp_if_destruct
        · -- EXECUTED: skipped (`ExecedUpTo[q]` moves past it if it is the next one)
          have hwex : w.status = stEXECUTED := by rw [← Hyf.2.2.1]; exact Hif
          ihave Hins := Hclose $$ %ptr %(some w) [Hptrs] [Hy Hycmds Hydeps Hylb]
          · rw [hpset]; iexact Hptrs
          · dsimp only; iexists y; iframe Hy Hycmds Hydeps Hylb
            isplitr
            · ipureintro; exact Hyf
            iexact Hyid
          rw [upd_self _ _ _ hx]
          have hc1 : 0 ≤ zz (c + W32 1) := by
            have := hcrtk.2; unfold MAX_INSTANCE at this; simp only [toN, zz] at *; word
          simp only [hbe, _root_.and_self, ↓reduceIte]
          wp_apply (lc := 1) wp_load_slice_index eut _ _ _ (σ'.execedUpTo k) hbe.1 $$ [$Heut] as Heut
          · ipureintro; exact hgk _
          wp_if_destruct
          · -- the next one: `ExecedUpTo[q] = inst` (the model's `execBump`)
            have hex : σ'.executed ⟨k, toN (σ'.execedUpTo k + 1)⟩ := ⟨w, hx, hwex⟩
            iapply fupd_wp
            imod (ep_execBump γ ⊤ i σ' k (by simp) hi hkn hex) $$ Hinv Hfrag Hlc1 with Hfrag
            imodintro
            simp only [hbe, _root_.and_self, ↓reduceIte]
            wp_apply wp_store_slice_index $$ [$Heut] as Heut
            · ipureintro; simp only [List.length_map, List.length_range]; rw [hidx]; unfold nR; omega
            wp_for_post
            iframe
            iexists σ'.execedUpTo k + W32 1 + W32 1, σ0, execBump σ' k
            iframe
            isplitr; · ipureintro; exact hc1
            isplitl [Heut]
            · rw [hidx]
              have e1 : (List.map σ'.execedUpTo (List.range nR)).set (Int.toNat (k : Int))
                    (σ'.execedUpTo k + W32 1) =
                  List.map (execBump σ' k).execedUpTo (List.range nR) := by
                simp only [Int.toNat_natCast, execBump]
                rw [map_range_upd _ _ _ _ hkn]; rfl
              rw [e1]; iexact Heut
            ipureintro
            exact ⟨Hrel.bump k, Hok.bump hkn hex, Hib⟩
          · wp_for_post
            iframe
            iexists c + W32 1, σ0, σ'
            iframe
            ipureintro
            exact ⟨hc1, Hrel, Hok, Hib⟩
        · -- not EXECUTED: committed with commands?
          have hwnex : w.status ≠ stEXECUTED := by rw [← Hyf.2.2.1]; exact Hif
          simp only [h1, _root_.and_self, ↓reduceIte]
          wp_apply wp_load_slice_index iss _ rows _ row h1.1 $$ [$Hrows] as -
          · ipureintro; exact hrowk
          simp only [h2, _root_.and_self, ↓reduceIte]
          wp_apply wp_load_slice_index row _ ptrs _ ptr h2.1 $$ [$Hptrs] as Hptrs
          · ipureintro; exact hptrc
          simp only [hdn, Bool.not_false]
          wp_auto
          simp only [h1, _root_.and_self, ↓reduceIte]
          wp_apply wp_load_slice_index iss _ rows _ row h1.1 $$ [$Hrows] as -
          · ipureintro; exact hrowk
          simp only [h2, _root_.and_self, ↓reduceIte]
          wp_apply wp_load_slice_index row _ ptrs _ ptr h2.1 $$ [$Hptrs] as Hptrs
          · ipureintro; exact hptrc
          wp_if_destruct
          · -- not committed yet: a problem instance
            ihave Hins := Hclose $$ %ptr %(some w) [Hptrs] [Hy Hycmds Hydeps Hylb]
            · rw [hpset]; iexact Hptrs
            · dsimp only; iexists y; iframe Hy Hycmds Hydeps Hylb
              isplitr
              · ipureintro; exact Hyf
              iexact Hyid
            rw [upd_self _ _ _ hx]
            -- PROBLEM
            icases Hpis with ⟨%l1, Hpis, %Hl1⟩
            icases Htos with ⟨%l2, Htos, %Hl2⟩
            ihave %Hs1 := ownSlice_len _ _ _ $$ Hpis
            ihave %Hs2 := ownSlice_len _ _ _ $$ Htos
            have hb1 : 0 ≤ sint.Z (W64 (sint.Z (W32 (k : Int)))) ∧
                sint.Z (W64 (sint.Z (W32 (k : Int)))) < sint.Z pis.len := by
              rw [hidx]; have := Hs1.1; have := Hs1.2; simp only [sint.nat, sint.Z] at *; omega
            have hb2 : 0 ≤ sint.Z (W64 (sint.Z (W32 (k : Int)))) ∧
                sint.Z (W64 (sint.Z (W32 (k : Int)))) < sint.Z tos.len := by
              rw [hidx]; have := Hs2.1; have := Hs2.2; simp only [sint.nat, sint.Z] at *; omega
            have hkt : (sint.Z (W64 (sint.Z (W32 (k : Int))))).toNat = k := by rw [hidx]; simp
            obtain ⟨pv, hpv⟩ : ∃ pv, l1[k]? = some pv := ⟨_, List.getElem?_eq_getElem (by omega)⟩
            obtain ⟨tv, htv⟩ : ∃ tv, l2[k]? = some tv := ⟨_, List.getElem?_eq_getElem (by omega)⟩
            simp only [hb1, _root_.and_self, ↓reduceIte]
            wp_apply wp_load_slice_index pis _ l1 _ pv hb1.1 $$ [$Hpis] as Hpis
            · ipureintro; rw [hkt]; exact hpv
            wp_if_destruct
            · -- the same problem instance: its timeout grows
              have hcpv : c = pv := Hif
              simp only [hb2, _root_.and_self, ↓reduceIte]
              wp_auto
              simp only [hb2, _root_.and_self, ↓reduceIte]
              wp_apply wp_load_slice_index tos _ l2 _ tv hb2.1 $$ [$Htos] as Htos
              · ipureintro; rw [hkt]; exact htv
              wp_apply wp_store_slice_index $$ [$Htos] as Htos
              · ipureintro; rw [Hl2, hidx]; omega
              have hl2' : (l2.set k (tv + W64 1000000)).length = 5 := by simp [Hl2]
              simp only [hb2, _root_.and_self, ↓reduceIte]
              rw [hkt]
              wp_apply wp_load_slice_index tos _ _ _ (tv + W64 1000000) hb2.1 $$ [$Htos] as Htos
              · ipureintro; rw [hkt]; exact List.getElem?_set_self (by omega)
              wp_if_destruct
              · -- the grace period is over: ask for the recovery of `inst ..= crtInstance[q]`
                ihave ⟨Hfrag, #Hlb⟩ := crtLb_get γ i k σ' $$ Hfrag
                have hcq : σ'.crtInstance k = σ0.crtInstance k := by rw [Hrel.crt]
                simp only [hb1, _root_.and_self, ↓reduceIte]
                wp_apply wp_load_slice_index pis _ l1 _ pv hb1.1 $$ [$Hpis] as Hpis
                · ipureintro; rw [hkt]; exact hpv
                ihave HK : (∃ kv : w32, "kk" ∷ k_ptr ↦ kv ∗ "%Hkv" ∷ ⌜0 ≤ zz kv⌝ ∗
                    "Htr" ∷ (∃ (sl : GoSlice) (ptrs : List Loc), toRecover_ptr ↦ sl ∗ sl ↦* ptrs ∗
                      ownSliceCap Loc sl (DFrac.own 1) ∗ [∗list] x ∈ ptrs, exRecoverReq γ i x) :
                    IProp GF) $$ [k Htr]
                · iexists pv; iframe; ipureintro; rw [← hcpv]; exact Hc
                wp_for HK
                simp only [hbc, _root_.and_self, ↓reduceIte]
                wp_apply wp_load_slice_index crt _ _ _ (σ0.crtInstance k) hbc.1 $$ [$Hcrt] as Hcrt
                · ipureintro; exact hgk _
                wp_if_destruct
                · -- append `&instanceId{q, k}`
                  icases Htr with ⟨%sl, %ptrsr, Htrp, Hsl, Hslcap, Hreqs⟩
                  wp_auto
                  wp_bind (App (Val (GoInstruction (CompositeLiteral
                    (go.SliceType (go.PointerType epaxos.instanceId.ty))))) (Val (LiteralValueV _)))
                  iapply wp_slice_literal (V := Loc) (t := go.PointerType epaxos.instanceId.ty) [«$sl0_ptr»]
                  wp_auto
                  isplitl []
                  · ipureintro; rfl
                  iintro %lit_ptr ⟨Hlit, -⟩
                  wp_apply wp_slice_append (V := Loc) sl ptrsr _ [«$sl0_ptr»] (DFrac.own 1)
                    $$ [$Hsl $Hslcap $Hlit] as %sl2 ⟨Hsl2, Hsl2cap, -⟩
                  have hkle : zz kv ≤ zz (σ0.crtInstance k) := by
                    simp only [zz]; exact of_decide_eq_true (go.intoVal_inj Hif)
                  wp_for_post
                  iframe
                  iexists kv + W32 1
                  iframe
                  isplitr
                  · ipureintro
                    have := hcrtk.2; unfold MAX_INSTANCE at this; simp only [toN, zz] at *; word
                  iexists sl2, ptrsr ++ [«$sl0_ptr»]
                  iframe
                  iapply BigSepL.bigSepL_singleton.2
                  unfold exRecoverReq
                  iexists k, toN kv, σ0.crtInstance k
                  rw [show W32 ((toN kv : Nat) : Int) = kv by simp only [toN, zz] at *; word]
                  iframe
                  isplitl
                  · rw [← hcq]; iexact Hlb
                  ipureintro; refine ⟨hkn, ?_⟩; simp only [toN, zz] at *; omega
                · have hnot : decide (sint.Z kv ≤ sint.Z (σ0.crtInstance k)) = false := by
                    cases h : decide (sint.Z kv ≤ sint.Z (σ0.crtInstance k))
                    · rfl
                    · rw [h] at Hif; exact absurd rfl Hif
                  simp only [hnot, Bool.false_eq_true, ↓reduceIte]
                  wp_auto
                  simp only [hb2, _root_.and_self, ↓reduceIte]
                  wp_apply wp_store_slice_index $$ [$Htos] as Htos
                  · ipureintro; rw [hl2', hidx]; omega
                  wp_for_post
                  wp_for_post
                  iframe
                  iexists k + 1, σ0, σ'
                  rw [show W32 (k : Int) + W32 1 = W32 ((k + 1 : Nat) : Int) by push_cast; word]
                  iframe
                  isplitr; · ipureintro; omega
                  isplitl [Heut]
                  · iexists eut; iframe Heutf Heut
                  isplitl [Hcrt]
                  · iexists crt; iframe Hcrtf Hcrt
                  isplitr; · ipureintro; exact ⟨Hrel, Hok, Hib⟩
                  isplitl [Hpis]
                  · iexists _; iframe Hpis; ipureintro; simp [Hl1]
                  iexists _; iframe Htos; ipureintro; simp [Hl2]
              · wp_for_post
                wp_for_post
                iframe
                iexists k + 1, σ0, σ'
                rw [show W32 (k : Int) + W32 1 = W32 ((k + 1 : Nat) : Int) by push_cast; word]
                iframe
                isplitr; · ipureintro; omega
                isplitl [Heut]
                · iexists eut; iframe Heutf Heut
                isplitl [Hcrt]
                · iexists crt; iframe Hcrtf Hcrt
                isplitr; · ipureintro; exact ⟨Hrel, Hok, Hib⟩
                isplitl [Hpis]
                · iexists _; iframe Hpis; ipureintro; simp [Hl1]
                iexists _; iframe Htos; ipureintro; exact hl2'
            · -- a new problem instance
              simp only [hb1, _root_.and_self, ↓reduceIte]
              wp_apply wp_store_slice_index $$ [$Hpis] as Hpis
              · ipureintro; rw [Hl1]; rw [hidx]; omega
              simp only [hb2, _root_.and_self, ↓reduceIte]
              wp_apply wp_store_slice_index $$ [$Htos] as Htos
              · ipureintro; rw [Hl2]; rw [hidx]; omega
              wp_for_post
              wp_for_post
              iframe
              iexists k + 1, σ0, σ'
              rw [show W32 (k : Int) + W32 1 = W32 ((k + 1 : Nat) : Int) by push_cast; word]
              iframe
              isplitr; · ipureintro; omega
              isplitl [Heut]
              · iexists eut; iframe Heutf Heut
              isplitl [Hcrt]
              · iexists crt; iframe Hcrtf Hcrt
              isplitr; · ipureintro; exact ⟨Hrel, Hok, Hib⟩
              isplitl [Hpis]
              · iexists _; iframe Hpis; ipureintro; simp [Hl1]
              iexists _; iframe Htos; ipureintro; simp [Hl2]
          · -- `Cmds == nil`?
            simp only [h1, _root_.and_self, ↓reduceIte]
            wp_apply wp_load_slice_index iss _ rows _ row h1.1 $$ [$Hrows] as -
            · ipureintro; exact hrowk
            simp only [h2, _root_.and_self, ↓reduceIte]
            wp_apply wp_load_slice_index row _ ptrs _ ptr h2.1 $$ [$Hptrs] as Hptrs
            · ipureintro; exact hptrc
            rcases hcv : w.cmds with _ | cs
            · -- no commands: a problem instance
              unfold cmdsRep; icases Hycmds with %Hnil
              rw [Hnil]
              wp_auto
              ihave Hins := Hclose $$ %ptr %(some w) [Hptrs] [Hy Hydeps Hylb]
              · rw [hpset]; iexact Hptrs
              · dsimp only; iexists y; iframe Hy Hydeps Hylb
                isplitr
                · ipureintro; exact Hyf
                isplitr
                · iexact Hyid
                try rw [hcv]
                ipureintro; exact Hnil
              rw [upd_self _ _ _ hx]
              -- PROBLEM
              icases Hpis with ⟨%l1, Hpis, %Hl1⟩
              icases Htos with ⟨%l2, Htos, %Hl2⟩
              ihave %Hs1 := ownSlice_len _ _ _ $$ Hpis
              ihave %Hs2 := ownSlice_len _ _ _ $$ Htos
              have hb1 : 0 ≤ sint.Z (W64 (sint.Z (W32 (k : Int)))) ∧
                  sint.Z (W64 (sint.Z (W32 (k : Int)))) < sint.Z pis.len := by
                rw [hidx]; have := Hs1.1; have := Hs1.2; simp only [sint.nat, sint.Z] at *; omega
              have hb2 : 0 ≤ sint.Z (W64 (sint.Z (W32 (k : Int)))) ∧
                  sint.Z (W64 (sint.Z (W32 (k : Int)))) < sint.Z tos.len := by
                rw [hidx]; have := Hs2.1; have := Hs2.2; simp only [sint.nat, sint.Z] at *; omega
              have hkt : (sint.Z (W64 (sint.Z (W32 (k : Int))))).toNat = k := by rw [hidx]; simp
              obtain ⟨pv, hpv⟩ : ∃ pv, l1[k]? = some pv := ⟨_, List.getElem?_eq_getElem (by omega)⟩
              obtain ⟨tv, htv⟩ : ∃ tv, l2[k]? = some tv := ⟨_, List.getElem?_eq_getElem (by omega)⟩
              simp only [hb1, _root_.and_self, ↓reduceIte]
              wp_apply wp_load_slice_index pis _ l1 _ pv hb1.1 $$ [$Hpis] as Hpis
              · ipureintro; rw [hkt]; exact hpv
              wp_if_destruct
              · -- the same problem instance: its timeout grows
                have hcpv : c = pv := Hif
                simp only [hb2, _root_.and_self, ↓reduceIte]
                wp_auto
                simp only [hb2, _root_.and_self, ↓reduceIte]
                wp_apply wp_load_slice_index tos _ l2 _ tv hb2.1 $$ [$Htos] as Htos
                · ipureintro; rw [hkt]; exact htv
                wp_apply wp_store_slice_index $$ [$Htos] as Htos
                · ipureintro; rw [Hl2, hidx]; omega
                have hl2' : (l2.set k (tv + W64 1000000)).length = 5 := by simp [Hl2]
                simp only [hb2, _root_.and_self, ↓reduceIte]
                rw [hkt]
                wp_apply wp_load_slice_index tos _ _ _ (tv + W64 1000000) hb2.1 $$ [$Htos] as Htos
                · ipureintro; rw [hkt]; exact List.getElem?_set_self (by omega)
                wp_if_destruct
                · -- the grace period is over: ask for the recovery of `inst ..= crtInstance[q]`
                  ihave ⟨Hfrag, #Hlb⟩ := crtLb_get γ i k σ' $$ Hfrag
                  have hcq : σ'.crtInstance k = σ0.crtInstance k := by rw [Hrel.crt]
                  simp only [hb1, _root_.and_self, ↓reduceIte]
                  wp_apply wp_load_slice_index pis _ l1 _ pv hb1.1 $$ [$Hpis] as Hpis
                  · ipureintro; rw [hkt]; exact hpv
                  ihave HK : (∃ kv : w32, "kk" ∷ k_ptr ↦ kv ∗ "%Hkv" ∷ ⌜0 ≤ zz kv⌝ ∗
                      "Htr" ∷ (∃ (sl : GoSlice) (ptrs : List Loc), toRecover_ptr ↦ sl ∗ sl ↦* ptrs ∗
                        ownSliceCap Loc sl (DFrac.own 1) ∗ [∗list] x ∈ ptrs, exRecoverReq γ i x) :
                      IProp GF) $$ [k Htr]
                  · iexists pv; iframe; ipureintro; rw [← hcpv]; exact Hc
                  wp_for HK
                  simp only [hbc, _root_.and_self, ↓reduceIte]
                  wp_apply wp_load_slice_index crt _ _ _ (σ0.crtInstance k) hbc.1 $$ [$Hcrt] as Hcrt
                  · ipureintro; exact hgk _
                  wp_if_destruct
                  · -- append `&instanceId{q, k}`
                    icases Htr with ⟨%sl, %ptrsr, Htrp, Hsl, Hslcap, Hreqs⟩
                    wp_auto
                    wp_bind (App (Val (GoInstruction (CompositeLiteral
                      (go.SliceType (go.PointerType epaxos.instanceId.ty))))) (Val (LiteralValueV _)))
                    iapply wp_slice_literal (V := Loc) (t := go.PointerType epaxos.instanceId.ty) [«$sl0_ptr»]
                    wp_auto
                    isplitl []
                    · ipureintro; rfl
                    iintro %lit_ptr ⟨Hlit, -⟩
                    wp_apply wp_slice_append (V := Loc) sl ptrsr _ [«$sl0_ptr»] (DFrac.own 1)
                      $$ [$Hsl $Hslcap $Hlit] as %sl2 ⟨Hsl2, Hsl2cap, -⟩
                    have hkle : zz kv ≤ zz (σ0.crtInstance k) := by
                      simp only [zz]; exact of_decide_eq_true (go.intoVal_inj Hif)
                    wp_for_post
                    iframe
                    iexists kv + W32 1
                    iframe
                    isplitr
                    · ipureintro
                      have := hcrtk.2; unfold MAX_INSTANCE at this; simp only [toN, zz] at *; word
                    iexists sl2, ptrsr ++ [«$sl0_ptr»]
                    iframe
                    iapply BigSepL.bigSepL_singleton.2
                    unfold exRecoverReq
                    iexists k, toN kv, σ0.crtInstance k
                    rw [show W32 ((toN kv : Nat) : Int) = kv by simp only [toN, zz] at *; word]
                    iframe
                    isplitl
                    · rw [← hcq]; iexact Hlb
                    ipureintro; refine ⟨hkn, ?_⟩; simp only [toN, zz] at *; omega
                  · have hnot : decide (sint.Z kv ≤ sint.Z (σ0.crtInstance k)) = false := by
                      cases h : decide (sint.Z kv ≤ sint.Z (σ0.crtInstance k))
                      · rfl
                      · rw [h] at Hif; exact absurd rfl Hif
                    simp only [hnot, Bool.false_eq_true, ↓reduceIte]
                    wp_auto
                    simp only [hb2, _root_.and_self, ↓reduceIte]
                    wp_apply wp_store_slice_index $$ [$Htos] as Htos
                    · ipureintro; rw [hl2', hidx]; omega
                    wp_for_post
                    wp_for_post
                    iframe
                    iexists k + 1, σ0, σ'
                    rw [show W32 (k : Int) + W32 1 = W32 ((k + 1 : Nat) : Int) by push_cast; word]
                    iframe
                    isplitr; · ipureintro; omega
                    isplitl [Heut]
                    · iexists eut; iframe Heutf Heut
                    isplitl [Hcrt]
                    · iexists crt; iframe Hcrtf Hcrt
                    isplitr; · ipureintro; exact ⟨Hrel, Hok, Hib⟩
                    isplitl [Hpis]
                    · iexists _; iframe Hpis; ipureintro; simp [Hl1]
                    iexists _; iframe Htos; ipureintro; simp [Hl2]
                · wp_for_post
                  wp_for_post
                  iframe
                  iexists k + 1, σ0, σ'
                  rw [show W32 (k : Int) + W32 1 = W32 ((k + 1 : Nat) : Int) by push_cast; word]
                  iframe
                  isplitr; · ipureintro; omega
                  isplitl [Heut]
                  · iexists eut; iframe Heutf Heut
                  isplitl [Hcrt]
                  · iexists crt; iframe Hcrtf Hcrt
                  isplitr; · ipureintro; exact ⟨Hrel, Hok, Hib⟩
                  isplitl [Hpis]
                  · iexists _; iframe Hpis; ipureintro; simp [Hl1]
                  iexists _; iframe Htos; ipureintro; exact hl2'
              · -- a new problem instance
                simp only [hb1, _root_.and_self, ↓reduceIte]
                wp_apply wp_store_slice_index $$ [$Hpis] as Hpis
                · ipureintro; rw [Hl1]; rw [hidx]; omega
                simp only [hb2, _root_.and_self, ↓reduceIte]
                wp_apply wp_store_slice_index $$ [$Htos] as Htos
                · ipureintro; rw [Hl2]; rw [hidx]; omega
                wp_for_post
                wp_for_post
                iframe
                iexists k + 1, σ0, σ'
                rw [show W32 (k : Int) + W32 1 = W32 ((k + 1 : Nat) : Int) by push_cast; word]
                iframe
                isplitr; · ipureintro; omega
                isplitl [Heut]
                · iexists eut; iframe Heutf Heut
                isplitl [Hcrt]
                · iexists crt; iframe Hcrtf Hcrt
                isplitr; · ipureintro; exact ⟨Hrel, Hok, Hib⟩
                isplitl [Hpis]
                · iexists _; iframe Hpis; ipureintro; simp [Hl1]
                iexists _; iframe Htos; ipureintro; simp [Hl2]
            · -- committed with commands: execute it (and what it reaches)
              unfold cmdsRep; icases Hycmds with ⟨%Hcnn, #Hcs⟩
              simp only [decide_eq_false Hcnn]
              wp_auto
              ihave Hins := Hclose $$ %ptr %(some w) [Hptrs] [Hy Hydeps Hylb]
              · rw [hpset]; iexact Hptrs
              · dsimp only; iexists y; iframe Hy Hydeps Hylb
                isplitr
                · ipureintro; exact Hyf
                isplitr
                · iexact Hyid
                try rw [hcv]
                isplitr
                · ipureintro; exact Hcnn
                iexact Hcs
              rw [upd_self _ _ _ hx]
              icases Hstk with ⟨%s1, %xs1, Hst, Hs, Hcap, %Hcap1⟩
              ihave Heut : repRowArr r go!"ExecedUpTo" σ'.execedUpTo $$ [Heut]
              · unfold repRowArr; iexists eut; iframe Heutf Heut
              have hq' : 0 ≤ zz (W32 (k : Int)) ∧ zz (W32 (k : Int)) < nR := by
                simp only [zz]; rw [hzk]; omega
              have hn' : 0 ≤ zz c ∧ toN c + 1 < MAX_INSTANCE := ⟨Hc, hcn⟩
              wp_apply (wp_executeCommand γ i r e rr L p Rext (wp_strongconnect hEx hRP γ i r e rr L p Rext)
                σ' (W32 (k : Int)) c s1 xs1 Hok.1 Hib hi hq' hn')
                $$ [$Hctx $Hins $Heut $Hstore $Hst $Hs $Hcap $Hfrag $Hpend $Hcur]
                as %b ⟨%σ'', Hins, Heut, Hstore, Hstk, Hfrag, Hpend, Hcur, %Hpost⟩
              · ipureintro; exact Hcap1
              obtain ⟨hER, hwf'', hib'', hbex⟩ := Hpost
              have Hrel2 := Hrel.exRel hER
              have Hok2 := Hok.exRel hER hwf''
              unfold repRowArr
              icases Heut with ⟨%eut2, #Heutf2, Heut⟩
              icombine Heutf2 Heutf gives %Heq2
              subst eut2
              have hc1 : 0 ≤ zz (c + W32 1) := by
                have := hcrtk.2; unfold MAX_INSTANCE at this; simp only [toN, zz] at *; word
              icases executed with ⟨%bx, executed⟩
              cases b
              · -- not executed (yet)
                wp_auto
                ihave Hcrt : repRowArr r go!"crtInstance" σ0.crtInstance $$ [Hcrt]
                · unfold repRowArr; iexists crt; iframe Hcrtf Hcrt
                ihave Heut : repRowArr r go!"ExecedUpTo" (σ'').execedUpTo $$ [Heut]
                · unfold repRowArr; iexists eut; iframe Heutf Heut
                -- fix E1-opt1 (E1-opt2: no Gosched): release the lock between roots and take it again
                ihave ⟨Hlocked, HR⟩ := scan_pack γ i r e lp σ0 (σ'') (Hrel2) (hib'') $$ He Hrest Hcrt Hins Heut Hstore
                  Hfrag Hpend Hcur Hstk
                wp_apply (lc := 1) sync.Mutex.wp_Unlock $$ [$Hlock $Hlocked HR]
                · inext; iexact HR
                wp_apply sync.Mutex.wp_Lock $$ [$Hlock] as ⟨Hlocked, HL⟩
                -- the loop's post statement (`inst++`) is a WP: open the invariant there
                iapply wp_for_post_do
                iapply fupd_wp
                imod (scan_unpack γ i r e lp hi) $$ Hinv He Hlocked HL Hlc1
                  with ⟨%σ1, Hrest, Hcrt, Hins, Heut, Hstore, Hfrag, Hpend, Hcur, Hstk, %Hok1⟩
                imodintro
                unfold repRowArr
                icases Hcrt with ⟨%crt1, #Hcrtf1, Hcrt⟩
                icombine Hcrtf Hcrtf1 gives %Hcrt1
                subst Hcrt1
                icases Heut with ⟨%eut1, #Heutf1, Heut⟩
                icombine Heutf Heutf1 gives %Heut1
                subst Heut1
                wp_pures
                try wp_auto
                iframe
                iexists c + W32 1, σ1, σ1
                iframe
                isplitr; · ipureintro; exact hc1
                isplitr; · ipureintro; exact ⟨ScanRel.refl σ1, Hok1.1, Hok1.2⟩
                iexists bx; iframe
              · -- executed: `executed = true`, and `ExecedUpTo[q]` moves past it if it is the next one
                have hexk : σ''.executed ⟨k, toN c⟩ := by
                  have := hbex rfl
                  rwa [show toN (W32 (k : Int)) = k by simp only [toN]; rw [hzk]; simp] at this
                wp_auto
                simp only [hbe, _root_.and_self, ↓reduceIte]
                wp_apply (lc := 1) wp_load_slice_index eut _ _ _ (σ''.execedUpTo k) hbe.1 $$ [$Heut] as Heut
                · ipureintro; exact hgk _
                wp_if_destruct
                · have hex : σ''.executed ⟨k, toN (σ''.execedUpTo k + 1)⟩ := hexk
                  iapply fupd_wp
                  imod (ep_execBump γ ⊤ i σ'' k (by simp) hi hkn hex) $$ Hinv Hfrag Hlc1 with Hfrag
                  imodintro
                  simp only [hbe, _root_.and_self, ↓reduceIte]
                  wp_apply wp_store_slice_index $$ [$Heut] as Heut
                  · ipureintro; simp only [List.length_map, List.length_range]; rw [hidx]; unfold nR; omega
                  have e1 : (List.map σ''.execedUpTo (List.range nR)).set
                      (sint.Z (W64 (sint.Z (W32 (k : Int))))).toNat (σ''.execedUpTo k + W32 1) =
                      List.map (execBump σ'' k).execedUpTo (List.range nR) := by
                    rw [hidx]; simp only [Int.toNat_natCast, execBump]
                    rw [map_range_upd _ _ _ _ hkn]; rfl
                  ihave Heut : eut ↦* List.map (execBump σ'' k).execedUpTo (List.range nR) $$ [Heut]
                  · rw [← e1]; iexact Heut
                  ihave Hcrt : repRowArr r go!"crtInstance" σ0.crtInstance $$ [Hcrt]
                  · unfold repRowArr; iexists crt; iframe Hcrtf Hcrt
                  ihave Heut : repRowArr r go!"ExecedUpTo" (execBump σ'' k).execedUpTo $$ [Heut]
                  · unfold repRowArr; iexists eut; iframe Heutf Heut
                  -- fix E1-opt1 (E1-opt2: no Gosched): release the lock between roots and take it again
                  rw [show σ''.inst = (execBump σ'' k).inst from rfl,
                    show σ''.store = (execBump σ'' k).store from rfl]
                  ihave ⟨Hlocked, HR⟩ := scan_pack γ i r e lp σ0 (execBump σ'' k) (Hrel2.bump k) (hib'') $$ He Hrest Hcrt Hins Heut Hstore
                    Hfrag Hpend Hcur Hstk
                  wp_apply (lc := 1) sync.Mutex.wp_Unlock $$ [$Hlock $Hlocked HR]
                  · inext; iexact HR
                  wp_apply sync.Mutex.wp_Lock $$ [$Hlock] as ⟨Hlocked, HL⟩
                  -- the loop's post statement (`inst++`) is a WP: open the invariant there
                  iapply wp_for_post_do
                  iapply fupd_wp
                  imod (scan_unpack γ i r e lp hi) $$ Hinv He Hlocked HL Hlc1
                    with ⟨%σ1, Hrest, Hcrt, Hins, Heut, Hstore, Hfrag, Hpend, Hcur, Hstk, %Hok1⟩
                  imodintro
                  unfold repRowArr
                  icases Hcrt with ⟨%crt1, #Hcrtf1, Hcrt⟩
                  icombine Hcrtf Hcrtf1 gives %Hcrt1
                  subst Hcrt1
                  icases Heut with ⟨%eut1, #Heutf1, Heut⟩
                  icombine Heutf Heutf1 gives %Heut1
                  subst Heut1
                  wp_pures
                  try wp_auto
                  iframe
                  iexists σ''.execedUpTo k + W32 1 + W32 1, σ1, σ1
                  iframe
                  isplitr; · ipureintro; exact hc1
                  isplitr; · ipureintro; exact ⟨ScanRel.refl σ1, Hok1.1, Hok1.2⟩
                  iexists true; iframe
                · iclear Hlc1
                  ihave Hcrt : repRowArr r go!"crtInstance" σ0.crtInstance $$ [Hcrt]
                  · unfold repRowArr; iexists crt; iframe Hcrtf Hcrt
                  ihave Heut : repRowArr r go!"ExecedUpTo" (σ'').execedUpTo $$ [Heut]
                  · unfold repRowArr; iexists eut; iframe Heutf Heut
                  -- fix E1-opt1 (E1-opt2: no Gosched): release the lock between roots and take it again
                  ihave ⟨Hlocked, HR⟩ := scan_pack γ i r e lp σ0 (σ'') (Hrel2) (hib'') $$ He Hrest Hcrt Hins Heut Hstore
                    Hfrag Hpend Hcur Hstk
                  wp_apply (lc := 1) sync.Mutex.wp_Unlock $$ [$Hlock $Hlocked HR]
                  · inext; iexact HR
                  wp_apply sync.Mutex.wp_Lock $$ [$Hlock] as ⟨Hlocked, HL⟩
                  -- the loop's post statement (`inst++`) is a WP: open the invariant there
                  iapply wp_for_post_do
                  iapply fupd_wp
                  imod (scan_unpack γ i r e lp hi) $$ Hinv He Hlocked HL Hlc1
                    with ⟨%σ1, Hrest, Hcrt, Hins, Heut, Hstore, Hfrag, Hpend, Hcur, Hstk, %Hok1⟩
                  imodintro
                  unfold repRowArr
                  icases Hcrt with ⟨%crt1, #Hcrtf1, Hcrt⟩
                  icombine Hcrtf Hcrtf1 gives %Hcrt1
                  subst Hcrt1
                  icases Heut with ⟨%eut1, #Heutf1, Heut⟩
                  icombine Heutf Heutf1 gives %Heut1
                  subst Heut1
                  wp_pures
                  try wp_auto
                  iframe
                  iexists c + W32 1, σ1, σ1
                  iframe
                  isplitr; · ipureintro; exact hc1
                  isplitr; · ipureintro; exact ⟨ScanRel.refl σ1, Hok1.1, Hok1.2⟩
                  iexists true; iframe
              done
    · -- the row is done: next row
      have hnot : decide (sint.Z c ≤ sint.Z (σ0.crtInstance k)) = false := by
        cases h : decide (sint.Z c ≤ sint.Z (σ0.crtInstance k))
        · rfl
        · rw [h] at Hif; exact absurd rfl Hif
      simp only [hnot, Bool.false_eq_true, ↓reduceIte]
      wp_for_post
      iframe
      iexists k + 1, σ0, σ'
      rw [show W32 (k : Int) + W32 1 = W32 ((k + 1 : Nat) : Int) by push_cast; word]
      iframe
      isplitr; · ipureintro; omega
      isplitl [Heut]
      · iexists eut; iframe Heutf Heut
      isplitl [Hcrt]
      · iexists crt; iframe Hcrtf Hcrt
      ipureintro; exact ⟨Hrel, Hok, Hib⟩
  · -- the scan is over: unlock
    obtain ⟨Hrel, Hok, Hib⟩ := Hσ
    ihave ⟨Hlocked, HR⟩ := scan_pack γ i r e lp σ0 σ Hrel Hib $$ He Hrest Hcrt Hins Heut Hstore
      Hfrag Hpend Hcur Hstk
    wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hlocked HR]
    · inext; iexact HR
    -- send the recovery requests (unlocked)
    icases Htr with ⟨%sl, %ptrsr, Htrp, Hsl, Hslcap, Hreqs⟩
    wp_auto
    ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
    ihave HR : (∃ j : Nat, "i" ∷ i_ptr ↦ W64 (j : Int) ∗ "%Hj" ∷ ⌜j ≤ ptrsr.length⌝ ∗
        "Hsl" ∷ sl ↦* ptrsr ∗ "Hreqs" ∷ ([∗list] x ∈ ptrsr.drop j, exRecoverReq γ i x) ∗
        "iid" ∷ (∃ v : Loc, iid_ptr ↦ v) : IProp GF) $$ [i Hsl Hreqs iid]
    · iexists 0; iframe; isplitr; · ipureintro; omega
      iexists _; iframe
    wp_for HR
    wp_if_destruct
    · -- send `toRecover[j]`
      have hjl : j < ptrsr.length := by
        have := Hsll.1; have := Hsll.2; simp only [sint.nat, sint.Z] at *; word
      have hjb : 0 ≤ sint.Z (W64 (j : Int)) ∧ sint.Z (W64 (j : Int)) < sint.Z sl.len := by
        have := Hsll.1; have := Hsll.2; simp only [sint.nat, sint.Z] at *; constructor <;> word
      have hjt : (sint.Z (W64 (j : Int))).toNat = j := by
        have := Hsll.1; have := Hsll.2; simp only [sint.nat, sint.Z] at *; word
      obtain ⟨v, hv⟩ : ∃ v, ptrsr[j]? = some v := ⟨_, List.getElem?_eq_getElem hjl⟩
      simp only [hjb, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index sl _ ptrsr _ v hjb.1 $$ [$Hsl] as Hsl
      · ipureintro; rw [hjt]; exact hv
      icases iid with ⟨%v0, iid⟩
      wp_auto
      rw [List.drop_eq_getElem_cons hjl, show ptrsr[j] = v from (List.getElem?_eq_some_iff.mp hv).2]
      icases (BigSepL.bigSepL_cons).1 $$ Hreqs with ⟨Hreq, Hreqs⟩
      wp_apply (wp_bag_send (V := Loc) γc ch v (exRecoverReq γ i)) $$ [$Hbag $Hreq]
      wp_for_post
      iframe
      iexists j + 1
      rw [show W64 (j : Int) + W64 1 = W64 ((j + 1 : Nat) : Int) by push_cast; word]
      iframe
      isplitr; · ipureintro; omega
      iexists v; iframe
    · -- the pass is over: sleep if nothing was executed
      icases executed with ⟨%bx, executed⟩
      wp_auto
      cases bx
      · wp_auto
        wp_apply sync.Mutex.wp_Lock $$ [$HM] as ⟨HMl, HMR⟩
        wp_apply sync.Mutex.wp_Unlock $$ [$HM $HMl $HMR]
        wp_apply time.wp_Sleep
        wp_for_post
        iframe
        isplitl [Hpis]
        · iexact Hpis
        · iexact Htos
      · wp_auto
        wp_for_post
        iframe
        isplitl [Hpis]
        · iexact Hpis
        · iexact Htos

/-- The run loop's `ExecuteCommandsSpec` (RunSpec.lean), from `wp_executeCommands` with the
callee specs (`Execute`, `ReplyProposeTS`; linked in Epaxos/Interface/Epaxos.lean). -/
theorem executeCommandsSpec_of (hEx : state.Command.Execute.spec (GF := GF))
    (hRP : replica.Replica.ReplyProposeTS.spec (GF := GF)) : ExecuteCommandsSpec (GF := GF) := by
  intro γ i r rr L p Rext ord e ch γc
  iintro %Φ ⟨Hctx, #He, #Her, #Hch, #Hbag⟩ HΦ
  unfold hctx
  icases Hctx with ⟨#Hpk, #Hisr, #Hrr, #Hfw, -⟩
  iapply (wp_executeCommands hEx hRP γ i r rr L p Rext e ch γc) $$ [] HΦ
  iframe #
  unfold exRecoverReq recoverReq
  iexact Hbag

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
