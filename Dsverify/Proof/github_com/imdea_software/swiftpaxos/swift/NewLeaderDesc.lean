/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/NewLeaderDesc.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
**Rounds 49-54 (sv-swb): the descriptor side of N1-R1/N1-R2** (D56, D65 (3), D70, D74; NewLeaderReqs.lean's
`swift.N1R1`/`swift.N1R2`; notes/prove-swift.md §57-§62, notes/lifecycle-table.md 11b.8-11b.13).

* **Coverage from the store** (T22: "coverage from `Rt` inside `nodeInvD`'s opening"), proved:
  `swift.rowsCover`: in the stopped epoch (ledger `Out = ∅`), every command with a row of
  `cballot` `c` is of the base `B` (a `sync` record, by `syncIs` agreement), or has a stored record
  that is `exec`, `rest d γi` or `released` (an `empty` record has no rows; a `sync` record at
  `c = 0` is refuted by `sync_ok`, `sp.syncIs_pos`). `swift.execRecs_in` (round 51): an `exec`
  record of `c` is a command of the record `X` of `c` (its `exIn` against `delivInv`'s `γxm`).
* `swift.n1r1` (rounds 51-54, frame lemmas): `Fz := swift.fzX` (round 52, D71 (1): a quarter of
  `γx` and half of `γxm`'s authority out of `delivInv`'s frozen-mode slot `swift.delivFz`), `W :=
  repEntW`, `Wd := swift.pdW`. Proved: `freeze`/`thaw` (`swift.fz_freeze`/`swift.fz_thaw`), `exec`
  (the record is `Fz`'s; the log's entries `xsEnt` with their log facts and witnesses), `deliv`.
  `swift.exec_wit` (round 52, 51-5) and, round 54, `swift.exec_wit_follower` (from `exEntOkE`'s
  `exFolW`) are proved. `desc` and `Wd_seq` (round 54, N6) are R54 sorries.
* `swift.n1r2`: clauses 3 (`dl`) and 4 (`swift.pd_deps`) and clause 2's base/`empty`/`sync`/`exec`
  cases proved; the entries' facts (clause 1) is a named sorry `R54:`.
* Round 58 (D82): `swift.n1r1` has no sorry (`desc`: `swift.incKey`, `swift.claimRead`,
  `swift.storedW`, `swift.pdOk_pdW`, `swift.fz_exIn`); N1-R2's clause 1 is proved for the log's
  entries (`WX`) and all but a follower's read below `COMMIT` (`R58:`).
* Round 56 (D79): clause 2's `rest` records (`swift.restRead`: the record's `cgW` against the
  stopped epoch's `incInv`, `stopPS`) proved but for a record without a proposal under an accepted
  or committed row (`R56:`); `released` records `R56:` (50-4). N4's R2-a proved
  (`swift.r2a_all`, over `W`'s base fact `swift.baseW`).
* Round B1 (D81): a rest record without a proposal has an empty row (`rowFacts`: an accepted or
  committed row has a proposal), so it has no row at `c`: the `R56:` case is refuted.
* Round 59 (D84 (2)): `swift.n1r2` has no sorry. A read with a proposal holds its stored home's
  claim (`swift.rdCl`, handed out by `desc`, held by FillAckN until after the report), which finds
  the read's own rest record of `(c, y)`: its token puts `y` in `r`'s sequence (`rowsOk`) and its
  `rowPhaseOk`, at the read's values, is clause 1 (`swift.readRec`, `swift.readEnt1`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.NewLeaderReqs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.Store
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.SyncSeq
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.ProposePure
import all Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Inv

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

/-! ## Pure -/

/-- `y` has a row of `c` at `st` (accepted, committed or pre-accepted: `coverOk`'s clause 2). -/
def swift.rowNE (st : sp.RState) (c : Nat) (y : sp.CmdId) : Prop :=
  (c, y) ∈ st.accR ∨ (c, y) ∈ st.comR ∨ (st.preAt c y).isSome

theorem swift.rowsOf_ne_empty (st : sp.RState) (c : Nat) (y : sp.CmdId)
    (h : swift.rowNE st c y) : swift.rowsOf st c y ≠ swift.rowEmpty := by
  unfold swift.rowNE at h
  unfold swift.rowsOf swift.rowEmpty
  intro he
  simp only [Prod.mk.injEq] at he
  rcases h with h | h | h
  · have := he.2.2.1; simp [h] at this
  · have := he.2.2.2; simp [h] at this
  · rw [he.1] at h; simp at h

/-- Round B1 (D81): a command whose row is empty has no row facts at `c`. -/
theorem swift.rowNE_of_empty (st : sp.RState) (O : GMap (Nat × sp.CmdId) swift.RowV) (c : Nat)
    (y : sp.CmdId) (rv : swift.RowV) (hrows : swift.rowsOk st O) (hrv : O.lookup (c, y) = some rv)
    (h1 : rv.1 = none) (h2 : rv.2.1 = none) (h3 : rv.2.2.1 = false) (h4 : rv.2.2.2 = false) :
    ¬ swift.rowNE st c y := by
  intro hy
  have hk : rv = swift.rowsOf st c y := by
    have h := hrows c y
    revert h
    rcases e : O.lookup (c, y) with _ | rv'
    · rw [hrv] at e; cases e
    · intro h; rw [hrv] at e; cases e; exact h.1
  apply swift.rowsOf_ne_empty st c y hy
  rw [← hk]
  obtain ⟨r1, r2, r3, r4⟩ := rv
  simp only at h1 h2 h3 h4
  rw [h1, h2, h3, h4]; rfl

/-- A row of `cballot` in the stopped epoch (no key out of the store) has a stored record. -/
theorem swift.rows_stored (st : sp.RState) (c : Nat) (O : GMap (Nat × sp.CmdId) swift.RowV)
    (Rt : GMap (Nat × sp.CmdId) swift.RecK) (Cl : GMap (Nat × sp.CmdId) swift.ClK) (y : sp.CmdId)
    (hy : swift.rowNE st c y) (hst : swift.storeOk c O Rt ∅ Cl) (hrows : swift.rowsOk st O) :
    O.lookup (c, y) = some (swift.rowsOf st c y) ∧ ∃ rk, Rt.lookup (c, y) = some rk := by
  have hne := swift.rowsOf_ne_empty st c y hy
  have hO : O.lookup (c, y) = some (swift.rowsOf st c y) := by
    have h := hrows c y
    revert h
    rcases e : O.lookup (c, y) with _ | rv
    · intro h; exact absurd h hne
    · intro h; rw [h.1]
  refine ⟨hO, ?_⟩
  rcases hst.2.1 (c, y) rfl (by rw [hO]; rfl) with h | h
  · exact Option.isSome_iff_exists.mp h
  · exact absurd h (by simp)

/-- A phase of at most `COMMIT` (round 58). -/
theorem swift.ph_cases (ph : w64) (h : uint.nat ph ≤ 3) :
    ph = W64 0 ∨ ph = W64 1 ∨ ph = W64 2 ∨ ph = W64 3 := by
  rcases (show uint.nat ph = 0 ∨ uint.nat ph = 1 ∨ uint.nat ph = 2 ∨ uint.nat ph = 3 by omega)
    with h | h | h | h
  · left; word
  · right; left; word
  · right; right; left; word
  · right; right; right; word

/-! ## Ghost -/

section ghost
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable {γ : sp.Names} {γc γm γl : GName}

/-- **No `MSync` at ballot 0** (`sync_ok`). -/
theorem sp.syncIs_pos (E : CoPset) (hE : ↑sp.spN ⊆ E) (b : Nat) (M : sp.SyncMsg) :
    sp.inv γ γc γm γl ∗ sp.syncIs γ b M ⊢ |={E}=> ⌜0 < b⌝ := by
  unfold sp.inv sp.syncIs
  iintro ⟨#Hinv, #HM⟩
  iinv Hinv with Hi Hclose
  unfold sp.invBody
  icases Hi with ⟨%S, %mC, %mL, %mS, %mA, %mP, %mCo, %mR, %mN, %sh, %mD, %mQ, %mK, %mPa, HC, HL, >HS, HA, HP, HCo, HRp, HN, HH, HD, Hown, HQ, HK, HPa, >%Hrepr, Hnodes, Hproto, HQs, HCl, HDom, Hslots, Hconns⟩
  ihave %Hlk := ghost_map_lookup $$ HS HM
  have hS : S.sync b = some M := by rw [← Hrepr.sync]; exact Hlk
  icases Hproto with (>%Hemp | ⟨%N, %fr, %l, #Hcfg, >%HP⟩)
  · exact absurd (Hemp.1.2.1 b ▸ hS) (by simp)
  · have hpos := (HP.1.sync_ok b M hS).1
    imod Hclose $$ [HC HL HS HA HP HCo HRp HN HH HD Hown HQ HK HPa Hnodes HQs HCl HDom Hslots Hconns Hcfg] with -
    · inext
      iexists S, mC, mL, mS, mA, mP, mCo, mR, mN, sh, mD, mQ, mK, mPa
      iframe
      isplitr
      · ipureintro; exact Hrepr
      iright
      iexists N, fr, l
      isplitr
      · iexact Hcfg
      ipureintro; exact HP
    imodintro
    ipureintro
    exact hpos

end ghost

section store
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions]

/-- A pure consequence of `P`, keeping `P`. -/
theorem swift.keep_pure {P : IProp netDistGF} {φ : Prop} (h : P ⊢ ⌜φ⌝) : P ⊢ P ∗ ⌜φ⌝ :=
  (BI.and_intro .rfl h).trans BI.persistent_and_sep_mp

/-- A `sync` record's command is a command of its ballot's `MSync`. -/
theorem swift.recSync_in (γ : sp.Names) (γo : GName) (sn : swift.StN)
    (Rt : GMap (Nat × sp.CmdId) swift.RecK) (K : Nat × sp.CmdId) (hK : Rt.lookup K = some .sync) :
    ([∗map] K ↦ rk ∈ Rt, swift.recBody γ γo sn K rk) ⊢ swift.syncIn γ K.1 K.2 := by
  iintro Hm
  ihave ⟨%rv, -, Hw, -⟩ := (BigSepM.bigSepM_lookup (Φ := fun K rk => swift.recBody γ γo sn K rk)
    (show PartialMap.get? Rt K = some .sync from hK)) $$ Hm
  simp only [swift.retWhy]
  icases Hw with ⟨-, #Hs⟩
  iexact Hs

/-- **No `released` record of a ballot whose free permit is held unspent** (round B1, D82 (4)): a
`released` record holds its ballot's permit spent (`retWhy .released`, `swift.freeSp`). -/
theorem swift.noReleased (γ : sp.Names) (γo : GName) (sn : swift.StN)
    (Rt : GMap (Nat × sp.CmdId) swift.RecK) (c : Nat) :
    ([∗map] K ↦ rk ∈ Rt, swift.recBody γ γo sn K rk) ∗ swift.freeP sn.γcg c ⊢
      ⌜∀ y, Rt.lookup (c, y) ≠ some .released⌝ := by
  refine (BI.forall_intro fun y => ?_).trans BI.pure_forall.2
  by_cases h : Rt.lookup (c, y) = some .released
  · iintro ⟨Hm, Hfp⟩
    ihave ⟨%rv, -, Hw, -⟩ := (BigSepM.bigSepM_lookup (Φ := fun K rk => swift.recBody γ γo sn K rk)
      (show PartialMap.get? Rt (c, y) = some .released from h)) $$ Hm
    simp only [swift.retWhy]
    iunfold swift.freeSp at Hw
    icases Hw with ⟨%γ0, #Hw⟩
    iunfold swift.freeP at Hfp
    ihave %Hag := ghostMapElem_agree (c, true) sn.γcg _ _ _ _ $$ Hfp Hw
    cases Hag
  · exact BI.pure_intro (fun h' => h h')

/-- **A row of `cballot`, covered by the store** (see the file header): one command `y`. -/
theorem swift.rowsCover (γ : sp.Names) (γo : GName) (sn : swift.StN) (st : sp.RState) (c : Nat)
    (O : GMap (Nat × sp.CmdId) swift.RowV) (Rt : GMap (Nat × sp.CmdId) swift.RecK)
    (Cl : GMap (Nat × sp.CmdId) swift.ClK) (B : List sp.CmdId) (y : sp.CmdId)
    (hy : swift.rowNE st c y) (hst : swift.storeOk c O Rt ∅ Cl) (hrows : swift.rowsOk st O) :
    ghostMapAuth γo 1 O ∗ ([∗map] K ↦ rk ∈ Rt, swift.recBody γ γo sn K rk) ∗
      (⌜c = 0 ∧ B = []⌝ ∨ ∃ M : sp.SyncMsg, sp.syncIs γ c M ∗ ⌜B = sp.syncOrder M⌝) ⊢
      ⌜y ∈ B ∨ ∃ rk, Rt.lookup (c, y) = some rk ∧ rk ≠ .empty ∧ (rk = .sync → c = 0)⌝ := by
  have hne := swift.rowsOf_ne_empty st c y hy
  obtain ⟨hO, rk, hR⟩ := swift.rows_stored st c O Rt Cl y hy hst hrows
  iintro ⟨HO, Hm, #Hb⟩
  cases rk with
  | exec => ipureintro; exact Or.inr ⟨_, hR, (by decide), (by intro h; cases h)⟩
  | released => ipureintro; exact Or.inr ⟨_, hR, (by decide), (by intro h; cases h)⟩
  | rest d γi => ipureintro; exact Or.inr ⟨_, hR, (by intro h; cases h), (by intro h; cases h)⟩
  | empty =>
    ihave ⟨%rv, Htok, Hw, -⟩ := (BigSepM.bigSepM_lookup (Φ := fun K rk => swift.recBody γ γo sn K rk)
      (show PartialMap.get? Rt (c, y) = some .empty from hR)) $$ Hm
    simp only [swift.retWhy]
    icases Hw with %hw
    iunfold swift.rowTok at Htok
    ihave %hl := ghost_map_lookup $$ HO Htok
    have hl' : O.lookup (c, y) = some rv := hl
    rw [hO] at hl'
    exfalso
    exact hne (by rw [Option.some.inj hl', hw])
  | sync =>
    ihave #Hs := swift.recSync_in γ γo sn Rt (c, y) hR $$ Hm
    iunfold swift.syncIn at Hs
    icases Hs with ⟨%M', #HM', %hyM'⟩
    icases Hb with (%hb | ⟨%M, #HM, %hBM⟩)
    · ipureintro; exact Or.inr ⟨_, hR, by decide, fun _ => hb.1⟩
    · iunfold sp.syncIs at HM
      iunfold sp.syncIs at HM'
      ihave %he := ghostMapElem_agree c γ.sync _ _ M M' $$ HM HM'
      ipureintro
      left
      rw [hBM, he]
      exact hyM'

/-- `swift.rowsCover` for every command. -/
theorem swift.rowsCoverAll (γ : sp.Names) (γo : GName) (sn : swift.StN) (st : sp.RState)
    (c : Nat) (O : GMap (Nat × sp.CmdId) swift.RowV) (Rt : GMap (Nat × sp.CmdId) swift.RecK)
    (Cl : GMap (Nat × sp.CmdId) swift.ClK) (B : List sp.CmdId)
    (hst : swift.storeOk c O Rt ∅ Cl) (hrows : swift.rowsOk st O) :
    ghostMapAuth γo 1 O ∗ ([∗map] K ↦ rk ∈ Rt, swift.recBody γ γo sn K rk) ∗
      (⌜c = 0 ∧ B = []⌝ ∨ ∃ M : sp.SyncMsg, sp.syncIs γ c M ∗ ⌜B = sp.syncOrder M⌝) ⊢
      ⌜∀ y, swift.rowNE st c y →
        y ∈ B ∨ ∃ rk, Rt.lookup (c, y) = some rk ∧ rk ≠ .empty ∧ (rk = .sync → c = 0)⌝ := by
  refine (BI.forall_intro fun y => ?_).trans BI.pure_forall.2
  by_cases hy : swift.rowNE st c y
  · exact (swift.rowsCover γ γo sn st c O Rt Cl B y hy hst hrows).trans
      (BI.pure_mono fun p _ => p)
  · exact BI.pure_intro (fun h => absurd h hy)

/-- `delivInv` opens at the report's mask (outside `nodeN`). -/
theorem swift.delivN_node_sub : ↑swift.delivN ⊆ (⊤ \ ↑swift.nodeN : CoPset) := by
  have h : ↑swift.delivN ## (↑swift.nodeN : CoPset) := by
    unfold swift.delivN swift.nodeN
    exact ndot_ne_disjoint nroot (by decide)
  intro e he
  rw [LawfulSet.mem_diff]
  exact ⟨CoPset.mem_full, fun h' => h e ⟨he, h'⟩⟩

/-- **An `exec` record of `c` is a command of the execution record `X` of `c`** (round 51): its
`exIn` against the record's ghost map `γxm`, which is `X` at `c` (`delivOk`). -/
theorem swift.execRecs_in (γ : sp.Names) (γo : GName) (sn : swift.StN)
    (Rt : GMap (Nat × sp.CmdId) swift.RecK) (c : Nat) (X : List swift.ExE)
    (Mx : GMap (Nat × Nat) swift.ExE) (hMx : ∀ i, Mx.lookup (c, i) = X[i]?) {qa : Iris.Qp} :
    ([∗map] K ↦ rk ∈ Rt, swift.recBody γ γo sn K rk) ∗ ghostMapAuth sn.γxm qa Mx ⊢
      ⌜∀ y, Rt.lookup (c, y) = some .exec → y ∈ X.map (fun e => toCmdId e.1)⌝ := by
  refine (BI.forall_intro fun y => ?_).trans BI.pure_forall.2
  by_cases h : Rt.lookup (c, y) = some .exec
  · iintro ⟨Hm, Ha⟩
    ihave ⟨%rv, -, Hw, -⟩ := (BigSepM.bigSepM_lookup
      (Φ := fun K rk => swift.recBody γ γo sn K rk)
      (show PartialMap.get? Rt (c, y) = some .exec from h)) $$ Hm
    simp only [swift.retWhy]
    icases Hw with ⟨%x, %hx, Hin⟩
    iunfold swift.exIn at Hin
    icases Hin with ⟨%X0, %e, Hlb, %he⟩
    iunfold swift.exLb at Hlb
    ihave ⟨-, He'⟩ := (BigSepL.bigSepL_snoc (PROP := IProp netDistGF)).1 $$ Hlb
    iunfold swift.exAt at He'
    ihave %Hl := ghost_map_lookup $$ Ha He'
    ipureintro
    intro _
    have h1 := hMx X0.length
    rw [Hl] at h1
    have hmem : e ∈ X := List.mem_of_getElem? h1.symm
    exact List.mem_map.mpr ⟨e, hmem, by rw [he]; exact hx⟩
  · exact BI.pure_intro (fun h' => absurd h' h)

/-! ### Round 56 (D79 (1), 52-3): a rest record is read in the stopped view -/

instance swift.incSt_timelessE (γi : GName) (Mc : GMap GoString GoInterface)
    (r : GoString × Loc × Bool) : Timeless (swift.incSt γi Mc r) := by
  unfold swift.incSt; split <;> infer_instance

instance swift.incInv_timelessE (g : swift.DescG) (Mc : GMap GoString GoInterface) :
    Timeless (swift.incInv g Mc) := by
  unfold swift.incInv; infer_instance

theorem swift.incSt_liveE (γi : GName) (Mc : GMap GoString GoInterface) (r : GoString × Loc × Bool)
    (h : r.2.2 = true) :
    swift.incSt γi Mc r ⊢ ghostVar γi (1 : Iris.Qp).half (r.1, r.2.1) ∗
      ⌜Mc !! r.1 = some (interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #r.2.1)⌝ := by
  unfold swift.incSt; rw [if_pos h]

theorem swift.incSt_deadE (γi : GName) (Mc : GMap GoString GoInterface) (r : GoString × Loc × Bool)
    (h : r.2.2 = false) :
    swift.incSt γi Mc r ⊢ ghostVar γi (1 : Iris.Qp) (r.1, r.2.1) := by
  unfold swift.incSt; rw [if_neg (by simp [h])]

/-- **A rest record of the stopped ballot is a read** (round 56, D79 (1), 52-3; N1-R2 clause 2):
the record's incarnation `γi` is committed in the stopped epoch (`cgW` against `stopPS`'s `cgG`),
so `incInv` holds its other half live, at the record's key `str x` and descriptor `d`; the stopped
view has `d` there, so a read `r` of it exists (`hMc`), whose `propose` is the record's. With a
proposal, the read's command is `y` (its key fact, `str` injective). Without one, the row has
neither a pre-acceptance nor a path (`rowFacts`). -/
theorem swift.restRead (γ : sp.Names) (x : swift.RunX) (O : GMap (Nat × sp.CmdId) swift.RowV)
    (Rt : GMap (Nat × sp.CmdId) swift.RecK) (Mc : GMap GoString GoInterface)
    (SR : List swift.DescRead) (c : Nat) (y : sp.CmdId) (d : Loc) (γi : GName)
    (hR : Rt.lookup (c, y) = some (.rest d γi))
    (hMc : ∀ k v, Mc !! k = some v → ∃ r ∈ SR, r.k = k ∧
      v = interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #r.d)
    (hkey : ∀ r ∈ SR, r.p ≠ null → x.str (ofCmdId r.y) = r.k)
    (hinj : Function.Injective x.str) :
    ghostMapAuth x.γo 1 O ∗ ([∗map] K ↦ rk ∈ Rt, swift.recBody γ x.γo x.sn K rk) ∗
      (∃ g : swift.DescG, swift.incInv g Mc ∗ ⌜g.ev.b = c⌝ ∗ swift.cgG x g) ∗
      ([∗list] r ∈ SR, r.fields) ⊢
      ⌜(∃ r ∈ SR, r.p ≠ null ∧ r.y = y) ∨
        ∃ rv : swift.RowV, O.lookup (c, y) = some rv ∧ rv.1 = none ∧ rv.2.1 = none ∧
          rv.2.2.1 = false ∧ rv.2.2.2 = false⌝ := by
  iintro ⟨HO, Hm, ⟨%g, Hinc, %hgb, #Hcg⟩, Hf⟩
  ihave ⟨%rv, Htok, Hw, -⟩ := (BigSepM.bigSepM_lookup
    (Φ := fun K rk => swift.recBody γ x.γo x.sn K rk)
    (show PartialMap.get? Rt (c, y) = some (.rest d γi) from hR)) $$ Hm
  iunfold swift.rowTok at Htok
  ihave %hO := ghost_map_lookup $$ HO Htok
  simp only [swift.retWhy]
  icases Hw with ⟨%x', %dv, %hx', Hγi, -, -, Hp4, -, HrF, #HcgW⟩
  iunfold swift.rowFacts at HrF
  icases HrF with ⟨-, -, %hpp, -, -⟩
  by_cases hnull : dv.propose = null
  · ipureintro
    right
    refine ⟨rv, hO, ?_, ?_, ?_, ?_⟩
    · cases h : rv.1 with
      | none => rfl
      | some _ => exact absurd hnull (hpp (Or.inl (by rw [h]; rfl)))
    · cases h : rv.2.1 with
      | none => rfl
      | some _ => exact absurd hnull (hpp (Or.inr (Or.inl (by rw [h]; rfl))))
    -- round B1 (D81): an accepted or committed row's record has a proposal (`rowFacts`)
    · cases h : rv.2.2.1 with
      | false => rfl
      | true => exact absurd hnull (hpp (Or.inr (Or.inr (Or.inl h))))
    · cases h : rv.2.2.2 with
      | false => rfl
      | true => exact absurd hnull (hpp (Or.inr (Or.inr (Or.inr h))))
  -- the incarnation is committed in the stopped epoch `g`
  subst hgb
  ihave ⟨%γsg, #Hiw⟩ := swift.cgW_incW x g γi $$ [HcgW Hcg]
  · iframe Hcg; iexact HcgW
  iunfold swift.incInv at Hinc
  icases Hinc with ⟨%I, %Rf, HIa, HIs, -⟩
  iunfold swift.incW at Hiw
  ihave %hI := ghost_map_lookup $$ HIa Hiw
  ihave HSt := (BigSepM.bigSepM_lookup (Φ := fun γi' _ => swift.incSt γi' Mc (Rf γi'))
    (show PartialMap.get? I γi = some γsg from hI)) $$ HIs
  cases hl : (Rf γi).2.2 with
  | false =>
    ihave Hd := swift.incSt_deadE γi Mc (Rf γi) hl $$ HSt
    ihave %Hv := ghostVar_valid_2 γi _ _ _ _ $$ Hd Hγi
    exfalso
    have hq := Hv.1
    simp only [Iris.Qp.le_iff, Iris.Qp.val_add, Iris.Qp.val_one] at hq
    have := ((1 : Iris.Qp).half).2
    grind
  | true =>
    ihave ⟨Hl, %hMd⟩ := swift.incSt_liveE γi Mc (Rf γi) hl $$ HSt
    ihave %Hag := ghostVar_agree γi _ _ _ _ $$ Hl Hγi
    simp only [Prod.mk.injEq] at Hag
    obtain ⟨hk1, hk2⟩ := Hag
    rw [hk1, hk2] at hMd
    obtain ⟨r, hr, hrk, hrv⟩ := hMc _ _ hMd
    have hrd : d = r.d := swift.mkOk_desc_inj _ _ hrv
    subst hrd
    ihave ⟨Hr, -⟩ := (BigSepL.bigSepL_mem_acc hr) $$ Hf
    iunfold swift.DescRead.fields at Hr
    iunfold swift.descRepFields at Hr
    icases Hr with ⟨Fp, -⟩
    icombine Fp Hp4 gives %Hpe
    ipureintro
    left
    have hpn : r.p ≠ null := by rw [Hpe]; exact hnull
    refine ⟨r, hr, hpn, ?_⟩
    have h1 := (hkey r hr hpn).trans hrk
    have h2 : ofCmdId r.y = x' := hinj h1
    have hy' : toCmdId x' = y := hx'.1
    rw [← hy', ← h2, toCmdId_ofCmdId]

/-- `swift.restRead` for every command of the stopped ballot. -/
theorem swift.restReadAll (γ : sp.Names) (x : swift.RunX) (O : GMap (Nat × sp.CmdId) swift.RowV)
    (Rt : GMap (Nat × sp.CmdId) swift.RecK) (Mc : GMap GoString GoInterface)
    (SR : List swift.DescRead) (c : Nat)
    (hMc : ∀ k v, Mc !! k = some v → ∃ r ∈ SR, r.k = k ∧
      v = interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #r.d)
    (hkey : ∀ r ∈ SR, r.p ≠ null → x.str (ofCmdId r.y) = r.k)
    (hinj : Function.Injective x.str) :
    ghostMapAuth x.γo 1 O ∗ ([∗map] K ↦ rk ∈ Rt, swift.recBody γ x.γo x.sn K rk) ∗
      (∃ g : swift.DescG, swift.incInv g Mc ∗ ⌜g.ev.b = c⌝ ∗ swift.cgG x g) ∗
      ([∗list] r ∈ SR, r.fields) ⊢
      ⌜∀ y, (∃ d γi, Rt.lookup (c, y) = some (.rest d γi)) →
        (∃ r ∈ SR, r.p ≠ null ∧ r.y = y) ∨
        ∃ rv : swift.RowV, O.lookup (c, y) = some rv ∧ rv.1 = none ∧ rv.2.1 = none ∧
          rv.2.2.1 = false ∧ rv.2.2.2 = false⌝ := by
  refine (BI.forall_intro fun y => ?_).trans BI.pure_forall.2
  by_cases hy : ∃ d γi, Rt.lookup (c, y) = some (.rest d γi)
  · obtain ⟨d, γi, hR⟩ := hy
    exact (swift.restRead γ x O Rt Mc SR c y d γi hR hMc hkey hinj).trans
      (BI.pure_mono fun p _ => p)
  · exact BI.pure_intro (fun h => absurd h hy)

/-! ### Round 59 (D84 (2)): a read's own record, by its claim -/

/-- **A read's own record** (round 59, D84 (2); N1-R2 clause 1): a read with a proposal holds its
stored home's claim on the rest record of `(c, y)` (`swift.rdCl`), so the store has that record
(`storeOk`'s claims clause), whose token gives the row `rv` (`O`), and whose halves agree with the
read's fields (`phase`, `dep`, `propose`; `dep`'s contents by `stopFacts`): the record's
`rowPhaseOk` and `rowFacts`' `COMMIT` clause are at the read's values. -/
theorem swift.readRec (γ : sp.Names) (x : swift.RunX) (O : GMap (Nat × sp.CmdId) swift.RowV)
    (Rt : GMap (Nat × sp.CmdId) swift.RecK) (Out : GMap (Nat × sp.CmdId) (Nat × Iris.Qp))
    (Cl : GMap (Nat × sp.CmdId) swift.ClK) (c : Nat) (r : swift.DescRead)
    (hst : swift.storeOk c O Rt Out Cl) :
    ghostMapAuth x.γo 1 O ∗ ghostMapAuth x.sn.γcl 1 Cl ∗
      ([∗map] K ↦ rk ∈ Rt, swift.recBody γ x.γo x.sn K rk) ∗ r.fields ∗
      swift.rdCl x.sn.γcl c r ⊢
      ⌜r.p ≠ null → ∃ (dv : swift.DescV) (rv : swift.RowV), O.lookup (c, r.y) = some rv ∧
        swift.rowPhaseOk x.N x.r c dv rv ∧ dv.phase = r.ph ∧ dv.D = r.D ∧ dv.propose = r.p ∧
        (dv.phase = W64 3 → rv.2.2.2 = true ∨ dv.propose = null)⌝ := by
  iintro ⟨HO, Hc, Hm, Hf, Hcl⟩
  iunfold swift.rdCl at Hcl
  icases Hcl with (%Hn | ⟨%γi, Hcl⟩)
  · ipureintro; intro h; exact absurd Hn h
  iunfold swift.claimTok at Hcl
  ihave %Hl := ghost_map_lookup $$ Hc Hcl
  have hR : Rt.lookup (c, r.y) = some (swift.recOf (.rest r.d γi)) := hst.2.2.2.2 _ _ Hl
  ihave ⟨%rv, Htok, Hw, -⟩ := (BigSepM.bigSepM_lookup
    (Φ := fun K rk => swift.recBody γ x.γo x.sn K rk)
    (show PartialMap.get? Rt (c, r.y) = some (.rest r.d γi) from hR)) $$ Hm
  iunfold swift.rowTok at Htok
  ihave %hO := ghost_map_lookup $$ HO Htok
  simp only [swift.retWhy]
  icases Hw with ⟨%x', %dv, %hx', -, Hph, Hdep, Hp4, Hsf, HrF, -⟩
  iunfold swift.rowFacts at HrF
  icases HrF with ⟨-, -, -, -, %h3⟩
  iunfold swift.DescRead.fields at Hf
  iunfold swift.descRepFields at Hf
  icases Hf with ⟨Fp, Fph, -, Fdep, Fdl, -, -⟩
  icombine Fp Hp4 gives %Hpe
  icombine Fph Hph gives %Hphe
  icombine Fdep Hdep gives %Hde
  by_cases hpn : r.p = null
  · ipureintro; intro h; exact absurd hpn h
  have hdp : dv.propose ≠ null := by
    intro h; apply hpn; first | rw [Hpe]; exact h | rw [← Hpe]; exact h
  iunfold swift.stopFacts at Hsf
  icases Hsf with (%Hn | ⟨-, HD, -⟩)
  · exact absurd Hn hdp
  have hdd : r.dsl = dv.dep := by first | exact Hde | exact Hde.symm
  ihave #Fdl' : dv.dep ↦*□ r.D $$ [Fdl]
  · rw [← hdd]; iexact Fdl
  ihave %hDD := ownSlice_agree dv.dep _ _ dv.D r.D $$ HD [Fdl']
  · iexact Fdl'
  ipureintro
  intro _
  refine ⟨dv, rv, hO, hx'.2, ?_, hDD, ?_, h3⟩
  · first | exact Hphe | exact Hphe.symm
  · first | exact Hpe | exact Hpe.symm

/-- `swift.readRec` for every held read. -/
theorem swift.readRecAll (γ : sp.Names) (x : swift.RunX) (O : GMap (Nat × sp.CmdId) swift.RowV)
    (Rt : GMap (Nat × sp.CmdId) swift.RecK) (Out : GMap (Nat × sp.CmdId) (Nat × Iris.Qp))
    (Cl : GMap (Nat × sp.CmdId) swift.ClK) (c : Nat) (SR : List swift.DescRead)
    (hst : swift.storeOk c O Rt Out Cl) :
    ghostMapAuth x.γo 1 O ∗ ghostMapAuth x.sn.γcl 1 Cl ∗
      ([∗map] K ↦ rk ∈ Rt, swift.recBody γ x.γo x.sn K rk) ∗ ([∗list] r ∈ SR, r.fields) ∗
      ([∗list] r ∈ SR, swift.rdCl x.sn.γcl c r) ⊢
      ⌜∀ r ∈ SR, r.p ≠ null → ∃ (dv : swift.DescV) (rv : swift.RowV),
        O.lookup (c, r.y) = some rv ∧
        swift.rowPhaseOk x.N x.r c dv rv ∧ dv.phase = r.ph ∧ dv.D = r.D ∧ dv.propose = r.p ∧
        (dv.phase = W64 3 → rv.2.2.2 = true ∨ dv.propose = null)⌝ := by
  refine (BI.forall_intro fun r => ?_).trans BI.pure_forall.2
  refine (BI.forall_intro fun hr => ?_).trans BI.pure_forall.2
  iintro ⟨HO, Hc, Hm, Hf, Hcl⟩
  ihave ⟨Hr, -⟩ := (BigSepL.bigSepL_mem_acc hr) $$ Hf
  ihave ⟨Hrc, -⟩ := (BigSepL.bigSepL_mem_acc hr) $$ Hcl
  iapply (swift.readRec γ x O Rt Out Cl c r hst)
  iframe

/-- **Clause 1 for a read's entry** (round 59, D84 (2)): the read's own record at the read's
values (`swift.readRec`), its row the replica's (`rowsOk`, which also puts the command in `r`'s
sequence): `rowPhaseOk` is clause 1 at the entry. -/
theorem swift.readEnt1 (N r c : Nat) (st : sp.RState) (O : GMap (Nat × sp.CmdId) swift.RowV)
    (s : sp.Seq) (rd : swift.DescRead) (e : sp.RepEntry) (hrows : swift.rowsOk st O)
    (he : rd.entry = some e)
    (h : rd.p ≠ null → ∃ (dv : swift.DescV) (rv : swift.RowV), O.lookup (c, rd.y) = some rv ∧
        swift.rowPhaseOk N r c dv rv ∧ dv.phase = rd.ph ∧ dv.D = rd.D ∧ dv.propose = rd.p ∧
        (dv.phase = W64 3 → rv.2.2.2 = true ∨ dv.propose = null)) :
    e.id ∈ st.locAt c ∧ e.phase.toNat ≤ 3 ∧
      (e.phase.toNat ≥ 2 → (c, e.id) ∈ st.accR ∨ (c, e.id) ∈ st.comR) ∧
      (∀ D, st.preAt c e.id = some D → e.phase.toNat ≥ 2 ∨ (e.phase.toNat = 1 ∧ e.dep = D)) ∧
      ((c, e.id) ∈ st.accR ∨ (c, e.id) ∈ st.comR →
        e.phase.toNat ≥ 2 ∨ (r = sp.leaderOf N c ∧ e.phase.toNat ≥ 1)) ∧
      (e.phase.toNat = 0 → ∀ d ∈ e.dep, d ∈ sp.depsIn s e.id) := by
  have hp : rd.p ≠ null := by
    intro hn; unfold swift.DescRead.entry at he; rw [if_pos hn] at he; cases he
  unfold swift.DescRead.entry at he
  rw [if_neg hp] at he
  obtain rfl := (Option.some.inj he).symm
  obtain ⟨dv, rv, hO, hrp, hph, hD, hpe, h3⟩ := h hp
  have hrv := hrows c rd.y
  rw [hO] at hrv
  obtain ⟨hrv, hloc⟩ := hrv
  have hdp : dv.propose ≠ null := by rw [hpe]; exact hp
  obtain ⟨hle, h0, h1, h2, hpre, hac⟩ := hrp.2 hdp
  subst hrv
  simp only [swift.rowsOf, decide_eq_true_eq] at h1 h2 h3 hpre hac
  dsimp only
  rw [← hph, ← hD]
  have hle' : dv.phase.toNat ≤ 3 := hle
  refine ⟨hloc, hle', fun hge => ?_, fun D hD' => ?_, fun hx => hac hx, fun hz d hd => ?_⟩
  · rcases swift.ph_cases dv.phase hle with hq | hq | hq | hq
    · rw [hq] at hge; exact absurd hge (by decide)
    · rw [hq] at hge; exact absurd hge (by decide)
    · exact Or.inl (h2 hq)
    · rcases h3 hq with h | h
      · exact Or.inr h
      · exact absurd h hdp
  · have hs : (st.preAt c rd.y).isSome := by rw [hD']; rfl
    have h1le : 1 ≤ dv.phase.toNat := hpre hs
    rcases swift.ph_cases dv.phase hle with hq | hq | hq | hq
    · rw [hq] at h1le; exact absurd h1le (by decide)
    · right
      refine ⟨by rw [hq]; rfl, ?_⟩
      have := h1 hq
      rw [hD'] at this
      exact (Option.some.inj this).symm
    · left; rw [hq]; decide
    · left; rw [hq]; decide
  · have hq : dv.phase = W64 0 := by
      have : dv.phase.toNat = (W64 0).toNat := by rw [hz]; rfl
      exact BitVec.eq_of_toNat_eq this
    rw [(h0 hq).1] at hd
    cases hd

/-! ### Round 58 (D82 (1)): a home's incarnation and record, read in the stopped view -/

theorem swift.incSt_liveI (γi : GName) (Mc : GMap GoString GoInterface) (r : GoString × Loc × Bool)
    (h : r.2.2 = true) :
    ghostVar γi (1 : Iris.Qp).half (r.1, r.2.1) ∗
      ⌜Mc !! r.1 = some (interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #r.2.1)⌝ ⊢
      swift.incSt γi Mc r := by
  unfold swift.incSt; rw [if_pos h]

/-- **A committed incarnation's key in the stopped view** (round 58, D82 (1)): an incarnation `γi`
committed in the stopped epoch of ballot `c` (`cgW` against `stopPS`'s `cgG`), whose half is held
at `(kk, d)`, is live there (a dead one has `γi` whole), so the stopped view has `kk ↦ d`. -/
theorem swift.incKey (x : swift.RunX) (Mc : GMap GoString GoInterface) (c : Nat) (γi : GName)
    (kk : GoString) (d : Loc) (E : CoPset) :
    (▷ ∃ g : swift.DescG, swift.incInv g Mc ∗ ⌜g.ev.b = c⌝ ∗ swift.cgG x g) ∗
      ghostVar γi (1 : Iris.Qp).half (kk, d) ∗ swift.cgW x.γcg c γi ⊢
      |={E}=> (▷ ∃ g : swift.DescG, swift.incInv g Mc ∗ ⌜g.ev.b = c⌝ ∗ swift.cgG x g) ∗
        ghostVar γi (1 : Iris.Qp).half (kk, d) ∗
        ⌜Mc !! kk = some (interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #d)⌝ := by
  iintro ⟨HPS, Hgv, #HcgW⟩
  imod HPS
  icases HPS with ⟨%g, Hinc, %hgb, #Hcg⟩
  subst hgb
  ihave ⟨%γsg, #Hiw⟩ := swift.cgW_incW x g γi $$ [HcgW Hcg]
  · iframe Hcg; iexact HcgW
  iunfold swift.incInv at Hinc
  icases Hinc with ⟨%I, %Rf, HIa, HIs, %HI1⟩
  ihave #Hiw2 := Hiw
  iunfold swift.incW at Hiw2
  ihave %hI := ghost_map_lookup $$ HIa Hiw2
  icases (BigSepM.bigSepM_delete (Φ := fun γi' _ => swift.incSt γi' Mc (Rf γi'))
    (show PartialMap.get? I γi = some γsg from hI)).1 $$ HIs with ⟨HSt, HIs⟩
  cases hl : (Rf γi).2.2 with
  | false =>
    ihave Hd := swift.incSt_deadE γi Mc (Rf γi) hl $$ HSt
    ihave %Hv := ghostVar_valid_2 γi _ _ _ _ $$ Hd Hgv
    exfalso
    have hq := Hv.1
    simp only [Iris.Qp.le_iff, Iris.Qp.val_add, Iris.Qp.val_one] at hq
    have := ((1 : Iris.Qp).half).2
    grind
  | true =>
    ihave ⟨Hl, %hMd⟩ := swift.incSt_liveE γi Mc (Rf γi) hl $$ HSt
    ihave %Hag := ghostVar_agree γi _ _ _ _ $$ Hl Hgv
    simp only [Prod.mk.injEq] at Hag
    obtain ⟨hk1, hk2⟩ := Hag
    have hMk := hMd
    rw [hk1, hk2] at hMk
    imodintro
    iframe Hgv
    isplitl [Hl HIa HIs]
    · inext
      iexists g
      iframe Hcg
      isplitl [Hl HIa HIs]
      · iunfold swift.incInv
        iexists I, Rf
        iframe HIa
        isplitl [Hl HIs]
        · iapply (BigSepM.bigSepM_delete (Φ := fun γi' _ => swift.incSt γi' Mc (Rf γi'))
            (show PartialMap.get? I γi = some γsg from hI)).2
          iframe HIs
          iapply swift.incSt_liveI γi Mc (Rf γi) hl
          iframe Hl; ipureintro; exact hMd
        ipureintro; exact HI1
      ipureintro; rfl
    ipureintro; exact hMk

/-- **A stored home's record, read** (round 58, D82 (1), (4)): the home's claim on its rest record
of the stopped ballot `c` gives (inside one opening of the node invariant) the record's command
`x'`, values `dv` and row `rv`: its half fields agree with the home's (`phase`, `dep`, `propose`),
its incarnation is live in the stopped view at `x'`'s key (`swift.incKey`), and its persistent
facts (`stopFacts`, `rowFacts`, `rowPhaseOk`). -/
theorem swift.claimRead (γ : sp.Names) (x : swift.RunX) (Mc : GMap GoString GoInterface)
    (K : Nat × sp.CmdId) (d : Loc) (γi : GName) (ph : w64) (dep : GoSlice) (p : Loc) :
    inv swift.nodeN (swift.nodeInvD γ x.γv x.γe x.γo x.sn x.k) ∗
      swift.claimTok x.sn.γcl K (.rest d γi) ∗
      typedPointsto (swift.dfld d go!"phase") ph (DFrac.own (1 : Iris.Qp).half) ∗
      typedPointsto (swift.dfld d go!"dep") dep (DFrac.own (1 : Iris.Qp).half) ∗
      typedPointsto (swift.dfld d go!"propose") p (DFrac.own (1 : Iris.Qp).half.half) ∗
      (▷ ∃ g : swift.DescG, swift.incInv g Mc ∗ ⌜g.ev.b = K.1⌝ ∗ swift.cgG x g) ⊢
    |={⊤}=> swift.claimTok x.sn.γcl K (.rest d γi) ∗
      typedPointsto (swift.dfld d go!"phase") ph (DFrac.own (1 : Iris.Qp).half) ∗
      typedPointsto (swift.dfld d go!"dep") dep (DFrac.own (1 : Iris.Qp).half) ∗
      typedPointsto (swift.dfld d go!"propose") p (DFrac.own (1 : Iris.Qp).half.half) ∗
      (▷ ∃ g : swift.DescG, swift.incInv g Mc ∗ ⌜g.ev.b = K.1⌝ ∗ swift.cgG x g) ∗
      ∃ (x' : swift.CommandId) (dv : swift.DescV) (rv : swift.RowV),
        ⌜toCmdId x' = K.2 ∧ swift.rowPhaseOk x.N x.r K.1 dv rv ∧ dv.phase = ph ∧ dv.dep = dep ∧
          dv.propose = p ∧
          Mc !! x.str x' = some (interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #d)⌝ ∗
        swift.stopFacts γ x.γxm x.N x.r K.1 x' dv ∗ swift.rowFacts γ x.r K.1 x' dv rv := by
  iintro ⟨#HN, Hcl, Hph, Hdep, Hp, HPS⟩
  iinv HN with Hn Hclose
  iunfold swift.nodeInvD at Hn
  imod Hn
  icases Hn with ⟨%st, %O, Hstn, Hw2, He, HO, HS, HX, %Hacc, %Hok⟩
  iunfold swift.storeD at HS
  icases HS with ⟨%Rt, %Out, %Cl, %U, Ha, Hc, Hm, Hu, %h, %hU⟩
  iunfold swift.claimTok at Hcl
  ihave %Hl := ghost_map_lookup $$ Hc Hcl
  have hR : Rt.lookup K = some (swift.recOf (.rest d γi)) := h.2.2.2.2 K _ Hl
  icases (BigSepM.bigSepM_delete (Φ := fun (K : Nat × sp.CmdId) (rk : swift.RecK) =>
      iprop(∃ rv : swift.RowV, swift.rowTok x.γo K.1 K.2 rv ∗
        swift.retWhy γ x.sn.γxm x.sn.γcg x.sn.str x.sn.N x.sn.r K rv rk ∗
        swift.tixOr x.sn.γxu x.sn.γxm K))
      (show PartialMap.get? Rt K = some (swift.recOf (.rest d γi)) from hR)).1 $$ Hm
    with ⟨⟨%rv, Htok, Hw, Htx⟩, Hm⟩
  isimp only [swift.recOf, swift.retWhy] at Hw
  icases Hw with ⟨%x', %dv, %Hx, Hγi, Hph', Hdep', Hp', #Hsf, #Hrf, #Hcg⟩
  icombine Hph Hph' gives %Hphe
  icombine Hdep Hdep' gives %Hdepe
  icombine Hp Hp' gives %Hpe
  imod swift.incKey x Mc K.1 γi (x.sn.str x') d (⊤ \ ↑swift.nodeN) $$ [HPS Hγi Hcg] with
    ⟨HPS, Hγi, %hMk⟩
  · iframe HPS Hγi; iexact Hcg
  imod Hclose $$ [Hstn Hw2 He HO HX Ha Hc Hm Hu Htok Htx Hγi Hph' Hdep' Hp'] with -
  · inext
    iunfold swift.nodeInvD
    iexists st, O
    iframe Hstn Hw2 He HO HX
    isplitl [Ha Hc Hm Hu Htok Htx Hγi Hph' Hdep' Hp']
    · iunfold swift.storeD
      iexists Rt, Out, Cl, U
      iframe Ha Hc Hu
      isplitl [Hm Htok Htx Hγi Hph' Hdep' Hp']
      · iapply (BigSepM.bigSepM_delete (Φ := fun (K : Nat × sp.CmdId) (rk : swift.RecK) =>
          iprop(∃ rv : swift.RowV, swift.rowTok x.γo K.1 K.2 rv ∗
            swift.retWhy γ x.sn.γxm x.sn.γcg x.sn.str x.sn.N x.sn.r K rv rk ∗
            swift.tixOr x.sn.γxu x.sn.γxm K))
          (show PartialMap.get? Rt K = some (swift.recOf (.rest d γi)) from hR)).2
        iframe Hm
        iexists rv
        iframe Htok Htx
        isimp only [swift.recOf, swift.retWhy]
        iexists x', dv
        iframe Hγi Hph' Hdep' Hp' Hsf Hrf Hcg
        ipureintro; exact Hx
      ipureintro; exact ⟨h, hU⟩
    ipureintro; exact ⟨Hacc, Hok⟩
  imodintro
  isplitl [Hcl]
  · iunfold swift.claimTok; iexact Hcl
  iframe Hph Hdep Hp HPS
  iexists x', dv, rv
  iframe Hsf Hrf
  ipureintro
  refine ⟨Hx.1, Hx.2, ?_, ?_, ?_, hMk⟩
  · first | exact Hphe | exact Hphe.symm
  · first | exact Hdepe | exact Hdepe.symm
  · first | exact Hpe | exact Hpe.symm

end store

/-! ## N1-R1 and N1-R2 (round 51, D70 (1): frame lemmas) -/

section reqs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions]

/-- **The frozen execution record** (N1-R1's `Fz`; round 52, D71 (1), lifecycle-table 11b.11
T20z/T23z): a quarter of the record's variable `γx` at `(c, X)` and half of the record's map
authority `γxm`, taken out of `delivInv`'s frozen-mode slot `swift.delivFz` (Deliver.lean) by
`freeze` for the run loop's half of the pins' variable `γxp`, given back by `thaw`. While it is
held, `γx` is `execL`'s ½, `delivInv`'s ¼ and this ¼, so no append to `X` and no reset is
possible, and a `deliver` (its pin) refutes the mode. -/
def swift.fzX (x : swift.RunX) (c : Nat) (X : List swift.ExE) : IProp netDistGF :=
  iprop(ghostVar x.γx (1 : Iris.Qp).half.half (c, X) ∗
    ∃ Mx : GMap (Nat × Nat) swift.ExE, ghostMapAuth x.γxm (1 : Iris.Qp).half Mx)

/-- `delivInv`'s invariant from the descriptors' context. -/
theorem swift.descCtxX_deliv (γ : sp.Names) (γc γm : GName) (x : swift.RunX) (rp : Loc) :
    swift.descCtxX γ γc γm x rp ⊢ ∃ γa γrm : GName,
      inv swift.delivN (swift.delivInv γ x.N x.r x.γdl x.γx x.γxp x.γxm γa x.γxe γrm x.str) := by
  iintro #Hctx
  iunfold swift.descCtxX at Hctx
  iunfold swift.descCtxE at Hctx
  icases Hctx with ⟨%me, %fr, %lg, %dm, %dc, %ex, %dr, %oe, %γa, %γrm, %rc0, %γrc, -, -,
    -, -, -, -, -, -, -, -, -, #HdI, -⟩
  iexists γa, γrm
  iexact HdI

/-- **The freeze** (round 52, D71 (1); T20z at `fillNewLeaderAckN`'s start): the run loop's half
of the pins' variable at `c` goes into `delivInv`'s frozen slot; `Fz c X` comes out. Removal mode
(`γxp` whole) and the frozen mode (the slot's half) are refuted by the run loop's half, and its
agreement gives the record's epoch `c`. -/
theorem swift.fz_freeze (γ : sp.Names) (γc γm : GName) (x : swift.RunX) (rp : Loc) (c : Nat) :
    swift.descCtxX γ γc γm x rp ∗ ghostVar x.γxp (1 : Iris.Qp).half c ⊢
      |={⊤}=> ∃ X : List swift.ExE, swift.fzX x c X := by
  iintro ⟨#Hctx, Hp⟩
  ihave ⟨%γa, %γrm, #HdI⟩ := swift.descCtxX_deliv γ γc γm x rp $$ Hctx
  iinv HdI with Hi Hclose
  iunfold swift.delivInv at Hi
  imod Hi
  icases Hi with ⟨%M, %bX, %X, %Mx, %rm, HV, HXi, HXp, HMx, ⟨HXx, HFz⟩, %HM⟩
  ihave ⟨Hp, HXp, %Hrm⟩ := swift.epochPinQ_agree x.γxp (1 : Iris.Qp).half c bX rm $$ [Hp HXp]
  · iunfold swift.epochPinQ; iframe
  obtain ⟨hrm, hb⟩ := Hrm
  subst hrm
  subst bX
  iunfold swift.delivFz at HFz
  icases HFz with ⟨#Hlb, (⟨Hx2, HM2⟩ | Hp2)⟩
  · imod Hclose $$ [HV HXi HXp HMx HXx Hp] with -
    · inext
      iunfold swift.delivInv
      iexists M, c, X, Mx, false
      iframe HV HXi HXp HMx
      isplitl [HXx Hp]
      · iframe HXx
        iunfold swift.delivFz
        iframe Hlb
        iright; iunfold swift.epochPinQ at Hp; iexact Hp
      ipureintro; exact HM
    imodintro
    iexists X
    iunfold swift.fzX
    iframe Hx2
    iexists Mx
    iexact HM2
  · iexfalso
    iapply swift.pin_noFz x.γxp (1 : Iris.Qp).half c c false
    iframe

/-- **The thaw** (round 52, D71 (1); T23z at `fillNewLeaderAckN`'s end): `Fz c X` goes back into
`delivInv`'s slot and the run loop's half of the pins' variable at `c` comes out. `Fz`'s half of
`γxm` refutes the slot's unfrozen branch, removal mode is refuted by the slot's `γxp` half, and
`Fz`'s quarter of `γx` gives the record's epoch `c`. -/
theorem swift.fz_thaw (γ : sp.Names) (γc γm : GName) (x : swift.RunX) (rp : Loc) (c : Nat)
    (X : List swift.ExE) :
    swift.descCtxX γ γc γm x rp ∗ swift.fzX x c X ⊢
      |={⊤}=> ghostVar x.γxp (1 : Iris.Qp).half c := by
  iintro ⟨#Hctx, HF⟩
  ihave ⟨%γa, %γrm, #HdI⟩ := swift.descCtxX_deliv γ γc γm x rp $$ Hctx
  iunfold swift.fzX at HF
  icases HF with ⟨Hq, %Mx0, HM0⟩
  iinv HdI with Hi Hclose
  iunfold swift.delivInv at Hi
  imod Hi
  icases Hi with ⟨%M, %bX, %X', %Mx, %rm, HV, HXi, HXp, HMx, ⟨HXx, HFz⟩, %HM⟩
  ihave %Hag := ghostVar_agree x.γx (bX, X') (1 : Iris.Qp).half.half (c, X)
    (1 : Iris.Qp).half.half $$ HXi Hq
  simp only [Prod.mk.injEq] at Hag
  obtain ⟨hb, hX⟩ := Hag
  subst bX
  subst X'
  ihave %HagM := ghostMapAuth_agree x.γxm _ _ Mx Mx0 $$ HMx HM0
  subst Mx0
  iunfold swift.delivFz at HFz
  icases HFz with ⟨#Hlb, (⟨Hx2, HM2⟩ | Hp2)⟩
  · iexfalso
    ihave H1 := (ghostMapAuth_halves x.γxm Mx).2 $$ [HMx HM2]
    · iframe
    ihave %Hv := ghostMapAuth_valid_2 x.γxm 1 (1 : Iris.Qp).half Mx Mx $$ H1 HM0
    exfalso
    have hq := Hv.1
    simp only [Iris.Qp.le_iff, Iris.Qp.val_add, Iris.Qp.val_one] at hq
    have := ((1 : Iris.Qp).half).2
    grind
  cases rm with
  | true =>
    iexfalso
    iapply swift.rm_noFz x.γxp c
    iframe
  | false =>
    imod Hclose $$ [HV HXi HXp HMx HXx Hq HM0] with -
    · inext
      iunfold swift.delivInv
      iexists M, c, X, Mx, false
      iframe HV HXi HXp HMx
      isplitl [HXx Hq HM0]
      · iframe HXx
        iunfold swift.delivFz
        iframe Hlb
        ileft; iframe
      ipureintro; exact HM
    imodintro
    iexact Hp2

/-- **An executed command of the frozen epoch is the record's** (round 58, D82 (4)): `exIn` of the
frozen ballot `c` against `delivInv`'s map `γxm`, which is `X` at `c` (`Fz`'s quarter of `γx`). -/
theorem swift.fz_exIn (γ : sp.Names) (γc γm : GName) (x : swift.RunX) (rp : Loc) (c : Nat)
    (X : List swift.ExE) (x' : swift.CommandId) :
    swift.descCtxX γ γc γm x rp ∗ swift.fzX x c X ∗ swift.exIn x.γxm c x' ⊢
      |={⊤}=> swift.fzX x c X ∗ ⌜toCmdId x' ∈ X.map (fun e => toCmdId e.1)⌝ := by
  iintro ⟨#Hctx, HF, #Hin⟩
  ihave ⟨%γa, %γrm, #HdI⟩ := swift.descCtxX_deliv γ γc γm x rp $$ Hctx
  iunfold swift.fzX at HF
  icases HF with ⟨Hq, %Mx0, HM0⟩
  iinv HdI with Hi Hclose
  iunfold swift.delivInv at Hi
  imod Hi
  icases Hi with ⟨%M, %bX, %X', %Mx, %rm, HV, HXi, HXp, HMx, HXx, %HM⟩
  ihave %Hag := ghostVar_agree x.γx (bX, X') (1 : Iris.Qp).half.half (c, X)
    (1 : Iris.Qp).half.half $$ HXi Hq
  simp only [Prod.mk.injEq] at Hag
  obtain ⟨rfl, rfl⟩ := Hag
  iunfold swift.exIn at Hin
  icases Hin with ⟨%X0, %e, Hlb, %he⟩
  iunfold swift.exLb at Hlb
  ihave ⟨-, He'⟩ := (BigSepL.bigSepL_snoc (PROP := IProp netDistGF)).1 $$ Hlb
  iunfold swift.exAt at He'
  ihave %Hlk := ghost_map_lookup $$ HMx He'
  imod Hclose $$ [HV HXi HXp HMx HXx] with -
  · inext
    iunfold swift.delivInv
    iexists M, bX, X', Mx, rm
    iframe
    ipureintro; exact HM
  imodintro
  isplitl [Hq HM0]
  · iunfold swift.fzX
    iframe Hq
    iexists Mx0; iexact HM0
  ipureintro
  have h1 := HM.2.2.1 X0.length
  rw [Hlk] at h1
  have hmem : e ∈ X' := List.mem_of_getElem? h1.symm
  exact List.mem_map.mpr ⟨e, hmem, by rw [he]⟩

/-- **A `proposeDep`'s facts** (N1-R1's `Wd`): the replica's sequence of `c` has `z`, and the
dependencies are of `depsIn` there. Round 55 (D76 (3)): and they are fewer than `2^62` (its
writer's `propDepOk`). -/
def swift.pdW (γ : sp.Names) (x : swift.RunX) (c : Nat) (z : sp.CmdId) (D : List sp.CmdId) :
    IProp netDistGF :=
  iprop(∃ s' : sp.Seq, sp.locLb γ x.r c s' ∗
    ⌜z ∈ s'.map Prod.fst ∧ (∀ d ∈ D, d ∈ sp.depsIn s' z) ∧ D.length < 2 ^ 62⌝)

instance swift.pdW_persistent (γ : sp.Names) (x : swift.RunX) (c : Nat) (z : sp.CmdId)
    (D : List sp.CmdId) : Persistent (swift.pdW γ x c z D) := by
  unfold swift.pdW sp.locLb; infer_instance

/-- Two lists agreeing at every index both have are prefix-comparable. -/
theorem swift.prefix_cmp_of_agree {A : Type} (s s' : List A)
    (h : ∀ (i : Nat) (a a' : A), s[i]? = some a → s'[i]? = some a' → a = a') :
    s <+: s' ∨ s' <+: s := by
  have key : ∀ (l1 l2 : List A), (∀ (i : Nat) (a a' : A), l1[i]? = some a → l2[i]? = some a' → a = a') →
      l1.length ≤ l2.length → l1 <+: l2 := by
    intro l1 l2 hag hle
    rw [List.prefix_iff_eq_take]
    apply List.ext_getElem?
    intro i
    rw [List.getElem?_take]
    by_cases hi : i < l1.length
    · rw [if_pos hi]
      obtain ⟨a, ha⟩ : ∃ a, l1[i]? = some a := ⟨_, List.getElem?_eq_getElem hi⟩
      obtain ⟨a', ha'⟩ : ∃ a', l2[i]? = some a' :=
        ⟨_, List.getElem?_eq_getElem (Nat.lt_of_lt_of_le hi hle)⟩
      rw [ha, ha', hag i a a' ha ha']
    · rw [if_neg hi, List.getElem?_eq_none (by omega)]
  by_cases hl : s.length ≤ s'.length
  · exact Or.inl (key s s' h hl)
  · exact Or.inr (key s' s (fun i a a' h1 h2 => (h i a' a h2 h1).symm) (by omega))

/-- **Two `locLb`s of one sequence are prefix-comparable** (round 55, for N6 (3)): both are read
against `sp.inv`'s authorities of the sequences' ids and commands (`sp.locLb_lookups`). -/
theorem swift.locLb_cmp (γ : sp.Names) (γc γm γl : GName) (E : CoPset) (hE : ↑sp.spN ⊆ E)
    (L b : Nat) (s s' : sp.Seq) :
    sp.inv γ γc γm γl ∗ sp.locLb γ L b s ∗ sp.locLb γ L b s' ⊢ |={E}=> ⌜s <+: s' ∨ s' <+: s⌝ := by
  unfold sp.inv
  iintro ⟨#Hinv, #Hlb, #Hlb'⟩
  iapply (fupd_mask_mono hE)
  iinv Hinv with Hi Hclose
  unfold sp.invBody
  icases Hi with ⟨%S, %mC, %mL, %mS, %mA, %mP, %mCo, %mR, %mN, %sh, %mD, %mQ, %mK, %mPa, >HC, >HL, HS,
    HA, HP, HCo, HRp, HN, HH, HD, Hown, HQ, HK, HPa, >%Hrepr, Hnodes, >Hproto, HQs, >%Hcl, >%HDom,
    Hcmds, Hconns⟩
  ihave %Hlk := sp.locLb_lookups (γ := γ) _ _ s mL mC $$ [HL HC Hlb]
  · iframe HL HC Hlb
  ihave %Hlk' := sp.locLb_lookups (γ := γ) _ _ s' mL mC $$ [HL HC Hlb']
  · iframe HL HC Hlb'
  imod Hclose $$ [HC HL HS HA HP HCo HRp HN HH HD Hown HQ HK HPa Hnodes Hproto HQs Hcmds Hconns]
    with -
  · inext
    iexists S, mC, mL, mS, mA, mP, mCo, mR, mN, sh, mD, mQ, mK, mPa
    iframe
    isplitr
    · ipureintro; exact Hrepr
    ipureintro; exact ⟨Hcl, HDom⟩
  imodintro
  ipureintro
  apply swift.prefix_cmp_of_agree
  intro i a a' h1 h2
  obtain ⟨e1, e2⟩ := Hlk i a h1
  obtain ⟨e1', e2'⟩ := Hlk' i a' h2
  rw [e1] at e1'
  have h1 : a.1 = a'.1 := Option.some.inj e1'
  rw [← h1, e2] at e2'
  have h2 : a.2 = a'.2 := Option.some.inj e2'
  exact Prod.ext h1 h2

/-- **The `proposeDep`s are of the full sequence's dependencies** (round 53, N1-R2's clause 4):
each `pdW` names a `locLb` `s'` of the replica's sequence of `c` with `z` and `D ⊆ depsIn s' z`;
with `s` the whole sequence (`s.map Prod.fst = st.locAt c`), `s'` is a prefix of `s`
(`sp.locLb_prefix`, read through `sp.node_step` without a change), so `depsIn s' z = depsIn s z`. -/
theorem swift.pd_deps (γ : sp.Names) (γc γm γl : GName) (x : swift.RunX) (E : CoPset)
    (hE : ↑sp.spN ⊆ E) (fr : Bool) (l : List GoString) (st : sp.RState) (c : Nat) (s : sp.Seq)
    (Pd : List (sp.CmdId × List sp.CmdId)) (hr : x.r < x.N) (hk : nodeOf l x.r = some x.k)
    (hs : s.map Prod.fst = st.locAt c) :
    sp.inv γ γc γm γl ∗ sp.cfg γc γm x.N fr l ∗ sp.nodeSt γ x.k (1 : Iris.Qp).half st ∗
      sp.locLb γ x.r c s ∗ ([∗list] p ∈ Pd, swift.pdW γ x c p.1 p.2) ⊢
      |={E}=> sp.nodeSt γ x.k (1 : Iris.Qp).half st ∗
        ⌜∀ p ∈ Pd, ∀ d ∈ p.2, d ∈ sp.depsIn s p.1⌝ := by
  iintro ⟨#Hinv, #Hcfg, Hst, #Hlb, #Hpd⟩
  imod sp.node_step E hE x.N fr l x.r x.k st none
    (fun s0 => iprop(⌜s0 = st ∧ ∀ p ∈ Pd, ∀ d ∈ p.2, d ∈ sp.depsIn s p.1⌝)) hr hk $$ [Hst]
    with ⟨%st', Hst, -, %Heq⟩
  · iframe Hinv Hcfg Hst
    isplitl []
    · iunfold sp.predPre; itrivial
    unfold sp.stepUpd
    iintro %S %mC %mL %mS %mA %mP %mCo %mR %mPa %HH HC HL HS HA HP HCo HRp HPa
    obtain ⟨HI, Hsr, Hrs, Hrepr⟩ := HH
    ihave %Hlk := sp.locLb_lookups (γ := γ) _ _ s mL mC $$ [HL HC Hlb]
    · iframe HL HC Hlb
    have h1 := (sp.locLb_prefix HI Hrepr Hlk).2
    have hloc : S.loc x.r c = s.map Prod.fst := by
      rw [(HI.rows_ok x.r c).1, Hrs, hs]
    have hlen : (S.seqOf (S.loc x.r c)).length ≤ s.length := by
      rw [hloc]; unfold sp.PState.seqOf
      exact Nat.le_trans (List.length_filterMap_le _ _) (by simp)
    have heq : s = S.seqOf (S.loc x.r c) :=
      h1.eq_of_length (Nat.le_antisymm h1.length_le hlen)
    ihave %Hall := sp.bigSepL_gather iprop(ghostMapAuth γ.loc 1 mL ∗ ghostMapAuth γ.cmds 1 mC)
      (fun p => swift.pdW γ x c p.1 p.2) (fun p => ∀ d ∈ p.2, d ∈ sp.depsIn s p.1) Pd
      (fun p _ => by
        iintro ⟨⟨HL, HC⟩, #Hp⟩
        iunfold swift.pdW at Hp
        icases Hp with ⟨%s', #Hlb', %Hz⟩
        ihave %Hlk' := sp.locLb_lookups (γ := γ) _ _ s' mL mC $$ [HL HC Hlb']
        · iframe HL HC Hlb'
        ipureintro
        have h2 := (sp.locLb_prefix HI Hrepr Hlk').2
        rw [← heq] at h2
        obtain ⟨u, hu⟩ := h2
        intro d hd
        rw [← hu, sp.depsIn_append_of_mem s' u p.1 Hz.1]
        exact Hz.2.1 d hd) $$ [HL HC Hpd]
    · iframe HL HC Hpd
    imodintro
    iexists S, mL, mS, mA, mP, mCo, mR, mPa
    iframe
    isplitr
    · ipureintro; exact ⟨HI, Hsr, Hrepr, rfl, rfl, sp.PState.le_refl S, fun _ _ => rfl, rfl⟩
    ipureintro; exact ⟨Hrs, Hall⟩
  obtain ⟨rfl, hp⟩ := Heq
  imodintro
  iframe Hst
  ipureintro; exact hp

/-- **`pdOk` → `pdW`** (round 58, D82 (2)): a `proposeDep`'s writer's facts give its facts at the
report. A proposal's (`propFacts`): the replica's prefix `s` with `y` last, its dependencies
`lkDeps` before it, i.e. `depsIn s y` (`swift.propFacts_pre`), fewer than `2^62` (`s`'s ids are
registered and distinct, `swift.locLb_small`, `swift.small_ids_len`). A sync entry's (round 58,
HandleSyncEntry): the replica's prefix `syncSeq M` with `y` and the dependencies of `depsIn`. -/
theorem swift.pdOk_pdW (γ : sp.Names) (γc γm γl : GName) (E : CoPset) (hE : ↑sp.spN ⊆ E)
    (x : swift.RunX) (c0 : swift.DC) (b : Nat) (y : swift.CommandId) (pd hs : GoSlice) (sq : w64)
    (hc0 : c0.γ = γ ∧ c0.r = x.r) :
    sp.inv γ γc γm γl ∗ swift.pdOk c0 b y pd hs sq ⊢
      |={E}=> ⌜pd = slice.nil⌝ ∨
        ∃ D : List sp.CmdId, pd ↦*□ (D.map ofCmdId) ∗ swift.pdW γ x b (toCmdId y) D := by
  obtain ⟨h1, h3⟩ := hc0
  subst h1
  iintro ⟨#Hinv, #Hok⟩
  iunfold swift.pdOk at Hok
  icases Hok with (⟨%Hn, -⟩ | ⟨%cc, %ld, %s, %B, %D, %P, %H, -, #HD, -, #Hf, -⟩ |
    ⟨%D, -, #HD, -, %M, -, #HlbM, %HM⟩)
  · imodintro; ileft; ipureintro; exact Hn
  · iunfold swift.propFacts at Hf
    icases Hf with ⟨#Hlb, -, -, %Hs⟩
    ihave Hsm := swift.locLb_small (γ := c0.γ) (γc := γc) (γm := γm) (γl := γl) c0.r b s
      $$ [Hinv Hlb]
    · iframe Hinv Hlb
    imod (fupd_mask_mono (E1 := ↑sp.spN) (E2 := E) hE) $$ Hsm with %Hsm
    obtain ⟨hmem, hD, -⟩ := swift.propFacts_pre s B D P (toCmdId y) cc ld c0.N c0.r b Hs.1 Hs.2.1
      Hs.2.2.1 Hs.2.2.2.1 Hs.2.2.2.2.1 Hs.2.2.2.2.2.1 Hs.2.2.2.2.2.2.1 Hs.2.2.2.2.2.2.2.1
    have hlen : s.length ≤ 6 * 2 ^ 32 := by
      have := swift.small_ids_len (s.map Prod.fst) Hs.2.2.2.2.2.2.2.2
        (by intro z hz; obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hz; exact Hsm q hq)
      simpa using this
    have hDl : D.length ≤ s.length := by
      rw [Hs.2.2.1]
      have h1 := swift.lkDeps_len s.dropLast cc
      have h2 : s.dropLast.length ≤ s.length := by simp
      omega
    imodintro
    iright
    iexists D
    iframe HD
    iunfold swift.pdW
    iexists s
    rw [← h3]
    iframe Hlb
    ipureintro
    refine ⟨hmem, fun d hd => by rw [← hD]; exact hd, by omega⟩
  · imodintro
    iright
    iexists D
    iframe HD
    iunfold swift.pdW
    iexists sp.syncSeq M
    rw [← h3]
    iframe HlbM
    ipureintro; exact HM

/-- An execution-log entry's report entry: the record's command and dependencies, the log's
phase. -/
def swift.xsEnt (p : swift.ExE × swift.commandStaticDesc) : sp.RepEntry :=
  ⟨toCmdId p.1.1, p.2.phase', p.1.2.1, p.1.2.2.map toCmdId⟩

/-- **A follower's executed entry's leader prefix** (round 54, D74 (2)-(3); 49-4, 52-1, 53-1..53-4):
at a follower (`r` not `c`'s leader) the report's witness (`repEntW`, `upd_report`) asks for the
leader's sequence `locLb (leaderOf N c) c s'` with `y` and its executed dependencies `depsIn s' y`.
The record's entry carries it (`exEntOkE`'s `exFolW`, from the descriptor's `depWhy` at `COMMIT`,
T15): the leader's `locDeps` (its fast ack's, Inv.lean round 53, adopted by `fastAckFromLeader` or
kept as a permutation, 53-2; or a sync entry's leader `locLb` of `syncSeq M`, 53-4). -/
theorem swift.exec_wit_follower (γ : sp.Names) (N r c : Nat) (e : swift.ExE)
    (hl : r ≠ sp.leaderOf N c) :
    swift.exFolW γ N r c e ⊢
      ∃ s' : sp.Seq, sp.locLb γ (sp.leaderOf N c) c s' ∗
        ⌜toCmdId e.1 ∈ s'.map Prod.fst ∧ (e.2.2.map toCmdId).Perm (sp.depsIn s' (toCmdId e.1))⌝ := by
  iintro #H
  iunfold swift.exFolW at H
  icases H with (%h | ⟨%D, #Hld, %HD⟩)
  · exact absurd h hl
  iunfold sp.locDeps at Hld
  icases Hld with ⟨%s, #Hlb, %Hs⟩
  iexists s
  iframe Hlb
  ipureintro
  exact ⟨Hs.1, HD.trans Hs.2⟩

/-- **A report entry's base fact** (round 56, D79 (2), R2-a; persistent): the entry is at `COMMIT`,
or some replica pre-accepted its command at `c` (so it is not of `c`'s base, `sp.preacc_notBase`).
Part of N1-R1's `W` (`swift.n1r1`): a log entry has it from `exEntOk` (a follower's is at
`COMMIT`; a leader's has its own pre-acceptance or the sync disjunct at `COMMIT`, T24). -/
def swift.baseW (γ : sp.Names) (c : Nat) (e : sp.RepEntry) : IProp netDistGF :=
  iprop(⌜e.phase.toNat = 3⌝ ∨ ∃ (r' : Nat) (D' : List sp.CmdId), sp.preacc γ r' c e.id D')

instance swift.baseW_persistent (γ : sp.Names) (c : Nat) (e : sp.RepEntry) :
    Persistent (swift.baseW γ c e) := by
  unfold swift.baseW sp.preacc; infer_instance

/-- An execution entry's base fact (round 56). -/
theorem swift.exec_base1 (γ : sp.Names) (N r c : Nat) (e : swift.ExE)
    (esi : swift.commandStaticDesc) :
    swift.exEntOkE γ N r c e esi ⊢ swift.baseW γ c (swift.xsEnt (e, esi)) := by
  iintro #H
  iunfold swift.exEntOkE at H
  icases H with ⟨Hok, -⟩
  iunfold swift.exEntOk at Hok
  icases Hok with ⟨-, -, -, Hph, Hl⟩
  iunfold swift.baseW
  simp only [swift.xsEnt]
  icases Hph with (⟨%h3, -⟩ | ⟨%hl, -⟩)
  · ileft; ipureintro; rw [h3]; rfl
  icases Hl with (%hn | #Hp | ⟨%h3, -⟩)
  · exact absurd hl hn
  · iright; iexists r, e.2.2.map toCmdId; iexact Hp
  · ileft; ipureintro; rw [h3]; rfl

/-- **A report entry's row fact** (round 57, clause 1; persistent): the entry is at `COMMIT` and
committed, or (at `c`'s leader) at `ACCEPT` and accepted or at `PRE_ACCEPT` and pre-accepted with
its dependencies, or it is a follower's entry below `COMMIT` (a read: its negative row facts come
from its rest record at the report, not from a persistent fact). A log entry has one of the first
two from `exEntOk` (`swift.exec_row1`). Part of N1-R1's `W` (`swift.n1r1`). -/
def swift.rowW (γ : sp.Names) (N r c : Nat) (e : sp.RepEntry) : IProp netDistGF :=
  iprop((⌜e.phase.toNat = 3⌝ ∗ sp.committed γ r c e.id) ∨
    (⌜r = sp.leaderOf N c⌝ ∗ ((⌜e.phase.toNat = 2⌝ ∗ sp.accepted γ r c e.id) ∨
      (⌜e.phase.toNat = 1⌝ ∗ sp.preacc γ r c e.id e.dep))) ∨
    ⌜r ≠ sp.leaderOf N c ∧ e.phase.toNat ≤ 2⌝)

instance swift.rowW_persistent (γ : sp.Names) (N r c : Nat) (e : sp.RepEntry) :
    Persistent (swift.rowW γ N r c e) := by
  unfold swift.rowW sp.committed sp.accepted sp.preacc; infer_instance

/-- `W`'s row facts (round 57). -/
theorem swift.W_rowW (γ : sp.Names) (N r c : Nat) (L : List sp.RepEntry) :
    ([∗list] e ∈ L, iprop(swift.repEntW γ N r c e ∗ swift.rowW γ N r c e)) ⊢
      [∗list] e ∈ L, swift.rowW γ N r c e :=
  BigSepL.bigSepL_mono_of_forall BI.sep_elim_right

/-- An execution entry's row fact (round 57): `exEntOk`'s phase conjunct. -/
theorem swift.exec_row1 (γ : sp.Names) (N r c : Nat) (e : swift.ExE)
    (esi : swift.commandStaticDesc) :
    swift.exEntOkE γ N r c e esi ⊢ swift.rowW γ N r c (swift.xsEnt (e, esi)) := by
  iintro #H
  iunfold swift.exEntOkE at H
  icases H with ⟨Hok, -⟩
  iunfold swift.exEntOk at Hok
  icases Hok with ⟨-, -, -, Hph, -⟩
  iunfold swift.rowW
  simp only [swift.xsEnt]
  icases Hph with (⟨%h3, #Hc⟩ | ⟨%hl, (⟨%h2, #Ha⟩ | ⟨%h1, #Hp⟩)⟩)
  · ileft
    isplitr
    · ipureintro; rw [h3]; rfl
    iexact Hc
  · iright; ileft
    isplitr
    · ipureintro; exact hl
    ileft
    isplitr
    · ipureintro; rw [h2]; rfl
    iexact Ha
  · iright; ileft
    isplitr
    · ipureintro; exact hl
    iright
    isplitr
    · ipureintro; rw [h1]; rfl
    iexact Hp

/-- **A log entry's own facts** (round 58, D82 (3); N1-R1's `WX`, which N1-R2 takes for the log's
entries besides `W`): its base fact (`swift.baseW`, for R2-a) and, from `exEntOk`'s phase, it is
at `COMMIT` or at `c`'s leader (so clause 1's follower case is not a log entry's). -/
def swift.wxW (γ : sp.Names) (N r c : Nat) (e : sp.RepEntry) : IProp netDistGF :=
  iprop(swift.baseW γ c e ∗ ⌜e.phase.toNat = 3 ∨ r = sp.leaderOf N c⌝)

instance swift.wxW_persistent (γ : sp.Names) (N r c : Nat) (e : sp.RepEntry) :
    Persistent (swift.wxW γ N r c e) := by
  unfold swift.wxW; infer_instance

/-- An execution entry's own facts (round 58). -/
theorem swift.exec_wx1 (γ : sp.Names) (N r c : Nat) (e : swift.ExE)
    (esi : swift.commandStaticDesc) :
    swift.exEntOkE γ N r c e esi ⊢ swift.wxW γ N r c (swift.xsEnt (e, esi)) := by
  iintro #H
  ihave #Hb := swift.exec_base1 γ N r c e esi $$ H
  iunfold swift.exEntOkE at H
  icases H with ⟨Hok, -⟩
  iunfold swift.exEntOk at Hok
  icases Hok with ⟨-, -, -, Hph, -⟩
  iunfold swift.wxW
  iframe Hb
  simp only [swift.xsEnt]
  icases Hph with (⟨%h3, -⟩ | ⟨%hl, -⟩)
  · ipureintro; left; rw [h3]; rfl
  · ipureintro; right; exact hl

/-- The log entries' phase facts (round 58). -/
theorem swift.wxW_pure (γ : sp.Names) (N r c : Nat) (L : List sp.RepEntry) :
    ([∗list] e ∈ L, swift.wxW γ N r c e) ⊢ ⌜∀ e ∈ L, e.phase.toNat = 3 ∨ r = sp.leaderOf N c⌝ := by
  induction L with
  | nil => iintro -; ipureintro; intro e he; cases he
  | cons e L ih =>
    iintro H
    icases (BigSepL.bigSepL_cons (PROP := IProp netDistGF)).1 $$ H with ⟨He, H⟩
    iunfold swift.wxW at He
    icases He with ⟨-, %h⟩
    ihave %h2 := ih $$ H
    ipureintro
    intro e' he'
    rcases List.mem_cons.mp he' with rfl | he'
    · exact h
    · exact h2 e' he'

/-- The log entries' base facts (round 58). -/
theorem swift.wx_base (γ : sp.Names) (N r c : Nat) (L : List sp.RepEntry) :
    ([∗list] e ∈ L, swift.wxW γ N r c e) ⊢ [∗list] e ∈ L, swift.baseW γ c e :=
  BigSepL.bigSepL_mono_of_forall (fun {_ _} => by unfold swift.wxW; exact BI.sep_elim_left)

/-- `W`'s witnesses (round 58). -/
theorem swift.W_rep (γ : sp.Names) (N r c : Nat) (L : List sp.RepEntry) :
    ([∗list] e ∈ L, iprop(swift.repEntW γ N r c e ∗ swift.rowW γ N r c e)) ⊢
      [∗list] e ∈ L, swift.repEntW γ N r c e :=
  BigSepL.bigSepL_mono_of_forall BI.sep_elim_left

/-- **A stored home's read facts** (round 58, D82 (1), (4); `desc`'s stored home): from its rest
record's facts (`stopFacts`, `rowFacts`, `rowPhaseOk`) at the read's values (`dv`, `dep`'s contents
`D`), the proposal's `propIs` at the home's `cmd` (`homeP`) and, at `c`'s leader, the replica's
prefix with the dependencies (`homeP`'s, `repPre`'s `ldrPrefix`): the read's entry has `W`
(`repEntW ∗ rowW`), or (a follower's `ACCEPT`/`COMMIT` without the leader's dependencies, D77 (1))
its command was executed in `c`; and a `START` read has no dependencies. -/
theorem swift.storedW (γ : sp.Names) (x : swift.RunX) (c : Nat) (y : swift.CommandId)
    (dv : swift.DescV) (rv : swift.RowV) (cc : sp.Cmd) (D : List swift.CommandId)
    (hrp : swift.rowPhaseOk x.N x.r c dv rv) (hpn : dv.propose ≠ null) :
    swift.stopFacts γ x.γxm x.N x.r c y dv ∗ swift.rowFacts γ x.r c y dv rv ∗ dv.dep ↦*□ D ∗
      swift.propIs γ dv.propose (toCmdId y) cc ∗
      (⌜x.r ≠ sp.leaderOf x.N c⌝ ∨ ∃ s : sp.Seq, sp.locLb γ x.r c s ∗
        ⌜(toCmdId y, cc) ∈ s ∧ (D.map toCmdId).Perm (sp.depsIn s (toCmdId y))⌝) ⊢
      (swift.exIn x.γxm c y ∨
        (swift.repEntW γ x.N x.r c ⟨toCmdId y, dv.phase, cc, D.map toCmdId⟩ ∗
          swift.rowW γ x.N x.r c ⟨toCmdId y, dv.phase, cc, D.map toCmdId⟩)) ∗
      ⌜dv.phase = W64 0 → D.length < 2 ^ 62⌝ := by
  iintro ⟨#Hsf, #Hrf, #HD, #HpI, #Hld⟩
  iunfold swift.stopFacts at Hsf
  icases Hsf with (%Hn | ⟨-, #HD2, #Hpw, #Hdw, -⟩)
  · exact absurd Hn hpn
  ihave %hDD := ownSlice_agree dv.dep DFrac.discard DFrac.discard dv.D D $$ HD2 [HD]
  · iexact HD
  subst hDD
  obtain ⟨-, hrp2⟩ := hrp
  obtain ⟨hle, h0, h1, h2, -, -⟩ := hrp2 hpn
  iunfold swift.rowFacts at Hrf
  icases Hrf with ⟨#Hcom, #Hacc, -, -, %h3c⟩
  ihave #Hcis : sp.cmdIs γ (toCmdId y) cc $$ []
  · iunfold swift.propIs at HpI
    icases HpI with ⟨%pp, %w, %mu, %addr, %ts, %vs, -, -, -, #Hc, -⟩
    iexact Hc
  iunfold swift.phaseWhy at Hpw
  -- from `ACCEPT` on: the leader's prefix (the home's own at the leader; a follower's from
  -- `depWhy`: the leader's dependencies, or executed)
  ihave #Hpre : ∀ _h : 2 ≤ uint.nat dv.phase, swift.exIn x.γxm c y ∨
      ∃ s' : sp.Seq, sp.locLb γ (sp.leaderOf x.N c) c s' ∗
        ⌜toCmdId y ∈ s'.map Prod.fst ∧ (dv.D.map toCmdId).Perm (sp.depsIn s' (toCmdId y))⌝ $$ []
  · iintro %hph1
    by_cases hl : x.r = sp.leaderOf x.N c
    · icases Hld with (%hnl | ⟨%s, #Hlb, %hs⟩)
      · exact absurd hl hnl
      iright
      iexists s
      rw [← hl]
      iframe Hlb
      ipureintro
      exact ⟨List.mem_map.mpr ⟨_, hs.1, rfl⟩, hs.2⟩
    · iunfold swift.depWhy at Hdw
      icases Hdw with ((%Hd1 | ⟨-, #Hex⟩) | ⟨%hor, -⟩ | ⟨%hls, -⟩ | ⟨-, %D', #Hloc, %Hperm⟩)
      · exfalso
        rcases Hd1 with h | h | h
        · omega
        · exact hpn h
        · revert hph1; rw [h]; decide
      · ileft; iexact Hex
      · exfalso
        rcases hor with h | h
        · exact hl h
        · omega
      · exfalso; exact hl hls.1
      · iright
        iunfold sp.locDeps at Hloc
        icases Hloc with ⟨%s, #Hlb, %hs⟩
        iexists s
        iframe Hlb
        ipureintro
        exact ⟨hs.1, Hperm.trans hs.2⟩
  rcases swift.ph_cases dv.phase hle with hp | hp | hp | hp
  · -- `START`: a follower's, no dependencies
    obtain ⟨hD0, hnl⟩ := h0 hp
    isplitl []
    · iright
      isplitl []
      · iunfold swift.repEntW
        dsimp only
        iframe Hcis
        ileft; ipureintro; rw [hp]; rfl
      iunfold swift.rowW
      dsimp only
      iright; iright
      ipureintro; exact ⟨hnl, by rw [hp]; decide⟩
    ipureintro; intro _; rw [hD0]; simp
  · -- `PRE_ACCEPT`: pre-accepted with the dependencies (`phaseWhy`)
    icases Hpw with (%hn1 | #Hpa)
    · exact absurd hp hn1
    isplitl []
    · iright
      isplitl []
      · iunfold swift.repEntW
        dsimp only
        iframe Hcis
        iright; ileft
        isplitr
        · ipureintro; rw [hp]; rfl
        iexact Hpa
      iunfold swift.rowW
      dsimp only
      by_cases hl : x.r = sp.leaderOf x.N c
      · iright; ileft
        isplitr
        · ipureintro; exact hl
        iright
        isplitr
        · ipureintro; rw [hp]; rfl
        iexact Hpa
      · iright; iright; ipureintro; exact ⟨hl, by rw [hp]; decide⟩
    ipureintro; intro h; rw [hp] at h; exact absurd h (by decide)
  · -- `ACCEPT`: the leader's prefix; at the leader, accepted (`rowPhaseOk`, `rowFacts`)
    have h2le : 2 ≤ uint.nat dv.phase := by rw [hp]; decide
    ihave #Hp2 := Hpre $$ %h2le
    icases Hp2 with (#Hex | ⟨%s', #Hlb', %hs'⟩)
    · isplitl []
      · ileft; iexact Hex
      ipureintro; intro h; rw [hp] at h; exact absurd h (by decide)
    isplitl []
    · iright
      isplitl []
      · iunfold swift.repEntW
        dsimp only
        iframe Hcis
        iright; iright
        isplitr
        · ipureintro; left; rw [hp]; decide
        iexists s'
        iframe Hlb'
        ipureintro; exact hs'
      iunfold swift.rowW
      dsimp only
      by_cases hl : x.r = sp.leaderOf x.N c
      · iright; ileft
        isplitr
        · ipureintro; exact hl
        ileft
        isplitr
        · ipureintro; rw [hp]; rfl
        icases Hacc with (%hf | #Ha)
        · exfalso; have := h2 hp; rw [hf] at this; cases this
        iexact Ha
      · iright; iright; ipureintro; exact ⟨hl, by rw [hp]; decide⟩
    ipureintro; intro h; rw [hp] at h; exact absurd h (by decide)
  · -- `COMMIT`: the leader's prefix; committed (`rowFacts`)
    have h2le : 2 ≤ uint.nat dv.phase := by rw [hp]; decide
    ihave #Hp2 := Hpre $$ %h2le
    icases Hp2 with (#Hex | ⟨%s', #Hlb', %hs'⟩)
    · isplitl []
      · ileft; iexact Hex
      ipureintro; intro h; rw [hp] at h; exact absurd h (by decide)
    isplitl []
    · iright
      isplitl []
      · iunfold swift.repEntW
        dsimp only
        iframe Hcis
        iright; iright
        isplitr
        · ipureintro; left; rw [hp]; decide
        iexists s'
        iframe Hlb'
        ipureintro; exact hs'
      iunfold swift.rowW
      dsimp only
      ileft
      isplitr
      · ipureintro; rw [hp]; rfl
      icases Hcom with (%hf | #Hc)
      · exfalso
        rcases h3c hp with h | h
        · rw [hf] at h; cases h
        · exact hpn h
      iexact Hc
    ipureintro; intro h; rw [hp] at h; exact absurd h (by decide)

/-- Clause 1's facts of one entry at the node state `st` (but the `START` dependencies', vacuous
here: the entry is at least `PRE_ACCEPT`). -/
def swift.ent1 (N r c : Nat) (st : sp.RState) (e : sp.RepEntry) : Prop :=
  e.id ∈ st.locAt c ∧ 1 ≤ e.phase.toNat ∧ e.phase.toNat ≤ 3 ∧
    (e.phase.toNat ≥ 2 → (c, e.id) ∈ st.accR ∨ (c, e.id) ∈ st.comR) ∧
    (∀ D, st.preAt c e.id = some D → e.phase.toNat ≥ 2 ∨ (e.phase.toNat = 1 ∧ e.dep = D)) ∧
    ((c, e.id) ∈ st.accR ∨ (c, e.id) ∈ st.comR →
      e.phase.toNat ≥ 2 ∨ (r = sp.leaderOf N c ∧ e.phase.toNat ≥ 1))

/-- **The entries' row facts at the node state** (round 57, clause 1): each entry's `rowW` read
against the replica's state (an identity step of `sp.node_step`): a commit, an acceptance or a
pre-acceptance of `r` at `c` is a row of `st` (`rows_ok`) and puts the command in `r`'s sequence
(`com_ok`, `acc_ok`, `pre_ok`); a follower's entry below `COMMIT` is left to its rest record. -/
theorem swift.rows_facts (γ : sp.Names) (γc γm γl : GName) (E : CoPset) (hE : ↑sp.spN ⊆ E)
    (N : Nat) (fr : Bool) (l : List GoString) (r k : Nat) (st : sp.RState) (c : Nat)
    (L : List sp.RepEntry) (hr : r < N) (hk : nodeOf l r = some k) :
    sp.inv γ γc γm γl ∗ sp.cfg γc γm N fr l ∗ sp.nodeSt γ k (1 : Iris.Qp).half st ∗
      ([∗list] e ∈ L, swift.rowW γ N r c e) ⊢
      |={E}=> sp.nodeSt γ k (1 : Iris.Qp).half st ∗
        ⌜∀ e ∈ L, (r ≠ sp.leaderOf N c ∧ e.phase.toNat ≤ 2) ∨ swift.ent1 N r c st e⌝ := by
  iintro ⟨#Hinv, #Hcfg, Hst, #HL⟩
  imod sp.node_step E hE N fr l r k st none
    (fun s0 => iprop(⌜s0 = st ∧ ∀ e ∈ L, (r ≠ sp.leaderOf N c ∧ e.phase.toNat ≤ 2) ∨
      swift.ent1 N r c st e⌝)) hr hk $$ [Hst]
    with ⟨%st', Hst, -, %Heq⟩
  · iframe Hinv Hcfg Hst
    isplitl []
    · iunfold sp.predPre; itrivial
    unfold sp.stepUpd
    iintro %S %mC %mL %mS %mA %mP %mCo %mR %mPa %HH HC HL' HS HA HP HCo HRp HPa
    obtain ⟨HI, Hsr, Hrs, Hrepr⟩ := HH
    have hrow := HI.rows_ok r c
    rw [Hrs] at hrow
    ihave %Hall := sp.bigSepL_gather
      iprop(ghostMapAuth γ.acc 1 mA ∗ ghostMapAuth γ.pre 1 mP ∗ ghostMapAuth γ.com 1 mCo)
      (fun e => swift.rowW γ N r c e)
      (fun e => (r ≠ sp.leaderOf N c ∧ e.phase.toNat ≤ 2) ∨ swift.ent1 N r c st e) L
      (fun e _ => by
        iintro ⟨⟨HA, HP, HCo⟩, #Hw⟩
        iunfold swift.rowW at Hw
        icases Hw with (⟨%h3, #Hc⟩ | ⟨%hl, (⟨%h2, #Ha⟩ | ⟨%h1, #Hp⟩)⟩ | %h0)
        · iunfold sp.committed at Hc
          ihave %Hlk := ghost_map_lookup $$ HCo Hc
          have hcom : S.com r c e.id := (Hrepr.com r c e.id).1 (by simp [Hlk])
          obtain ⟨-, -, hloc, -⟩ := HI.com_ok r c e.id hcom
          have hcR : (c, e.id) ∈ st.comR := (hrow.2.2.2.2.1 e.id).1 hcom
          ipureintro; right
          refine ⟨by rw [← hrow.1]; exact hloc, by omega, by omega, fun _ => Or.inr hcR,
            fun _ _ => Or.inl (by omega), fun _ => Or.inl (by omega)⟩
        · iunfold sp.accepted at Ha
          ihave %Hlk := ghost_map_lookup $$ HA Ha
          have hacc : S.acc r c e.id := (Hrepr.acc r c e.id).1 (by simp [Hlk])
          obtain ⟨-, hloc, -⟩ := HI.acc_ok r c e.id hacc
          have haR : (c, e.id) ∈ st.accR := (hrow.2.1 e.id).1 hacc
          ipureintro; right
          refine ⟨by rw [← hrow.1]; exact hloc, by omega, by omega, fun _ => Or.inl haR,
            fun _ _ => Or.inl (by omega), fun _ => Or.inl (by omega)⟩
        · iunfold sp.preacc at Hp
          ihave %Hlk := ghost_map_lookup $$ HP Hp
          have hpre : S.pre r c e.id = some e.dep := by rw [← Hrepr.pre]; exact Hlk
          obtain ⟨-, -, hloc, -⟩ := HI.pre_ok r c e.id e.dep hpre
          have hpS : st.preAt c e.id = some e.dep := by rw [← hrow.2.2.1 e.id]; exact hpre
          ipureintro; right
          refine ⟨by rw [← hrow.1]; exact hloc, by omega, by omega, fun h => absurd h (by omega),
            fun D hD => Or.inr ⟨h1, ?_⟩, fun _ => Or.inr ⟨hl, by omega⟩⟩
          rw [hpS] at hD; exact Option.some.inj hD
        · ipureintro; left; exact h0) $$ [HA HP HCo HL]
    · iframe HA HP HCo HL
    imodintro
    iexists S, mL, mS, mA, mP, mCo, mR, mPa
    iframe
    isplitr
    · ipureintro; exact ⟨HI, Hsr, Hrepr, rfl, rfl, sp.PState.le_refl S, fun _ _ => rfl, rfl⟩
    ipureintro; exact ⟨Hrs, Hall⟩
  obtain ⟨rfl, h⟩ := Heq
  imodintro
  iframe Hst
  ipureintro; exact h

/-- **An execution entry's report witness** (round 52, 51-5): `cmdIs` from `exEntOkE` (T15 passes
`repPre`'s `propIs` on); at `c`'s leader the phase facts and `exRepOk`'s `locLb`; at a follower
the committed entry's leader prefix (`swift.exec_wit_follower`, open). -/
theorem swift.exec_wit1 (γ : sp.Names) (N r c : Nat) (e : swift.ExE)
    (esi : swift.commandStaticDesc) :
    swift.exEntOkE γ N r c e esi ⊢ swift.repEntW γ N r c (swift.xsEnt (e, esi)) := by
  iintro #H
  iunfold swift.exEntOkE at H
  icases H with ⟨Hok, Hrep, #Hcis, #HfW⟩
  iunfold swift.repEntW
  simp only [swift.xsEnt]
  iframe Hcis
  iunfold swift.exEntOk at Hok
  icases Hok with ⟨-, -, -, Hph, -⟩
  by_cases hl : r = sp.leaderOf N c
  · iunfold swift.exRepOk at Hrep
    icases Hrep with ⟨-, (%Hn | ⟨-, %s, #Hlb, %Hs⟩)⟩
    · exfalso; exact Hn hl
    icases Hph with (⟨%h3, -⟩ | ⟨-, (⟨%h2, -⟩ | ⟨%h1, #Hpre⟩)⟩)
    · iright; iright
      isplitr
      · ipureintro; right; exact hl
      iexists s; rw [← hl]; iframe Hlb
      ipureintro; exact ⟨List.mem_map.mpr ⟨_, Hs.1, rfl⟩, Hs.2⟩
    · iright; iright
      isplitr
      · ipureintro; right; exact hl
      iexists s; rw [← hl]; iframe Hlb
      ipureintro; exact ⟨List.mem_map.mpr ⟨_, Hs.1, rfl⟩, Hs.2⟩
    · iright; ileft
      isplitr
      · ipureintro; rw [h1]; rfl
      iexact Hpre
  · icases Hph with (⟨%h3, #Hcom⟩ | ⟨%Hl, -⟩)
    · iright; iright
      isplitr
      · ipureintro; left; rw [h3]; decide
      iapply swift.exec_wit_follower γ N r c e hl
      iexact HfW
    · exfalso; exact hl Hl

/-- **The log entries' report witnesses** (round 52, 51-5; `swift.exec_wit1` per entry). -/
theorem swift.exec_wit (γ : sp.Names) (x : swift.RunX) (c : Nat) (X : List swift.ExE)
    (es : List swift.commandStaticDesc) :
    ([∗list] i ↦ e ∈ X, ∃ esi : swift.commandStaticDesc, ⌜es[i]? = some esi⌝ ∗
        swift.exEntOkE γ x.N x.r c e esi) ⊢
      [∗list] e ∈ (X.zip es).map swift.xsEnt,
        iprop((swift.repEntW γ x.N x.r c e ∗ swift.rowW γ x.N x.r c e) ∗ swift.wxW γ x.N x.r c e) := by
  induction X generalizing es with
  | nil => iintro -; simp only [List.zip_nil_left, List.map_nil]; iapply BigSepL.bigSepL_nil.2; itrivial
  | cons e X ih =>
    cases es with
    | nil =>
      iintro -; simp only [List.zip_nil_right, List.map_nil]; iapply BigSepL.bigSepL_nil.2; itrivial
    | cons esi es =>
      simp only [List.zip_cons_cons, List.map_cons]
      iintro H
      icases (BigSepL.bigSepL_cons (PROP := IProp netDistGF)).1 $$ H with ⟨⟨%esi', %h, H0⟩, H⟩
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      iapply (BigSepL.bigSepL_cons (PROP := IProp netDistGF)).2
      isplitl [H0]
      · ihave #H0' := H0
        isplitr
        · isplitr
          · iapply swift.exec_wit1; iexact H0'
          iapply swift.exec_row1; iexact H0'
        iapply swift.exec_wx1; iexact H0'
      iapply ih es
      isimp only [List.getElem?_cons_succ] at H
      iexact H

/-- **R2-a** (round 56, D79 (2); N4's request, N1-R2's second conjunct): a report entry with its
witness and base fact (`W`), of a command of `c`'s base `syncOrder M`, is at `COMMIT` (its base
fact's pre-acceptance would give the command a path, `pre_ok`/`path_ok`, so it is not of the base)
and has the `MSync`'s dependencies: its witness's leader prefix `s'` and the leader's `syncSeq M`
(`syncObj`'s `locLb`) are both prefixes of the leader's sequence of `c` (`sp.locLb_prefix`), so
`depsIn` agrees on them (`sp.depsIn_append_of_mem`), and `M`'s entry has `depsIn (syncSeq M)`
(`sp.syncIs_seq`). -/
theorem swift.r2a_all (γ : sp.Names) (γc γm γl : GName) (E : CoPset) (hE : ↑sp.spN ⊆ E)
    (N r c : Nat) (M : sp.SyncMsg) (XS : List sp.RepEntry) :
    sp.inv γ γc γm γl ∗ sp.syncIs γ c M ∗ sp.locLb γ (sp.leaderOf N c) c (sp.syncSeq M) ∗
      ([∗list] e ∈ XS, iprop(swift.repEntW γ N r c e ∗ swift.baseW γ c e)) ⊢
      |={E}=> ⌜∀ e ∈ XS, e.id ∈ sp.syncOrder M →
        e.phase.toNat = 3 ∧ ∃ p ∈ M, p.1 = e.id ∧ e.dep.Perm p.2.2⌝ := by
  iintro ⟨#Hinv, #HM, #HlbM, #HW⟩
  imod sp.syncIs_seq E hE c M $$ [Hinv HM] with %Hseq
  · iframe Hinv HM
  unfold sp.inv
  iapply (fupd_mask_mono hE)
  iinv Hinv with Hi Hclose
  unfold sp.invBody
  icases Hi with ⟨%S, %mC, %mL, %mS, %mA, %mP, %mCo, %mR, %mN, %sh, %mD, %mQ, %mK, %mPa, >HC, >HL, >HS,
    HA, >HP, HCo, HRp, HN, HH, HD, Hown, HQ, HK, HPa, >%Hrepr, Hnodes, >Hproto, HQs, >%Hcl, >%HDom,
    Hcmds, Hconns⟩
  ihave #HM2 := HM
  iunfold sp.syncIs at HM2
  ihave %HlkM := ghost_map_lookup $$ HS HM2
  have hS : S.sync c = some M := by rw [← Hrepr.sync]; exact HlkM
  icases Hproto with (%He | ⟨%N', %fr, %l, #Hcfg, %Hq⟩)
  · exfalso; rw [He.1.2.1 c] at hS; cases hS
  ihave %HlkS := sp.locLb_lookups (γ := γ) _ _ (sp.syncSeq M) mL mC $$ [HL HC HlbM]
  · iframe HL HC HlbM
  have hpM := (sp.locLb_prefix Hq.1 Hrepr HlkS).2
  ihave %Hall := sp.bigSepL_gather
    iprop(ghostMapAuth γ.loc 1 mL ∗ ghostMapAuth γ.cmds 1 mC ∗ ghostMapAuth γ.pre 1 mP)
    (fun e => iprop(swift.repEntW γ N r c e ∗ swift.baseW γ c e))
    (fun e => e.id ∈ sp.syncOrder M →
      e.phase.toNat = 3 ∧ ∃ p ∈ M, p.1 = e.id ∧ e.dep.Perm p.2.2) XS
    (fun e _ => by
      iintro ⟨⟨HL, HC, HP⟩, #Hw⟩
      icases Hw with ⟨#Hrep, #Hb⟩
      iunfold swift.baseW at Hb
      icases Hb with (%h3 | ⟨%r', %D', #Hp⟩)
      · iunfold swift.repEntW at Hrep
        icases Hrep with ⟨-, (%h0 | ⟨%h1, -⟩ | ⟨-, %s', #Hlb', %hs'⟩)⟩
        · ipureintro; intro _; omega
        · ipureintro; intro _; omega
        ihave %Hlk' := sp.locLb_lookups (γ := γ) _ _ s' mL mC $$ [HL HC Hlb']
        · iframe HL HC Hlb'
        have hp' := (sp.locLb_prefix Hq.1 Hrepr Hlk').2
        ipureintro
        intro hid
        refine ⟨h3, ?_⟩
        obtain ⟨q, hq, hq1⟩ := List.mem_map.mp (sp.syncOrder_mem M e.id hid)
        obtain ⟨y, cc, D⟩ := q
        dsimp only at hq1
        subst hq1
        obtain ⟨-, hD⟩ := Hseq.2 _ cc D hq
        have hidM : e.id ∈ (sp.syncSeq M).map Prod.fst := by rw [Hseq.1]; exact hid
        have heq : sp.depsIn s' e.id = sp.depsIn (sp.syncSeq M) e.id := by
          rcases List.prefix_or_prefix_of_prefix hp' hpM with ⟨u, hu⟩ | ⟨u, hu⟩
          · rw [← hu, sp.depsIn_append_of_mem s' u e.id hs'.1]
          · rw [← hu, sp.depsIn_append_of_mem _ u e.id hidM]
        refine ⟨(e.id, cc, D), hq, rfl, ?_⟩
        rw [heq] at hs'
        exact hs'.2.trans hD.symm
      · iunfold sp.preacc at Hp
        ihave %Hlkp := ghost_map_lookup $$ HP Hp
        have hpre : S.pre r' c e.id = some D' := by rw [← Hrepr.pre]; exact Hlkp
        ipureintro
        intro hid
        exfalso
        obtain ⟨-, -, -, -, hpath⟩ := Hq.1.pre_ok r' c e.id D' hpre
        obtain ⟨P, hP⟩ := Option.ne_none_iff_exists'.mp hpath
        obtain ⟨-, hnb, -⟩ := Hq.1.path_ok r' c e.id P hP
        unfold sp.PState.base at hnb
        rw [hS] at hnb
        exact hnb hid) $$ [HL HC HP HW]
  · iframe HL HC HP HW
  imod Hclose $$ [HC HL HS HA HP HCo HRp HN HH HD Hown HQ HK HPa Hnodes HQs Hcmds Hconns] with -
  · inext
    iexists S, mC, mL, mS, mA, mP, mCo, mR, mN, sh, mD, mQ, mK, mPa
    iframe
    isplitr
    · ipureintro; exact Hrepr
    isplitr
    · iright; iexists N', fr, l; iframe Hcfg; ipureintro; exact Hq
    ipureintro; exact ⟨Hcl, HDom⟩
  imodintro
  ipureintro
  exact Hall

/-- An execution entry's log facts (`exEntOk`'s): the log entry is the report entry's. -/
theorem swift.exec_ent (γ : sp.Names) (N r c : Nat) (e : swift.ExE)
    (esi : swift.commandStaticDesc) :
    swift.exEntOkE γ N r c e esi ⊢ ∃ (vs : GoSlice),
      ⌜toCmdId esi.cmdId' = (swift.xsEnt (e, esi)).id ∧
        (if sint.Z esi.phase' < 1 then 1 else (sint.Z esi.phase').toNat) =
          (swift.xsEnt (e, esi)).phase.toNat ∧
        esi.cmd' = state.Command.mk (swift.xsEnt (e, esi)).cmd.op (swift.xsEnt (e, esi)).cmd.key vs⌝ ∗
      vs ↦*□ (swift.xsEnt (e, esi)).cmd.val ∗
      ∃ D : List swift.CommandId, esi.dep' ↦*□ D ∗ ⌜D.map toCmdId = (swift.xsEnt (e, esi)).dep⌝ := by
  iintro H
  iunfold swift.exEntOkE at H
  icases H with ⟨H, -⟩
  iunfold swift.exEntOk at H
  icases H with ⟨%hid, ⟨%vs, %hcmd, #Hvs⟩, #Hdep, Hph, -⟩
  ihave %hph : ⌜esi.phase' = W64 3 ∨ esi.phase' = W64 2 ∨ esi.phase' = W64 1⌝ $$ [Hph]
  · icases Hph with (⟨%h3, -⟩ | ⟨-, (⟨%h2, -⟩ | ⟨%h1, -⟩)⟩)
    · ipureintro; exact Or.inl h3
    · ipureintro; exact Or.inr (Or.inl h2)
    · ipureintro; exact Or.inr (Or.inr h1)
  iexists vs
  simp only [swift.xsEnt]
  iframe Hvs
  isplitr
  · ipureintro
    refine ⟨by rw [hid], ?_, hcmd⟩
    rcases hph with h | h | h <;> rw [h] <;> decide
  iexists e.2.2
  iframe Hdep
  ipureintro; rfl

/-- The log's entries as `exec` states them (persistent). -/
theorem swift.exec_ents (γ : sp.Names) (N r c : Nat) (X : List swift.ExE)
    (es : List swift.commandStaticDesc) (hlen : es.length = X.length) :
    □ ([∗list] i ↦ e ∈ X, ∃ esi : swift.commandStaticDesc, ⌜es[i]? = some esi⌝ ∗
        swift.exEntOkE γ N r c e esi) ⊢
      [∗list] i ↦ esi ∈ es, ∃ (e : sp.RepEntry) (vs : GoSlice),
        ⌜((X.zip es).map swift.xsEnt)[i]? = some e ∧ toCmdId esi.cmdId' = e.id ∧
          (if sint.Z esi.phase' < 1 then 1 else (sint.Z esi.phase').toNat) = e.phase.toNat ∧
          esi.cmd' = state.Command.mk e.cmd.op e.cmd.key vs⌝ ∗ vs ↦*□ e.cmd.val ∗
        ∃ D : List swift.CommandId, esi.dep' ↦*□ D ∗ ⌜D.map toCmdId = e.dep⌝ := by
  apply BigSepL.bigSepL_intro
  intro k esi hk
  have hkl : k < X.length := by rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hk).1
  obtain ⟨e, he⟩ : ∃ e, X[k]? = some e := ⟨_, List.getElem?_eq_getElem hkl⟩
  iintro #H
  ihave ⟨%esi', %hk', #Hok⟩ := (BigSepL.bigSepL_lookup he) $$ H
  rw [hk] at hk'
  cases hk'
  ihave ⟨%vs, %hv, #Hvs, %D, #HD, %hD⟩ := swift.exec_ent γ N r c e esi $$ Hok
  iexists swift.xsEnt (e, esi), vs
  iframe Hvs
  isplitr
  · ipureintro
    refine ⟨?_, hv⟩
    rw [List.getElem?_map, show (X.zip es)[k]? = some (e, esi) from
      List.getElem?_zip_eq_some.mpr ⟨he, hk⟩]
    rfl
  iexists D
  iframe HD
  ipureintro; exact hD

/-- **N1-R1** (round 51, D70 (1); see NewLeaderReqs.lean), over `Fz := swift.fzX`. Round 58
(D82): every law proved; `W := repEntW ∗ rowW` (a read's or a log entry's), `WX := swift.wxW` (a
log entry's own facts, from `exEntOk`), `Wd := swift.pdW`. -/
def swift.n1r1 (rp : Loc) (γ : sp.Names) (γc γm : GName) (x : swift.RunX) :
    swift.N1R1 rp γ γc γm x where
  Fz := swift.fzX x
  W := fun c e => iprop(swift.repEntW γ x.N x.r c e ∗ swift.rowW γ x.N x.r c e)
  Wd := swift.pdW γ x
  W_pers := fun c e => by infer_instance
  Wd_pers := fun c z D => swift.pdW_persistent γ x c z D
  WX := fun c e => swift.wxW γ x.N x.r c e
  WX_pers := fun c e => swift.wxW_persistent γ x.N x.r c e
  W_wit := fun _ _ => BI.sep_elim_left
  freeze := fun c => swift.fz_freeze γ γc γm x rp c
  thaw := fun c X => swift.fz_thaw γ γc γm x rp c X
  exec := fun c X es bX X' hlen => by
    iintro ⟨#Hctx, HFz, HXl, #Hents⟩
    iunfold swift.fzX at HFz
    icases HFz with ⟨HFz, HFm⟩
    ihave %Hag := ghostVar_agree x.γx (bX, X') (1 : Iris.Qp).half (c, X) (1 : Iris.Qp).half.half
      $$ HXl HFz
    simp only [Prod.mk.injEq] at Hag
    obtain ⟨rfl, rfl⟩ := Hag
    ihave #Hw := swift.exec_wit γ x bX X' es $$ Hents
    icases (BigSepL.bigSepL_sep_eqv (PROP := IProp netDistGF)).1 $$ Hw with ⟨#Hw1, #Hw2⟩
    ihave #Hes := swift.exec_ents γ x.N x.r bX X' es hlen $$ Hents
    imodintro
    isplitl [HFz HFm]
    · iunfold swift.fzX; iframe
    isplitl [HXl]
    · iexact HXl
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    iexists (X'.zip es).map swift.xsEnt
    isplitr
    · ipureintro
      refine ⟨by simp [hlen], ?_⟩
      rw [List.map_map]
      have h1 : (X'.zip es).map ((·.id) ∘ swift.xsEnt) = (X'.zip es).map (fun p => toCmdId p.1.1) := by
        rfl
      have h2 : (X'.zip es).map Prod.fst = X' := List.map_fst_zip (by omega)
      rw [h1]
      calc (X'.zip es).map (fun p => toCmdId p.1.1)
          = ((X'.zip es).map Prod.fst).map (fun e => toCmdId e.1) := by rw [List.map_map]; rfl
        _ = X'.map (fun e => toCmdId e.1) := by rw [h2]
    iframe Hw1 Hes Hw2
  desc := fun c X k d Mc _hk hinjd hinj => by
    -- round 57 (D80 (4)): the home's two forms (`descRestS`); round 58 (D82 (1)): at the stopped
    -- ballot `c`
    iintro ⟨#Hctx, HFz, HPS, Hfree⟩
    ihave #Hctx2 := Hctx
    iunfold swift.descCtxX at Hctx2
    iunfold swift.descCtxE at Hctx2
    icases Hctx2 with ⟨%me, %fr, %lg, %dm, %dc, %ex, %dr, %oe, %γa, %γrm, %rc0, %γrc, -, -,
      -, -, -, -, #Hinv, -⟩
    iunfold swift.descFree at Hfree
    icases Hfree with ⟨%m, %s, %sl, %fa, Hm, Hs, Hsl, Hfa, Hsf, Hff, HDF⟩
    iunfold swift.descDF at HDF
    icases HDF with ⟨%a, %sq, Ha, Hsq, %Has, HR⟩
    iunfold swift.RunX.DR at HR
    iunfold swift.descRestS at HR
    icases HR with (HT | ⟨#HN, %K, %γi, Hcl, HH⟩)
    · -- the tokenless home (`descRestT`): `propose` is `null`, so no entry is read; its
      -- `proposeDep`'s facts (round 58: of the key's command, by the incarnation's half against
      -- the stopped view, `swift.incKey`; `pdOk` → `pdW`, `swift.pdOk_pdW`)
      iunfold swift.descRestT at HT
      icases HT with ⟨%q, %ph, %sqv, %cc, %vs, %dsl, %hs, %pd, %sb, %ap, %wa, %sl', %df, %D, Hsh, #Hmx,
        Hph, Hcmd, #Hvs, %Hop, Hdep, #HD, Hhs, Hsqn, Hp, Hpd, Hpdf, Hap, Hocf, Hslw, Hdf, Hwa, Hsb⟩
      ihave Hpk : |={⊤}=> (▷ ∃ g : swift.DescG, swift.incInv g Mc ∗ ⌜g.ev.b = c⌝ ∗ swift.cgG x g) ∗
          ∃ PD : List swift.CommandId, pd ↦*□ PD ∗
          (⌜pd = slice.nil⌝ ∨ ∀ z : sp.CmdId, ⌜x.str (ofCmdId z) = k⌝ -∗
            swift.pdW γ x c z (PD.map toCmdId)) ∗
          (⌜pd = slice.nil⌝ ∨ ∃ (c0 : swift.DC) (y : swift.CommandId) (γi : GName),
            swift.pdOk c0 c y pd hs sqv ∗ ⌜c0.γ = γ ∧ c0.N = x.sn.N ∧ c0.r = x.sn.r⌝ ∗
            ghostVar γi (1 : Iris.Qp).half (x.sn.str y, d) ∗ swift.cgW x.sn.γcg c γi) $$ [HPS Hpdf]
      · icases Hpdf with (%Hn | ⟨%c0, %y, %γi, #Hok, %Hc0, Hgv, #HcgW⟩)
        · subst Hn
          imodintro
          iframe HPS
          iexists []
          isplitr
          · iapply ownSlice_nil
          isplitr
          · ileft; ipureintro; rfl
          ileft; ipureintro; rfl
        imod swift.incKey x Mc c γi (x.sn.str y) d ⊤ $$ [HPS Hgv HcgW] with ⟨HPS, Hgv, %hMk⟩
        · iframe HPS Hgv; iexact HcgW
        have hky : x.str y = k := hinjd _ hMk
        imod swift.pdOk_pdW γ γc γm x.γl ⊤ (by simp) x c0 c y pd hs sqv ⟨Hc0.1, Hc0.2.2⟩
          $$ [Hinv Hok] with Hpw
        · iframe Hinv Hok
        icases Hpw with (%Hn | ⟨%D', #HD', #Hpw⟩)
        · subst Hn
          imodintro
          iframe HPS
          iexists []
          isplitr
          · iapply ownSlice_nil
          isplitr
          · ileft; ipureintro; rfl
          ileft; ipureintro; rfl
        imodintro
        iframe HPS
        iexists D'.map ofCmdId
        iframe HD'
        isplitr
        · iright
          iintro %z %hz
          have hzy : z = toCmdId y := by
            have h1 : ofCmdId z = y := hinj (hz.trans hky.symm)
            rw [← h1, toCmdId_ofCmdId]
          subst hzy
          have hmap : (D'.map ofCmdId).map toCmdId = D' := by
            simp [List.map_map, Function.comp_def]
          rw [hmap]
          iexact Hpw
        iright
        iexists c0, y, γi
        iframe Hok Hgv HcgW
        ipureintro; exact Hc0
      imod Hpk with ⟨HPS, %PD, #HPD, #Hwd, Hpdf⟩
      imodintro
      iframe HFz HPS
      iexists ⟨k, d, 1, null, ph, cc.op, cc.key, vs, dsl, pd, D, PD, default, cc⟩
      isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      isplitl [Hp Hph Hcmd Hdep Hpd]
      · iunfold swift.DescRead.fields
        iunfold swift.descRepFields
        iframe Hp Hph Hcmd Hdep Hpd HD HPD
      -- round 59 (D84 (2)): no proposal, no claim
      isplitr
      · iunfold swift.rdCl; ileft; ipureintro; rfl
      isplitl [Hm Hs Hsl Hfa Hsf Hff Ha Hsq Hsh Hhs Hsqn Hpdf Hap Hocf Hslw Hdf Hwa Hsb]
      · iintro Hf -
        iunfold swift.DescRead.fields at Hf
        iunfold swift.descRepFields at Hf
        icases Hf with ⟨Hp, Hph, Hcmd, Hdep, -, Hpd, -⟩
        iunfold swift.descFree
        iexists m, s, sl, fa
        iframe Hm Hs Hsl Hfa Hsf Hff
        iunfold swift.descDF
        iexists a, sq
        iframe Ha Hsq
        isplitr
        · ipureintro; exact Has
        iapply swift.descRestT_S
        iunfold swift.descRestT
        iexists q, ph, sqv, cc, vs, dsl, hs, pd, sb, ap, wa, sl', df, D
        iframe Hsh Hmx Hph Hcmd Hvs Hdep HD Hhs Hsqn Hp Hpd Hpdf Hap Hocf Hslw Hdf Hwa Hsb
        ipureintro; exact Hop
      iunfold swift.descReadOk
      isplitr
      · ileft; ipureintro; rfl
      iexact Hwd
    · -- round 58 (D82 (1), (4)): a stored home, its claim on a rest record of `c`
      iunfold swift.descRestH at HH
      icases HH with ⟨%q, %ph, %sqv, %cc, %vs, %dep, %hs, %pd, %sb, %p, %ap, %wa, %sl', %df, Hsh, #Hmx,
        Hph, Hcmd, #Hvs, %Hop, Hdep, Hhs, Hsqn, Hp2, Hp3, Hpd, Hap, Hocf, Hslw, Hdf, Hwa, Hsb, %y,
        %c0, #Hok, %HK, #HhP⟩
      obtain ⟨hK, hc0⟩ := HK
      subst hK
      -- the record: its command `y` at the key `k`, its values the home's, its facts
      imod swift.claimRead γ x Mc (c, toCmdId y) d γi ph dep p $$ [HN Hcl Hph Hdep Hp3 HPS] with
        ⟨Hcl, Hph, Hdep, Hp3, HPS, %x', %dv, %rv, %Hrec, #HsfR, #HrfR⟩
      · iframe HN Hcl Hph Hdep Hp3 HPS
      obtain ⟨hx', hrp, hph, hdep, hp, hMk⟩ := Hrec
      subst hph hdep hp
      have hxy : x' = y := by
        have h1 : toCmdId x' = toCmdId y := hx'
        have h2 := congrArg ofCmdId h1
        simpa using h2
      subst hxy
      have hky : x.str x' = k := hinjd _ hMk
      ihave #Hsf' : swift.stopFacts γ x.γxm x.N x.r c x' dv $$ []
      · iexact HsfR
      ihave #Hrf' : swift.rowFacts γ x.r c x' dv rv $$ []
      · iexact HrfR
      -- `proposeDep`'s facts (`pdOk` → `pdW`)
      imod swift.pdOk_pdW γ γc γm x.γl ⊤ (by simp) x c0 c x' pd hs sqv ⟨hc0.1, hc0.2.2⟩
        $$ [Hinv Hok] with #Hpw
      · iframe Hinv Hok
      ihave ⟨%PD, #HPD, #Hwd⟩ : ∃ PD : List swift.CommandId, pd ↦*□ PD ∗
          (⌜pd = slice.nil⌝ ∨ ∀ z : sp.CmdId, ⌜x.str (ofCmdId z) = k⌝ -∗
            swift.pdW γ x c z (PD.map toCmdId)) $$ []
      · icases Hpw with (%Hn | ⟨%D', #HD', #Hpw⟩)
        · subst Hn
          iexists []
          isplitr
          · iapply ownSlice_nil
          ileft; ipureintro; rfl
        iexists D'.map ofCmdId
        iframe HD'
        iright
        iintro %z %hz
        have hzy : z = toCmdId x' := by
          have h1 : ofCmdId z = x' := hinj (hz.trans hky.symm)
          rw [← h1, toCmdId_ofCmdId]
        subst hzy
        have hmap : (D'.map ofCmdId).map toCmdId = D' := by
          simp [List.map_map, Function.comp_def]
        rw [hmap]
        iexact Hpw
      -- `dep`'s contents and the proposal (`homeP`)
      ihave #HhP2 := HhP
      iunfold swift.homeP at HhP2
      icases HhP2 with ⟨%D, #HD, #HhP3⟩
      -- the read's facts: the record's (`swift.storedW`), or executed in `c` (`swift.fz_exIn`)
      ihave Hr : |={⊤}=> swift.fzX x c X ∗ (⌜dv.propose = null⌝ ∨
          ∃ (pp w mu : Loc) (addr : GoString) (vs' : GoSlice) (ts : w64),
          dv.propose ↦□ replica.defs.GPropose.mk pp w mu false addr ∗
          pp ↦□ replica.defs.Propose.mk (toCmdId x').seq (toCmdId x').cl
            (state.Command.mk cc.op cc.key vs') ts ∗
          ⌜cc.op = cc.op ∧ cc.key = cc.key ∧ x.str (ofCmdId (toCmdId x')) = k ∧
            (dv.phase = W64 0 → D.length < 2 ^ 62)⌝ ∗ vs ↦*□ cc.val ∗
          (⌜toCmdId x' ∈ X.map (fun e => toCmdId e.1)⌝ ∨
            iprop(swift.repEntW γ x.N x.r c ⟨toCmdId x', dv.phase, cc, D.map toCmdId⟩ ∗
              swift.rowW γ x.N x.r c ⟨toCmdId x', dv.phase, cc, D.map toCmdId⟩))) $$ [HFz]
      · icases HhP3 with (%Hpn | ⟨#HpI, #Hld⟩)
        · imodintro; iframe HFz; ileft; ipureintro; exact Hpn
        ihave #HpI2 := HpI
        iunfold swift.propIs at HpI2
        icases HpI2 with ⟨%pp, %w, %mu, %addr, %ts, %vs', #Hgp, #Hpx, -, -, -⟩
        ihave %Hgpnn := typedPointsto_not_null _ _ _ $$ Hgp
        ihave ⟨#HW, %hlen⟩ := swift.storedW γ x c x' dv rv cc D hrp Hgpnn $$ [Hsf' Hrf' HD HpI Hld]
        · iframe Hsf' Hrf' HD HpI
          iexact Hld
        have hkk : x.str (ofCmdId (toCmdId x')) = k := by simpa using hky
        icases HW with (#Hex | #HW)
        · imod swift.fz_exIn γ γc γm x rp c X x' $$ [Hctx HFz Hex] with ⟨HFz, %hX⟩
          · iframe Hctx HFz Hex
          imodintro
          iframe HFz
          iright
          iexists pp, w, mu, addr, vs', ts
          iframe Hgp Hpx Hvs
          isplitr
          · ipureintro; exact ⟨rfl, rfl, hkk, hlen⟩
          ileft; ipureintro; exact hX
        · imodintro
          iframe HFz
          iright
          iexists pp, w, mu, addr, vs', ts
          iframe Hgp Hpx Hvs
          isplitr
          · ipureintro; exact ⟨rfl, rfl, hkk, hlen⟩
          iright; iexact HW
      imod Hr with ⟨HFz, #Hr⟩
      icases (typedPointsto_half_split (swift.dfld d go!"cmd") (state.Command.mk cc.op cc.key vs) (1 : Iris.Qp)).1 $$ Hcmd
        with ⟨Hcmd1, Hcmd2⟩
      icases (typedPointsto_half_split (swift.dfld d go!"proposeDep") pd (1 : Iris.Qp)).1 $$ Hpd with ⟨Hpd1, Hpd2⟩
      imodintro
      iframe HFz HPS
      iexists ⟨k, d, (1 : Iris.Qp).half, dv.propose, dv.phase, cc.op, cc.key, vs, dv.dep, pd, D, PD,
        toCmdId x', cc⟩
      isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      isplitl [Hp2 Hph Hcmd1 Hdep Hpd1]
      · iunfold swift.DescRead.fields
        iunfold swift.descRepFields
        iframe Hp2 Hph Hcmd1 Hdep Hpd1 HD HPD
      -- round 59 (D84 (2)): with a proposal, the claim goes with the read (`swift.rdCl`)
      ihave ⟨Hcl1, Hclw⟩ : (⌜dv.propose = null⌝ ∨
          ∃ γi' : GName, swift.claimTok x.sn.γcl (c, toCmdId x') (.rest d γi')) ∗
          ((⌜dv.propose = null⌝ ∨
            ∃ γi' : GName, swift.claimTok x.sn.γcl (c, toCmdId x') (.rest d γi')) -∗
            ∃ γi' : GName, swift.claimTok x.sn.γcl (c, toCmdId x') (.rest d γi')) $$ [Hcl]
      · by_cases hpn : dv.propose = null
        · isplitr
          · ileft; ipureintro; exact hpn
          iintro -
          iexists γi; iexact Hcl
        · isplitl [Hcl]
          · iright; iexists γi; iexact Hcl
          iintro (%h | H)
          · exact absurd h hpn
          · iexact H
      isplitl [Hcl1]
      · iunfold swift.rdCl; iexact Hcl1
      isplitl [Hm Hs Hsl Hfa Hsf Hff Ha Hsq Hclw Hsh Hcmd2 Hhs Hsqn Hp3 Hpd2 Hap Hocf Hslw Hdf Hwa Hsb]
      · iintro Hf Hcl1
        iunfold swift.rdCl at Hcl1
        ihave ⟨%γi, Hcl⟩ := Hclw $$ Hcl1
        iunfold swift.DescRead.fields at Hf
        iunfold swift.descRepFields at Hf
        icases Hf with ⟨Hp2, Hph, Hcmd1, Hdep, -, Hpd1, -⟩
        ihave Hcmd := (typedPointsto_half_split (swift.dfld d go!"cmd") (state.Command.mk cc.op cc.key vs) (1 : Iris.Qp)).2
          $$ [Hcmd1 Hcmd2]
        · iframe
        ihave Hpd := (typedPointsto_half_split (swift.dfld d go!"proposeDep") pd (1 : Iris.Qp)).2 $$ [Hpd1 Hpd2]
        · iframe
        iunfold swift.descFree
        iexists m, s, sl, fa
        iframe Hm Hs Hsl Hfa Hsf Hff
        iunfold swift.descDF
        iexists a, sq
        iframe Ha Hsq
        isplitr
        · ipureintro; exact Has
        iunfold swift.RunX.DR
        iunfold swift.descRestS
        iright
        iframe HN
        iexists (c, toCmdId x'), γi
        iframe Hcl
        iunfold swift.descRestH
        iexists q, dv.phase, sqv, cc, vs, dv.dep, hs, pd, sb, dv.propose, ap, wa, sl', df
        iframe Hsh Hmx Hph Hcmd Hvs Hdep Hhs Hsqn Hp2 Hp3 Hpd Hap Hocf Hslw Hdf Hwa Hsb
        isplitr
        · ipureintro; exact Hop
        iexists x', c0
        iframe Hok HhP
        ipureintro; exact ⟨rfl, hc0⟩
      iunfold swift.descReadOk
      isplitr
      · iexact Hr
      iexact Hwd
  deliv := fun c X γa γrm hinj => by
    iintro ⟨HFz, Hi⟩
    iunfold swift.delivInv at Hi
    icases Hi with ⟨%M, %bX', %X', %Mx, %rm, HV, HXi, HXp, HMx, HXx, %HM⟩
    iunfold swift.fzX at HFz
    icases HFz with ⟨HFz, HFm⟩
    ihave %Hag := ghostVar_agree x.γx (bX', X') (1 : Iris.Qp).half.half (c, X)
      (1 : Iris.Qp).half.half $$ HXi HFz
    simp only [Prod.mk.injEq] at Hag
    obtain ⟨rfl, rfl⟩ := Hag
    isplitl [HFz HFm]
    · iunfold swift.fzX; iframe
    iexists M
    iframe HV
    isplitl [HXi HXp HMx HXx]
    · iintro HV
      iunfold swift.delivInv
      iexists M, bX', X', Mx, rm
      iframe
      ipureintro; exact HM
    ipureintro
    intro y hy
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hy
    obtain ⟨e, he, hk⟩ := HM.1 _ v hv
    have : ofCmdId y = e.1 := hinj hk
    exact List.mem_map.mpr ⟨e, he, by rw [← this, toCmdId_ofCmdId]⟩
  Wd_seq := fun c z D s => by
    -- round 55 (D76 (3)): both prefixes of the replica's sequence of `c` (`swift.locLb_cmp`); the
    -- bound is `pdW`'s
    iintro ⟨#Hctx, #Hpd, #Hlb⟩
    iunfold swift.descCtxX at Hctx
    iunfold swift.descCtxE at Hctx
    icases Hctx with ⟨%me, %fr, %lg, %dm, %dc, %ex, %dr, %oe, %γa, %γrm, %rc0, %γrc, -, -,
      -, -, -, -, #Hinv, -⟩
    iunfold swift.pdW at Hpd
    icases Hpd with ⟨%s', #Hlb', %Hz⟩
    imod swift.locLb_cmp γ γc γm x.γl ⊤ (by simp) x.r c s s' $$ [Hinv Hlb Hlb'] with %hcmp
    · iframe Hinv Hlb Hlb'
    imodintro
    ipureintro
    intro hzs
    refine ⟨fun d hd => ?_, Hz.2.2⟩
    rcases hcmp with ⟨u, hu⟩ | ⟨u, hu⟩
    · have h := Hz.2.1 d hd
      rw [← hu, sp.depsIn_append_of_mem s u z hzs] at h
      exact h
    · rw [← hu, sp.depsIn_append_of_mem s' u z Hz.1]
      exact Hz.2.1 d hd

/-- **N1-R2** over `swift.n1r1` (round 51; see NewLeaderReqs.lean). Proved (round 59: clause 1's
last case, a read's entry, by the read's own record, `swift.readRecAll`). -/
theorem swift.n1r2 (rp : Loc) (γ : sp.Names) (γc γm : GName) (x : swift.RunX) :
    swift.N1R2 rp γ γc γm x (swift.n1r1 rp γ γc γm x) := by
  intro c X XS S SR γdc Mc dl Pd st O s B M0 hc hs _hB hXS hS hMc _hPd hdl hSR hkey hinj
  simp only [swift.n1r1]
  iintro ⟨#Hctx, HFz, >HPS, Hfp, Hout, Hview, Hflds, Hcls, #HW, #HWXl, #HWd, #Hbase, #Hlb, Hbody⟩
  ihave #Hctx2 := Hctx
  iunfold swift.descCtxX at Hctx2
  iunfold swift.descCtxE at Hctx2
  icases Hctx2 with ⟨%me, %fr, %lg, %dm, %dc, %ex, %dr, %oe, %γa, %γrm, %rc0, %γrc, -, -,
    %Hids, -, -, -, #Hinv, #Hcfg, -, -, -, #HdI, -⟩
  obtain ⟨-, -, hrN, -, -, hk⟩ := Hids
  icases Hbody with ⟨Hn, Hv, He, HO, HS, %hacc, %hrows⟩
  -- clause 4 (round 53): the `proposeDep`s against the whole sequence `s` (`swift.pd_deps`)
  imod swift.pd_deps γ γc γm x.γl x (⊤ \ ↑swift.nodeN) swift.nodeN_diff fr lg st c s Pd hrN hk
    hs $$ [Hinv Hcfg Hn Hlb HWd] with ⟨Hn, %hpd⟩
  · iframe Hinv Hcfg Hn Hlb HWd
  -- round 57 (clause 1): the entries' row facts at `st` (`swift.rows_facts`)
  ihave #HWr := swift.W_rowW γ x.N x.r c (XS ++ S) $$ HW
  -- round 58 (D82 (3)): the log entries are at `COMMIT` or at the leader (`WX`, from `exEntOk`)
  ihave %hXl := swift.wxW_pure γ x.N x.r c XS $$ HWXl
  imod swift.rows_facts γ γc γm x.γl (⊤ \ ↑swift.nodeN) swift.nodeN_diff x.N fr lg x.r x.k st c
    (XS ++ S) hrN hk $$ [Hinv Hcfg Hn HWr] with ⟨Hn, %hrowf⟩
  · iframe Hinv Hcfg Hn HWr
  iunfold swift.storeD at HS
  icases HS with ⟨%Rt, %Out, %Cl, %U, Ha, Hc, Hm, Hu, %hst, %hU⟩
  ihave %hOut := ghostMapAuth_agree x.γout _ _ _ Out $$ Hout Ha
  subst hOut
  rw [hc] at hst
  -- coverage from the store
  ihave #Hbase2 : ⌜c = 0 ∧ B = []⌝ ∨ ∃ M : sp.SyncMsg, sp.syncIs γ c M ∗ ⌜B = sp.syncOrder M⌝ $$ []
  · icases Hbase with (⟨%h1, %h2, -⟩ | ⟨%M, -, #HM, -, %hM⟩)
    · ileft; ipureintro; exact ⟨h1, h2⟩
    · iright; iexists M; iframe HM; ipureintro; exact hM
  ihave ⟨⟨HO, Hm, -⟩, %hcov⟩ := swift.keep_pure
    (swift.rowsCoverAll γ x.γo x.sn st c O Rt Cl B hst hrows) $$ [HO Hm]
  · iframe HO Hm Hbase2
  -- round 56 (D79 (2)): R2-a, the log's entries of the base (`swift.r2a_all`)
  ihave Hr2 : |={⊤ \ ↑swift.nodeN}=> ⌜∀ M, M0 = some M → ∀ e ∈ XS, e.id ∈ B →
      e.phase.toNat = 3 ∧ ∃ p ∈ M, p.1 = e.id ∧ e.dep.Perm p.2.2⌝ $$ []
  · icases Hbase with (⟨%h1, %h2, %h3⟩ | ⟨%M, %hM0, #HM, #HlbM, %hB⟩)
    · imodintro; ipureintro; intro M hM; rw [h3] at hM; cases hM
    · ihave #HWX : [∗list] e ∈ XS, iprop(swift.repEntW γ x.N x.r c e ∗ swift.baseW γ c e) $$ []
      · icases (BigSepL.bigSepL_append (PROP := IProp netDistGF)).1 $$ HW with ⟨#HWX, -⟩
        ihave #H1 := swift.W_rep γ x.N x.r c XS $$ HWX
        ihave #H2 := swift.wx_base γ x.N x.r c XS $$ HWXl
        iapply (BigSepL.bigSepL_sep_eqv (PROP := IProp netDistGF)).2
        iframe H1 H2
      imod swift.r2a_all γ γc γm x.γl (⊤ \ ↑swift.nodeN) swift.nodeN_diff x.N x.r c M XS
        $$ [Hinv HM HlbM HWX] with %Hr
      · iframe Hinv HM HlbM HWX
      imodintro; ipureintro
      intro M' hM' e he hid
      rw [hM0] at hM'
      obtain rfl := Option.some.inj hM'
      exact Hr e he (hB ▸ hid)
  imod Hr2 with %hR2a
  -- round 56 (D79 (1), 52-3): the rest records of `c` are reads of the stopped view
  ihave ⟨⟨HO, Hm, HPS, Hflds⟩, %hrest⟩ := swift.keep_pure
    (swift.restReadAll γ x O Rt Mc SR c hMc hkey hinj) $$ [HO Hm HPS Hflds]
  · iframe HO Hm HPS Hflds
  -- round B1 (D82 (4)): no `released` record of `c` (the free permit, unspent)
  ihave ⟨⟨Hm, Hfp⟩, %hnorel⟩ := swift.keep_pure
    (swift.noReleased γ x.γo x.sn Rt c) $$ [Hm Hfp]
  · iframe Hm; iexact Hfp
  -- round 59 (D84 (2)): a read with a proposal finds its own rest record by its claim
  ihave ⟨⟨HO, Hc, Hm, Hflds, Hcls⟩, %hrd⟩ := swift.keep_pure
    (swift.readRecAll γ x O Rt _ Cl c SR hst) $$ [HO Hc Hm Hflds Hcls]
  · iframe HO Hc Hm Hflds Hcls
  -- a `sync` record at ballot 0 is refuted by `sync_ok`
  by_cases hz : c = 0 ∧ ∃ y, Rt.lookup (c, y) = some .sync
  · obtain ⟨_, y0, hy0⟩ := hz
    ihave #Hsi := swift.recSync_in γ x.γo x.sn Rt (c, y0) hy0 $$ Hm
    iunfold swift.syncIn at Hsi
    icases Hsi with ⟨%M', #HM', -⟩
    imod sp.syncIs_pos (⊤ \ ↑swift.nodeN) swift.nodeN_diff c M' $$ [Hinv HM'] with %hpos
    · iframe Hinv HM'
    exfalso; omega
  -- the `exec` records of `c` are `X`'s (`delivInv`'s ghost map, `X` by `Fz`)
  imod (inv_acc (E := ⊤ \ ↑swift.nodeN) (N := swift.delivN) swift.delivN_node_sub) $$ HdI
    with ⟨Hi, Hclose⟩
  iunfold swift.delivInv at Hi
  icases Hi with ⟨%Md, %bX', %X', %Mx, %rm, >HV, >HXi, >HXp, >HMx, >HXx, >%HM⟩
  iunfold swift.fzX at HFz
  icases HFz with ⟨HFz, HFm⟩
  ihave %Hag := ghostVar_agree x.γx (bX', X') (1 : Iris.Qp).half.half (c, X)
    (1 : Iris.Qp).half.half $$ HXi HFz
  simp only [Prod.mk.injEq] at Hag
  obtain ⟨rfl, rfl⟩ := Hag
  ihave ⟨⟨Hm, HMx⟩, %hexec⟩ := swift.keep_pure
    (swift.execRecs_in γ x.γo x.sn Rt bX' X' Mx HM.2.2.1) $$ [Hm HMx]
  · iframe Hm HMx
  imod Hclose $$ [HV HXi HXp HMx HXx] with -
  · inext; iunfold swift.delivInv; iexists Md, bX', X', Mx, rm; iframe; ipureintro; exact HM
  imodintro
  isplitl [HFz HFm]
  · iunfold swift.fzX; iframe
  isplitl [HPS]
  · inext; iexact HPS
  iframe Hfp Hout Hview Hflds Hcls
  isplitl [Hn Hv He HO Ha Hc Hm Hu]
  · simp only [swift.nodeBody]
    iframe Hn Hv He HO
    isplitl [Ha Hc Hm Hu]
    · iunfold swift.storeD
      iexists Rt, ∅, Cl, U
      iframe
      ipureintro; rw [hc]; exact ⟨hst, hU⟩
    · ipureintro; exact ⟨hacc, hrows⟩
  ipureintro
  refine ⟨?_, ?_⟩
  · unfold swift.coverOk
    refine ⟨fun e he => ?_, fun y hy => ?_, fun y hy => ?_, fun p hp d hd => ?_⟩
    · rcases hrowf e he with hfol | ⟨h1, h2, h3, h4, h5, h6⟩
      · rcases List.mem_append.mp he with hx | hsS
        · exfalso
          rcases hXl e hx with h | h
          · omega
          · exact hfol.1 h
        · -- round 59 (D84 (2)): the read's own record (`swift.readRec`)
          obtain ⟨rd, hrd1, hrde⟩ := hS e hsS
          exact swift.readEnt1 x.N x.r _ st O s rd e hrows hrde (hrd rd hrd1)
      · exact ⟨h1, h3, h4, h5, h6, fun h0 => absurd h0 (by omega)⟩
    · rcases hcov y hy with hB | ⟨rk, hrk, hne, hs0⟩
      · exact Or.inr hB
      · by_cases hsy : rk = .sync
        · exact absurd ⟨hs0 hsy, y, hsy ▸ hrk⟩ hz
        · by_cases hex : rk = .exec
          · subst hex
            left
            rw [List.map_append, hXS]
            exact List.mem_append_left _ (hexec y hrk)
          · cases rk with
            | empty => exact absurd rfl hne
            | sync => exact absurd rfl hsy
            | exec => exact absurd rfl hex
            | released =>
              exact absurd hrk (hnorel y)
            | rest d γi =>
              rcases hrest y ⟨d, γi, hrk⟩ with ⟨r, hr, hp, rfl⟩ | ⟨rv, hrv, h1, h2, h3, h4⟩
              · obtain ⟨e, he1, he2⟩ : ∃ e, r.entry = some e ∧ e.id = r.y := by
                  refine ⟨⟨r.y, r.ph, r.c, r.D.map toCmdId⟩, ?_, rfl⟩
                  unfold swift.DescRead.entry; rw [if_neg hp]
                rcases hSR r hr e he1 with h | h
                · left; rw [← he2]; exact h
                · right; rw [← he2]; exact h
              · -- round B1 (D81): the record's row is empty (`restRead`: no proposal, so no
                -- pre-acceptance, path, acceptance or commit), against the row of `y` at `c`
                exact absurd hy (swift.rowNE_of_empty st _ _ y rv hrows hrv h1 h2 h3 h4)
    · rw [hXS]; exact hdl y hy
    · exact hpd p hp d hd
  · exact hR2a
end reqs

end Perennial.github_com.imdea_software.swiftpaxos

end
