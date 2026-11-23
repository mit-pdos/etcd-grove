/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/DescNode.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The replica's node state as the **descriptors' goroutines** see it (notes/prove-swift.md §1.1,
§1.2, §9): a descriptor's step (pre-accept, accept, commit) runs concurrently with the run loop's
steps, so it cannot read the replica's state off the run loop's view. It knows two things, by
ghost state kept in the node invariant:

* **the epoch** (`epochTok γe q (b, b)`): the replica's ballot and `cballot` are `b` (normal
  operation in ballot `b`). The node invariant holds half of the ghost variable `γe` at
  `(ballot, cballot)`; the other half is split among the epoch's readers (each live descriptor
  goroutine holds a fraction, §1.1's reader token), and the run loop changes the ballot only with
  that whole half back (`stopDescs`).
* **its command's rows** (`rowTok γo b y rv`): the replica's pre-acceptance, path, acceptance and
  commit of `y` in `b` are `rv` (exclusive: the descriptor of `y` owns it; it travels with the
  proposal, `handleProposal` allocates it at `upd_handle`, `handleSync` for the `MSync`'s
  commands). Without it a descriptor could not show that its step is the first of its kind
  (`upd_*`'s freshness premises).

`swift.nodeInvD` is `swift.nodeInv` (Local.lean) with these two; a run-loop step keeping the
ballot and the rows is `swift.run_updD` (as `run_upd`); `handle_stepD` is `handle_step`
allocating the row token. **Shared change (additive)**: the system allocates `nodeInvD` in
place of `nodeInv` (notes/swift-shared-changes.md).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RunSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.HandleStep
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RetBase

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

/-! ## Pure: a command's rows -/


def swift.rowsOf (st : sp.RState) (b : Nat) (y : sp.CmdId) : swift.RowV :=
  (st.preAt b y, st.pathAt b y, decide ((b, y) ∈ st.accR), decide ((b, y) ∈ st.comR))


/-- The row tokens' authority `O` against the replica's state: a token's rows are the
replica's, of a command of its sequence; a command without a token has no rows. -/
def swift.rowsOk (st : sp.RState) (O : GMap (Nat × sp.CmdId) swift.RowV) : Prop :=
  ∀ b y, match O.lookup (b, y) with
    | some rv => rv = swift.rowsOf st b y ∧ y ∈ st.locAt b
    | none => swift.rowsOf st b y = swift.rowEmpty

theorem swift.find?_cons_key {α β : Type} [DecidableEq α] (a : α) (v : β) (l : List (α × β))
    (a' : α) : ((((a, v) :: l).find? (·.1 == a')).map Prod.snd) =
      if a = a' then some v else (l.find? (·.1 == a')).map Prod.snd := by
  by_cases h : a = a'
  · subst h; simp
  · simp [List.find?_cons, h]

theorem swift.rowsOf_preaccepted (st : sp.RState) (b : Nat) (y : sp.CmdId) (D P : List sp.CmdId)
    (b' : Nat) (y' : sp.CmdId) :
    swift.rowsOf (st.preaccepted b y D P) b' y' =
      if (b, y) = (b', y') then (some D, some P, (swift.rowsOf st b y).2.2)
      else swift.rowsOf st b' y' := by
  unfold swift.rowsOf sp.RState.preaccepted sp.RState.preAt sp.RState.pathAt
  by_cases h : (b, y) = (b', y')
  · cases h; simp
  · have h' : ((b, y) == (b', y')) = false := by simpa using h
    simp only [List.find?_cons, h', if_neg h]

theorem swift.rowsOf_accepted (st : sp.RState) (b : Nat) (y : sp.CmdId) (b' : Nat) (y' : sp.CmdId) :
    swift.rowsOf (st.accepted b y) b' y' =
      if (b, y) = (b', y') then ((swift.rowsOf st b y).1, (swift.rowsOf st b y).2.1, true,
        (swift.rowsOf st b y).2.2.2)
      else swift.rowsOf st b' y' := by
  unfold swift.rowsOf sp.RState.accepted
  by_cases h : (b, y) = (b', y')
  · cases h; simp [sp.RState.preAt, sp.RState.pathAt]
  · simp only [if_neg h]
    have : ((b', y') ∈ (b, y) :: st.accR) ↔ (b', y') ∈ st.accR := by
      simp only [List.mem_cons]; constructor
      · rintro (h' | h'); exact absurd h'.symm h; exact h'
      · exact Or.inr
    simp [sp.RState.preAt, sp.RState.pathAt, this]

theorem swift.rowsOf_committed (st : sp.RState) (b : Nat) (y : sp.CmdId) (b' : Nat) (y' : sp.CmdId) :
    swift.rowsOf (st.committed b y) b' y' =
      if (b, y) = (b', y') then ((swift.rowsOf st b y).1, (swift.rowsOf st b y).2.1,
        (swift.rowsOf st b y).2.2.1, true)
      else swift.rowsOf st b' y' := by
  unfold swift.rowsOf sp.RState.committed
  by_cases h : (b, y) = (b', y')
  · cases h; simp [sp.RState.preAt, sp.RState.pathAt]
  · simp only [if_neg h]
    have : ((b', y') ∈ (b, y) :: st.comR) ↔ (b', y') ∈ st.comR := by
      simp only [List.mem_cons]; constructor
      · rintro (h' | h'); exact absurd h'.symm h; exact h'
      · exact Or.inr
    simp [sp.RState.preAt, sp.RState.pathAt, this]

/-- A step changing only `(b, y)`'s rows (to `rv'`), keeping the sequences, keeps `rowsOk` with
the token's new value. -/
theorem swift.rowsOk_step (st st' : sp.RState) (O : GMap (Nat × sp.CmdId) swift.RowV) (b : Nat)
    (y : sp.CmdId) (rv' : swift.RowV) (hok : swift.rowsOk st O) (hin : (O.lookup (b, y)).isSome)
    (hloc : st'.locR = st.locR)
    (hrows : ∀ b' y', swift.rowsOf st' b' y' =
      if (b, y) = (b', y') then rv' else swift.rowsOf st b' y') :
    swift.rowsOk st' (O.insert (b, y) rv') := by
  intro b' y'
  have hla : ∀ c, st'.locAt c = st.locAt c := fun c => by
    unfold sp.RState.locAt; rw [hloc]
  have hk := hok b' y'
  rw [GMap.lookup_insert_eq_iff]
  by_cases h : (b, y) = (b', y')
  · rw [if_pos h]
    cases h
    obtain ⟨rv, hrv⟩ := Option.isSome_iff_exists.mp hin
    rw [hrv] at hk
    refine ⟨by rw [hrows, if_pos rfl], by rw [hla]; exact hk.2⟩
  · rw [if_neg h]
    revert hk
    rcases O.lookup (b', y') with _ | rv
    · intro hk; show swift.rowsOf st' b' y' = _; rw [hrows, if_neg h]; exact hk
    · intro hk; show rv = _ ∧ _; rw [hrows, if_neg h, hla]; exact hk

/-- Every `y ∈ o` set to `rv` in ballot `b`. -/
def swift.insAll {V : Type} (O : GMap (Nat × sp.CmdId) V) (b : Nat) (o : List sp.CmdId)
    (rv : V) : GMap (Nat × sp.CmdId) V :=
  o.foldl (fun O y => O.insert (b, y) rv) O

theorem swift.insAll_lookup {V : Type} (O : GMap (Nat × sp.CmdId) V) (b : Nat) (o : List sp.CmdId)
    (rv : V) (b2 : Nat) (y2 : sp.CmdId) :
    (swift.insAll O b o rv).lookup (b2, y2) =
      if b2 = b ∧ y2 ∈ o then some rv else O.lookup (b2, y2) := by
  induction o generalizing O with
  | nil => simp [swift.insAll]
  | cons y o ih =>
    show (swift.insAll (O.insert (b, y) rv) b o rv).lookup (b2, y2) = _
    rw [ih]
    show _ = if b2 = b ∧ y2 ∈ y :: o then some rv else O.lookup (b2, y2)
    by_cases h3 : b2 = b ∧ y2 ∈ o
    · rw [if_pos h3, if_pos ⟨h3.1, List.mem_cons_of_mem _ h3.2⟩]
    · rw [if_neg h3, GMap.lookup_insert_eq_iff]
      by_cases h2 : (b, y) = (b2, y2)
      · cases h2; rw [if_pos rfl, if_pos ⟨rfl, List.mem_cons_self⟩]
      · rw [if_neg h2]
        have : ¬ (b2 = b ∧ y2 ∈ y :: o) := by
          rintro ⟨rfl, hy⟩
          rcases List.mem_cons.mp hy with rfl | hy
          · exact h2 rfl
          · exact h3 ⟨rfl, hy⟩
        rw [if_neg this]

/-! ## The node invariant with the epoch and the row tokens -/

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [π : NetProtoGS]

/-- The epoch: the replica's ballot and `cballot` (see the file header). -/
def swift.epochOf (st : sp.RState) : Nat × Nat := (st.ballot, st.cballot)

/-- A reader's share of the epoch `(b, c)` (ballot, `cballot`). -/
def swift.epochTok (γe : GName) (q : Qp) (bc : Nat × Nat) : IProp netDistGF := ghostVar γe q bc

/-- The token of `y`'s rows in ballot `b` (exclusive). -/
def swift.rowTok (γo : GName) (b : Nat) (y : sp.CmdId) (rv : swift.RowV) : IProp netDistGF :=
  ghostMapElem γo (b, y) (DFrac.own 1) rv

/-- **The store's parameters** (round 32, notes/lifecycle-plan.md "Revision 5"): the execution
record's map `γxm` (executed records), the ledger `γout` (a ghost map `K ↦ (j, qj)`, its authority
half here, half in the epoch's `descInv`), the claims `γcl`, the commands' strings `str`, and the
replica `r` of `N` (the rest records' facts). -/
structure swift.StN where
  γxm : GName
  γout : GName
  γcl : GName
  str : swift.CommandId → GoString
  N : Nat
  r : Nat
  /-- round 46 (D-SWC2-5, D57): the execution tickets' map (`swift.xTixK`, RetBase.lean) -/
  γxu : GName
  /-- round N5 (D72 (1)): the report tokens' map (`swift.repTok`, DescNode.lean) -/
  γrp : GName
  /-- round 56 (D79 (1), 52-3): the epochs' map ballot ↦ that epoch's commit-witness map `γk`
  (`swift.nodeX`, DescNode.lean; read by `retWhy (.rest d γi)`) -/
  γcg : GName

/-- **The store's pure invariant** (table rev 5/5b §3.7, the ledger): stored and out keys have
rows, are disjoint, and are of ballots up to `cballot` `cb`; every key of `cb` with rows is stored
or out (G-pre: the new leader's pre-sync tokens of a later ballot are the run loop's); a claim
claims a stored key, with the record's kind. -/
def swift.storeOk (cb : Nat) (O : GMap (Nat × sp.CmdId) swift.RowV)
    (Rt : GMap (Nat × sp.CmdId) swift.RecK) (Out : GMap (Nat × sp.CmdId) (Nat × Qp))
    (Cl : GMap (Nat × sp.CmdId) swift.ClK) : Prop :=
  (∀ K, (Rt.lookup K).isSome ∨ (Out.lookup K).isSome → (O.lookup K).isSome) ∧
  (∀ K, K.1 = cb → (O.lookup K).isSome → (Rt.lookup K).isSome ∨ (Out.lookup K).isSome) ∧
  (∀ K, (Rt.lookup K).isSome → Out.lookup K = none) ∧
  (∀ K, (Rt.lookup K).isSome ∨ (Out.lookup K).isSome → K.1 ≤ cb) ∧
  (∀ K ck, Cl.lookup K = some ck → Rt.lookup K = some (swift.recOf ck))

/-- **The returned-rows store** (D32 (a), D34's G-led; table rev 5): the tokens not held by an
owner, each with its record (`swift.retWhy`), the ledger's authority half, the claims'
authority. Round 46 (D-SWC2-5, D57): each stored token with its key's ticket or its use
(`swift.tixOr`), and the tickets' authority `xuAuth` (its keys among the rows' keys `O`). -/
def swift.storeD (γ : sp.Names) (γo : GName) (sn : swift.StN) (cb : Nat)
    (O : GMap (Nat × sp.CmdId) swift.RowV) : IProp netDistGF :=
  iprop(∃ (Rt : GMap (Nat × sp.CmdId) swift.RecK) (Out : GMap (Nat × sp.CmdId) (Nat × Qp))
      (Cl : GMap (Nat × sp.CmdId) swift.ClK) (U : GMap (Nat × sp.CmdId) Unit),
    ghostMapAuth sn.γout (1 : Qp).half Out ∗ ghostMapAuth sn.γcl 1 Cl ∗
    ([∗map] K ↦ rk ∈ Rt, ∃ rv : swift.RowV,
      swift.rowTok γo K.1 K.2 rv ∗ swift.retWhy γ sn.γxm sn.γcg sn.str sn.N sn.r K rv rk ∗
      swift.tixOr sn.γxu sn.γxm K) ∗
    swift.xuAuth sn.γxu U ∗
    ⌜swift.storeOk cb O Rt Out Cl⌝ ∗ ⌜∀ K, (U.lookup K).isSome → (O.lookup K).isSome⌝)

instance swift.storeD_timeless (γ : sp.Names) (γo : GName) (sn : swift.StN) (cb : Nat)
    (O : GMap (Nat × sp.CmdId) swift.RowV) : Timeless (swift.storeD γ γo sn cb O) := by
  unfold swift.storeD swift.rowTok swift.xuAuth; infer_instance

/-- **The report token of ballot `b`** (round N5, D72 (1); exclusive): `newBallot` mints it
(`swift.newBallot_stepD`), `fillNewLeaderAckN` spends it into the node invariant
(`swift.nodeX_report`); held, it refutes an earlier report for `b` (`swift.nodeX_none`). -/
def swift.repTok (γrp : GName) (b : Nat) : IProp netDistGF :=
  ghostMapElem γrp b (DFrac.own 1) ()

/-- **The epochs' map** (round 56, D79 (1), 52-3): `γcg`'s authority, ballot ↦ that epoch's
commit-witness map `γk` (`none` from the ballot's sync step, `swift.takeSync_stepD`, until its
`DescG` is allocated, `swift.descDS_alloc`; then `some γk`, persisted). Every ballot it has is at
most `cballot`, so the sync step to a later ballot finds its key fresh. Round B1 (D82 (4)): the
keys are `(b, false)` (the epoch's registration) and `(b, true)` (its free permit,
`swift.freeP`/`swift.freeSp`); a permit's key is there only once the ballot is registered, so
the registration finds the permit's key fresh. -/
def swift.cgAuth (sn : swift.StN) (cb : Nat) : IProp netDistGF :=
  iprop(∃ G : GMap (Nat × Bool) (Option GName), ghostMapAuth sn.γcg 1 G ∗
    ⌜(∀ k, (G.lookup k).isSome → k.1 ≤ cb) ∧
      ∀ b, (G.lookup (b, true)).isSome → ∃ γk, G.lookup (b, false) = some (some γk)⌝)

/-- **The node invariant's report tokens and base acceptances** (round N5, D72 (1), (2)): the
minted ballots `T` (none above `ballot`, so the next ballot's token is fresh); one spent token per
report; and (D72 (2), a `nodeInv` clause: no model lemma gives it, `PInv` does not tie `cballot`
to the acceptances) every command of `cballot`'s `MSync` is accepted at `cballot` (`tookSync`). -/
def swift.nodeX (γ : sp.Names) (sn : swift.StN) (st : sp.RState) : IProp netDistGF :=
  iprop((∃ T : GMap Nat Unit, ghostMapAuth sn.γrp 1 T ∗
      ⌜∀ b, (T.lookup b).isSome → b ≤ st.ballot⌝) ∗
    ([∗list] p ∈ st.repR, swift.repTok sn.γrp p.1) ∗
    (⌜st.cballot = 0⌝ ∨ ∃ M : sp.SyncMsg, sp.syncIs γ st.cballot M ∗
      ⌜∀ y ∈ sp.syncOrder M, (st.cballot, y) ∈ st.accR⌝) ∗
    swift.cgAuth sn st.cballot)

instance swift.nodeX_timeless (γ : sp.Names) (sn : swift.StN) (st : sp.RState) :
    Timeless (swift.nodeX γ sn st) := by
  unfold swift.nodeX swift.repTok sp.syncIs swift.cgAuth; infer_instance

/-- The node invariant (`nodeInv` with the epoch's half and the row tokens' authority; round 32:
with the store, `swift.storeD`; round N5: the report tokens and base acceptances, `swift.nodeX`). -/
def swift.nodeInvD (γ : sp.Names) (γv γe γo : GName) (sn : swift.StN) (k : Nat) : IProp netDistGF :=
  iprop(∃ (st : sp.RState) (O : GMap (Nat × sp.CmdId) swift.RowV),
    sp.nodeSt γ k (1 : Qp).half st ∗ ghostVar γv (1 : Qp).half (swift.viewOf st) ∗
    ghostVar γe (1 : Qp).half (swift.epochOf st) ∗ ghostMapAuth γo 1 O ∗
    swift.storeD γ γo sn st.cballot O ∗ swift.nodeX γ sn st ∗
    ⌜(∀ b x, (b, x) ∈ st.accR → b ≤ st.cballot) ∧ swift.rowsOk st O⌝)

end defs

section nodeX
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [π : NetProtoGS]

/-- `nodeX` along a step that keeps `cballot` and the reports, grows the acceptances and does
not lower the ballot. -/
theorem swift.nodeX_mono (γ : sp.Names) (sn : swift.StN) (st st' : sp.RState)
    (hb : st.ballot ≤ st'.ballot) (hr : st'.repR = st.repR) (hc : st'.cballot = st.cballot)
    (ha : ∀ p ∈ st.accR, p ∈ st'.accR) :
    swift.nodeX γ sn st ⊢ swift.nodeX γ sn st' := by
  unfold swift.nodeX
  iintro ⟨⟨%T, Ha, %hT⟩, Hs, Hb, Hcg⟩
  isplitl [Ha]
  · iexists T; iframe Ha; ipureintro; intro b h; exact Nat.le_trans (hT b h) hb
  isplitl [Hs]
  · rw [hr]; iexact Hs
  · rw [hc]
    iframe Hcg
    icases Hb with (%h | ⟨%M, #HM, %hM⟩)
    · ileft; ipureintro; exact h
    · iright; iexists M; iframe HM; ipureintro; intro y hy; exact ha _ (hM y hy)

/-- **Minting the next ballot's report token** (`newBallot`, `b' >` the ballot). -/
theorem swift.nodeX_newBal (E : CoPset) (γ : sp.Names) (sn : swift.StN) (st : sp.RState) (b' : Nat)
    (hb : st.ballot < b') :
    swift.nodeX γ sn st ⊢ |={E}=> swift.nodeX γ sn (st.newBal b') ∗ swift.repTok sn.γrp b' := by
  unfold swift.nodeX
  rw [show (st.newBal b').repR = st.repR from rfl, show (st.newBal b').cballot = st.cballot from rfl,
    show (st.newBal b').accR = st.accR from rfl, show (st.newBal b').ballot = b' from rfl]
  iintro ⟨⟨%T, Ha, %hT⟩, Hs, Hb, Hcg⟩
  have hf : T.lookup b' = none := by
    cases h : T.lookup b' with
    | none => rfl
    | some _ => have := hT b' (by rw [h]; rfl); omega
  imod ghost_map_insert (γ := sn.γrp) b' () hf $$ Ha with ⟨Ha, Ht⟩
  imodintro
  unfold swift.repTok
  iframe Ht
  isplitl [Ha]
  · iexists T.insert b' (); iframe Ha; ipureintro
    intro b h
    rw [GMap.lookup_insert_eq_iff] at h
    by_cases e : b' = b
    · omega
    · rw [if_neg e] at h; have := hT b h; omega
  isplitl [Hs]
  · iexact Hs
  · iframe Hb Hcg

/-- **Spending a report token** (`upd_report` at `b'`). -/
theorem swift.nodeX_report (γ : sp.Names) (sn : swift.StN) (st : sp.RState) (b' : Nat)
    (R : sp.Report) :
    swift.nodeX γ sn st ∗ swift.repTok sn.γrp b' ⊢ swift.nodeX γ sn (st.reportedAs b' R) := by
  unfold swift.nodeX
  have e1 : (st.reportedAs b' R).ballot = st.ballot := rfl
  have e2 : (st.reportedAs b' R).repR = (b', R) :: st.repR := rfl
  have e3 : (st.reportedAs b' R).cballot = st.cballot := rfl
  have e4 : (st.reportedAs b' R).accR = st.accR := rfl
  rw [e1, e2, e3, e4]
  iintro ⟨⟨⟨%T, Ha, %hT⟩, Hs, Hb, Hcg⟩, Ht⟩
  isplitl [Ha]
  · iexists T; iframe Ha; ipureintro; exact hT
  isplitl [Hs Ht]
  · iapply BigSepL.bigSepL_cons.2
    iframe
  · iframe Hb Hcg

/-- **A held report token: no report for its ballot yet** (D72 (1): `upd_report`'s `hnone`). -/
theorem swift.nodeX_none (γ : sp.Names) (sn : swift.StN) (st : sp.RState) (b : Nat) :
    swift.nodeX γ sn st ∗ swift.repTok sn.γrp b ⊢
      swift.nodeX γ sn st ∗ swift.repTok sn.γrp b ∗ ⌜st.repAt b = none⌝ := by
  cases h : st.repAt b with
  | none => iintro ⟨H, Ht⟩; iframe H Ht; ipureintro; rfl
  | some R =>
    have : ∃ p ∈ st.repR, p.1 = b := by
      unfold sp.RState.repAt at h
      cases hf : st.repR.find? (·.1 == b) with
      | none => rw [hf] at h; cases h
      | some p =>
        exact ⟨p, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf⟩
    obtain ⟨p, hp, rfl⟩ := this
    unfold swift.nodeX
    iintro ⟨⟨-, Hs, -, -⟩, Ht⟩
    ihave ⟨Hp, -⟩ := (BigSepL.bigSepL_mem_acc (Φ := fun p : Nat × sp.Report =>
      swift.repTok sn.γrp p.1) hp) $$ Hs
    unfold swift.repTok
    icombine Hp Ht gives %Hv
    exfalso; have := DFrac.valid_own_op Hv.1; simp at this

/-- **The base's acceptances** (D72 (2)): at the run loop's last `MSync` `M` of `cballot`. -/
theorem swift.nodeX_base (γ : sp.Names) (sn : swift.StN) (st : sp.RState) (M : sp.SyncMsg)
    (hc : 0 < st.cballot) :
    swift.nodeX γ sn st ∗ sp.syncIs γ st.cballot M ⊢
      swift.nodeX γ sn st ∗ ⌜∀ y ∈ sp.syncOrder M, (st.cballot, y) ∈ st.accR⌝ := by
  unfold swift.nodeX
  iintro ⟨⟨Ha, Hs, Hb, Hcg⟩, #HM⟩
  icases Hb with (%h | ⟨%M', #HM', %hM⟩)
  · exfalso; omega
  · ihave #HM2 := HM
    unfold sp.syncIs
    icombine HM HM' gives %Hv
    obtain ⟨-, rfl⟩ := Hv
    iframe Ha Hs Hcg
    isplitl
    · iright; iexists M; iframe HM2; ipureintro; exact hM
    · ipureintro; exact hM

end nodeX

section lemmas
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [π : NetProtoGS]

theorem swift.nodeN_diff : ↑sp.spN ⊆ (⊤ \ ↑swift.nodeN : CoPset) := by
  intro e he
  rw [LawfulSet.mem_diff]
  exact ⟨CoPset.mem_full, fun h' => swift.nodeN_spN e ⟨h', he⟩⟩

/-- The store under a change of the rows' values (not of their keys). -/
theorem swift.storeOk_dom (cb : Nat) (O O' : GMap (Nat × sp.CmdId) swift.RowV) Rt Out Cl
    (hO : ∀ K, (O.lookup K).isSome ↔ (O'.lookup K).isSome) (h : swift.storeOk cb O Rt Out Cl) :
    swift.storeOk cb O' Rt Out Cl := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨fun K hK => (hO K).1 (h1 K hK), fun K hc hK => h2 K hc ((hO K).2 hK), h3, h4, h5⟩

theorem swift.storeD_dom (γ : sp.Names) (γo : GName) (sn : swift.StN) (cb : Nat)
    (O O' : GMap (Nat × sp.CmdId) swift.RowV)
    (hO : ∀ K, (O.lookup K).isSome ↔ (O'.lookup K).isSome) :
    swift.storeD γ γo sn cb O ⊢ swift.storeD γ γo sn cb O' := by
  unfold swift.storeD
  iintro ⟨%Rt, %Out, %Cl, %U, Ha, Hc, Hm, Hu, %h, %hU⟩
  iexists Rt, Out, Cl, U
  iframe Ha Hc Hm Hu
  isplitr
  · ipureintro; exact swift.storeOk_dom cb O O' Rt Out Cl hO h
  · ipureintro; exact fun K hK => (hO K).1 (hU K hK)

/-- An update of an existing key's rows keeps the store. -/
theorem swift.storeD_upd (γ : sp.Names) (γo : GName) (sn : swift.StN) (cb : Nat)
    (O : GMap (Nat × sp.CmdId) swift.RowV) (K : Nat × sp.CmdId) (rv : swift.RowV)
    (hK : (O.lookup K).isSome) :
    swift.storeD γ γo sn cb O ⊢ swift.storeD γ γo sn cb (O.insert K rv) := by
  apply swift.storeD_dom
  intro K'
  rw [GMap.lookup_insert_eq_iff]
  by_cases e : K = K'
  · subst e; rw [if_pos rfl]; simp [hK]
  · rw [if_neg e]

/-- **A mint into the store** (T28): a fresh key of the current ballot, its token stored with its
record `recOf ck`, and a claim of kind `ck`. -/
theorem swift.storeD_mint (γ : sp.Names) (γo : GName) (sn : swift.StN) (cb : Nat)
    (O : GMap (Nat × sp.CmdId) swift.RowV) (K : Nat × sp.CmdId) (rv : swift.RowV) (ck : swift.ClK)
    (hK : O.lookup K = none) (hcb : K.1 = cb) :
    swift.storeD γ γo sn cb O ∗ swift.rowTok γo K.1 K.2 rv ∗
      swift.retWhy γ sn.γxm sn.γcg sn.str sn.N sn.r K rv (swift.recOf ck) ⊢
    |==> (swift.storeD γ γo sn cb (O.insert K rv) ∗ swift.claimTok sn.γcl K ck) := by
  unfold swift.storeD
  iintro ⟨⟨%Rt, %Out, %Cl, %U, Ha, Hc, Hm, Hu, %h, %hU⟩, Ht, Hw⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hR : Rt.lookup K = none := by
    cases e : Rt.lookup K
    · rfl
    · have := h1 K (Or.inl (by simp [e])); rw [hK] at this; cases this
  have hOut : Out.lookup K = none := by
    cases e : Out.lookup K
    · rfl
    · have := h1 K (Or.inr (by simp [e])); rw [hK] at this; cases this
  have hC : Cl.lookup K = none := by
    cases e : Cl.lookup K with
    | none => rfl
    | some c => have := h5 K c e; rw [hR] at this; cases this
  have hUK : U.lookup K = none := by
    cases e : U.lookup K
    · rfl
    · have := hU K (by simp [e]); rw [hK] at this; cases this
  imod ghost_map_insert K ck hC $$ Hc with ⟨Hc, Hcl⟩
  iunfold swift.xuAuth at Hu
  imod ghost_map_insert K () hUK $$ Hu with ⟨Hu, Htix⟩
  imodintro
  isplitl [Ha Hc Hm Ht Hw Hu Htix]
  · iexists Rt.insert K (swift.recOf ck), Out, Cl.insert K ck, U.insert K ()
    iframe Ha Hc
    isplitl [Hm Ht Hw Htix]
    · iapply (BigSepM.bigSepM_insert (Φ := fun (K : Nat × sp.CmdId) (rk : swift.RecK) =>
        iprop(∃ rv : swift.RowV, swift.rowTok γo K.1 K.2 rv ∗
          swift.retWhy γ sn.γxm sn.γcg sn.str sn.N sn.r K rv rk ∗ swift.tixOr sn.γxu sn.γxm K))
        (show Iris.Std.PartialMap.get? Rt K = none from hR)).2
      iframe Hm
      iexists rv; iframe Ht Hw
      iunfold swift.tixOr; ileft; iunfold swift.xTixK; iexact Htix
    isplitl [Hu]
    · iunfold swift.xuAuth; iexact Hu
    isplitr
    · ipureintro
      refine ⟨fun K' hK' => ?_, fun K' hc hK' => ?_, fun K' hK' => ?_, fun K' hK' => ?_,
        fun K' c hc => ?_⟩
      · rw [GMap.lookup_insert_eq_iff]
        by_cases e : K = K'
        · rw [if_pos e]; rfl
        · rw [if_neg e]; rw [GMap.lookup_insert_eq_iff, if_neg e] at hK'; exact h1 K' hK'
      · rw [GMap.lookup_insert_eq_iff]
        by_cases e : K = K'
        · rw [if_pos e]; left; rfl
        · rw [if_neg e]; rw [GMap.lookup_insert_eq_iff, if_neg e] at hK'; exact h2 K' hc hK'
      · rw [GMap.lookup_insert_eq_iff] at hK'
        by_cases e : K = K'
        · subst e; exact hOut
        · rw [if_neg e] at hK'; exact h3 K' hK'
      · rw [GMap.lookup_insert_eq_iff] at hK'
        by_cases e : K = K'
        · subst e; omega
        · rw [if_neg e] at hK'; exact h4 K' hK'
      · rw [GMap.lookup_insert_eq_iff] at hc ⊢
        by_cases e : K = K'
        · rw [if_pos e] at hc ⊢; cases hc; rfl
        · rw [if_neg e] at hc ⊢; exact h5 K' c hc
    · ipureintro
      intro K' hK'
      rw [GMap.lookup_insert_eq_iff] at hK' ⊢
      by_cases e : K = K'
      · rw [if_pos e]; rfl
      · rw [if_neg e] at hK' ⊢; exact hU K' hK'
  · unfold swift.claimTok; iexact Hcl

/-- New keys of another ballot than `cb` keep the store (`computeSync_stepD`'s pre-sync tokens,
table rev 5b T28b: the run loop's). -/
theorem swift.storeD_grow (γ : sp.Names) (γo : GName) (sn : swift.StN) (cb : Nat)
    (O O' : GMap (Nat × sp.CmdId) swift.RowV)
    (hsub : ∀ K, (O.lookup K).isSome → (O'.lookup K).isSome)
    (hnew : ∀ K, (O'.lookup K).isSome → (O.lookup K).isSome ∨ K.1 ≠ cb) :
    swift.storeD γ γo sn cb O ⊢ swift.storeD γ γo sn cb O' := by
  unfold swift.storeD
  iintro ⟨%Rt, %Out, %Cl, %U, Ha, Hc, Hm, Hu, %h, %hU⟩
  iexists Rt, Out, Cl, U
  iframe Ha Hc Hm Hu
  isplitr
  · ipureintro
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    refine ⟨fun K hK => hsub K (h1 K hK), fun K hc hK => ?_, h3, h4, h5⟩
    rcases hnew K hK with h | h
    · exact h2 K hc h
    · exact absurd hc h
  · ipureintro; exact fun K hK => hsub K (hU K hK)

/-- **Tickets minted for the fresh keys `(b, y)`, `y ∈ o`** (round 46, D-SWC2-5): the authority
grows by the keys, and a ticket of each. -/
theorem swift.xTixK_mintAll (γxu : GName) (b : Nat) :
    ∀ (o : List sp.CmdId) (U : GMap (Nat × sp.CmdId) Unit), o.Nodup →
      (∀ y ∈ o, U.lookup (b, y) = none) →
      swift.xuAuth γxu U ⊢ |==> (swift.xuAuth γxu (swift.insAll U b o ()) ∗
        [∗list] y ∈ o, swift.xTixK γxu (b, y))
  | [], U, _, _ => by
    iintro Hu
    imodintro
    simp only [swift.insAll, List.foldl_nil]
    iframe Hu
    iapply BigSepL.bigSepL_nil.2; iempintro
  | y :: o, U, hnd, hfr => by
    rw [show swift.insAll U b (y :: o) () = swift.insAll (U.insert (b, y) ()) b o () from rfl]
    have hnd' := List.nodup_cons.mp hnd
    iintro Hu
    iunfold swift.xuAuth at Hu
    imod ghost_map_insert (b, y) () (hfr y List.mem_cons_self) $$ Hu with ⟨Hu, Ht⟩
    imod swift.xTixK_mintAll γxu b o (U.insert (b, y) ()) hnd'.2 (fun y' hy' => by
        have hne : (b, y) ≠ (b, y') := fun e => hnd'.1 (by cases e; exact hy')
        rw [GMap.lookup_insert_ne _ _ hne]
        exact hfr y' (List.mem_cons_of_mem _ hy')) $$ [Hu] with ⟨Hu, Hts⟩
    · iunfold swift.xuAuth; iexact Hu
    imodintro
    iframe Hu
    iapply BigSepL.bigSepL_cons.2
    iframe Hts
    iunfold swift.xTixK; iexact Ht

/-- **`storeD_grow` with the new keys' tickets** (round 46, D-SWC2-5; `computeSync_stepD`'s
pre-sync tokens, T28b): the keys `(b, y)`, `y ∈ o`, fresh in `O` and present in `O'`, get their
tickets (the run loop's, with the tokens). -/
theorem swift.storeD_growMint (γ : sp.Names) (γo : GName) (sn : swift.StN) (cb : Nat)
    (O O' : GMap (Nat × sp.CmdId) swift.RowV) (b : Nat) (o : List sp.CmdId) (hnd : o.Nodup)
    (hfr : ∀ y ∈ o, O.lookup (b, y) = none) (hin : ∀ y ∈ o, (O'.lookup (b, y)).isSome)
    (hsub : ∀ K, (O.lookup K).isSome → (O'.lookup K).isSome)
    (hnew : ∀ K, (O'.lookup K).isSome → (O.lookup K).isSome ∨ K.1 ≠ cb) :
    swift.storeD γ γo sn cb O ⊢
      |==> (swift.storeD γ γo sn cb O' ∗ [∗list] y ∈ o, swift.xTixK sn.γxu (b, y)) := by
  unfold swift.storeD
  iintro ⟨%Rt, %Out, %Cl, %U, Ha, Hc, Hm, Hu, %h, %hU⟩
  imod swift.xTixK_mintAll sn.γxu b o U hnd (by
      intro y hy
      cases e : U.lookup (b, y)
      · rfl
      · have := hU (b, y) (by simp [e]); rw [hfr y hy] at this; cases this) $$ Hu
    with ⟨Hu, Hts⟩
  imodintro
  iframe Hts
  iexists Rt, Out, Cl, swift.insAll U b o ()
  iframe Ha Hc Hm Hu
  isplitr
  · ipureintro
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    refine ⟨fun K hK => hsub K (h1 K hK), fun K hc hK => ?_, h3, h4, h5⟩
    rcases hnew K hK with h | h
    · exact h2 K hc h
    · exact absurd hc h
  · ipureintro
    intro K hK
    obtain ⟨b2, y2⟩ := K
    rw [swift.insAll_lookup] at hK
    by_cases e : b2 = b ∧ y2 ∈ o
    · obtain ⟨rfl, hy⟩ := e; exact hin y2 hy
    · rw [if_neg e] at hK; exact hsub _ (hU _ hK)

/-- The sync order's tokens into the store, claims of kind `sync` out (component level). -/
theorem swift.store_insSync (γ : sp.Names) (γo : GName) (sn : swift.StN) (b' : Nat)
    (M : sp.SyncMsg) :
    ∀ (o : List sp.CmdId) (Rt : GMap (Nat × sp.CmdId) swift.RecK)
      (Cl : GMap (Nat × sp.CmdId) swift.ClK), o.Nodup →
      (∀ y ∈ o, Rt.lookup (b', y) = none ∧ Cl.lookup (b', y) = none) →
      (∀ y ∈ o, y ∈ sp.syncOrder M) →
      sp.syncIs γ b' M ∗ ghostMapAuth sn.γcl 1 Cl ∗
        ([∗map] K ↦ rk ∈ Rt, ∃ rv : swift.RowV,
          swift.rowTok γo K.1 K.2 rv ∗ swift.retWhy γ sn.γxm sn.γcg sn.str sn.N sn.r K rv rk ∗
          swift.tixOr sn.γxu sn.γxm K) ∗
        ([∗list] y ∈ o, swift.rowTok γo b' y swift.rvSync) ∗
        ([∗list] y ∈ o, swift.xTixK sn.γxu (b', y)) ⊢
      |==> (ghostMapAuth sn.γcl 1 (swift.insAll Cl b' o .sync) ∗
        ([∗map] K ↦ rk ∈ swift.insAll Rt b' o .sync, ∃ rv : swift.RowV,
          swift.rowTok γo K.1 K.2 rv ∗ swift.retWhy γ sn.γxm sn.γcg sn.str sn.N sn.r K rv rk ∗
          swift.tixOr sn.γxu sn.γxm K) ∗
        [∗list] y ∈ o, swift.claimTok sn.γcl (b', y) .sync)
  | [], Rt, Cl, _, _, _ => by
    iintro ⟨-, Hc, Hm, -, -⟩
    imodintro
    simp only [swift.insAll, List.foldl_nil]
    iframe Hc Hm
    iapply BigSepL.bigSepL_nil.2; iempintro
  | y :: o, Rt, Cl, hnd, hfr, hM => by
    rw [show swift.insAll Cl b' (y :: o) .sync = swift.insAll (Cl.insert (b', y) .sync) b' o .sync
      from rfl, show swift.insAll Rt b' (y :: o) .sync =
        swift.insAll (Rt.insert (b', y) .sync) b' o .sync from rfl]
    have hnd' := List.nodup_cons.mp hnd
    iintro ⟨#HM, Hc, Hm, Ht, Hx⟩
    icases BigSepL.bigSepL_cons.1 $$ Ht with ⟨Ht1, Ht⟩
    icases BigSepL.bigSepL_cons.1 $$ Hx with ⟨Hx1, Hx⟩
    imod ghost_map_insert (b', y) swift.ClK.sync (hfr y List.mem_cons_self).2 $$ Hc with ⟨Hc, Hcl⟩
    ihave Hm : ([∗map] K ↦ rk ∈ Rt.insert (b', y) swift.RecK.sync, ∃ rv : swift.RowV,
        swift.rowTok γo K.1 K.2 rv ∗ swift.retWhy γ sn.γxm sn.γcg sn.str sn.N sn.r K rv rk ∗
        swift.tixOr sn.γxu sn.γxm K) $$ [Hm Ht1 Hx1]
    · iapply (BigSepM.bigSepM_insert (Φ := fun (K : Nat × sp.CmdId) (rk : swift.RecK) =>
        iprop(∃ rv : swift.RowV, swift.rowTok γo K.1 K.2 rv ∗
          swift.retWhy γ sn.γxm sn.γcg sn.str sn.N sn.r K rv rk ∗ swift.tixOr sn.γxu sn.γxm K))
        (show Iris.Std.PartialMap.get? Rt (b', y) = none from (hfr y List.mem_cons_self).1)).2
      iframe Hm
      iexists swift.rvSync
      iframe Ht1
      ihave Hx1 : swift.tixOr sn.γxu sn.γxm (b', y) $$ [Hx1]
      · iunfold swift.tixOr; ileft; iexact Hx1
      iframe Hx1
      dsimp only [swift.retWhy]
      isplitl []
      · ipureintro; rfl
      · iunfold swift.syncIn; iexists M; iframe HM; ipureintro; exact hM y List.mem_cons_self
    imod swift.store_insSync γ γo sn b' M o (Rt.insert (b', y) .sync) (Cl.insert (b', y) .sync)
      hnd'.2 (fun y' hy' => by
        have hne : (b', y) ≠ (b', y') := fun e => hnd'.1 (by cases e; exact hy')
        rw [GMap.lookup_insert_ne _ _ hne, GMap.lookup_insert_ne _ _ hne]
        exact hfr y' (List.mem_cons_of_mem _ hy'))
      (fun y' hy' => hM y' (List.mem_cons_of_mem _ hy')) $$ [HM Hc Hm Ht Hx] with ⟨Hc, Hm, Hcls⟩
    · iframe HM Hc Hm Ht Hx
    imodintro
    iframe Hc Hm
    iapply BigSepL.bigSepL_cons.2
    iframe Hcls
    unfold swift.claimTok; iexact Hcl

/-- **`takeSync_stepD`'s store step** (T28, rev 5b G-pre): `cballot` moves from `cb` to `b'`;
the sync order's tokens go into the store as `sync` records, and the run loop gets `sync`
claims. -/
theorem swift.storeD_takeSync (γ : sp.Names) (γo : GName) (sn : swift.StN) (cb b' : Nat)
    (O : GMap (Nat × sp.CmdId) swift.RowV) (M : sp.SyncMsg) (o : List sp.CmdId) (hnd : o.Nodup)
    (hb : cb < b') (ho : ∀ y ∈ o, y ∈ sp.syncOrder M)
    (hcov : ∀ y, ((swift.insAll O b' o swift.rvSync).lookup (b', y)).isSome → y ∈ o) :
    swift.storeD γ γo sn cb O ∗ sp.syncIs γ b' M ∗
      ([∗list] y ∈ o, swift.rowTok γo b' y swift.rvSync) ∗
      -- round 46 (D-SWC2-5): the keys' tickets (the new leader's, minted with its pre-sync
      -- tokens), or fresh keys (a follower's: minted here)
      (⌜∀ y ∈ o, O.lookup (b', y) = none⌝ ∨ [∗list] y ∈ o, swift.xTixK sn.γxu (b', y)) ⊢
    |==> (swift.storeD γ γo sn b' (swift.insAll O b' o swift.rvSync) ∗
      [∗list] y ∈ o, swift.claimTok sn.γcl (b', y) .sync) := by
  unfold swift.storeD
  iintro ⟨⟨%Rt, %Out, %Cl, %U, Ha, Hc, Hm, Hu, %h, %hU⟩, #HM, Ht, Htx⟩
  ihave Hx : (|==> ∃ U' : GMap (Nat × sp.CmdId) Unit, swift.xuAuth sn.γxu U' ∗
      ⌜∀ K, (U'.lookup K).isSome → ((swift.insAll O b' o swift.rvSync).lookup K).isSome⌝ ∗
      [∗list] y ∈ o, swift.xTixK sn.γxu (b', y)) $$ [Hu Htx]
  · icases Htx with (%hfr | Htx)
    · imod swift.xTixK_mintAll sn.γxu b' o U hnd (by
          intro y hy
          cases e : U.lookup (b', y)
          · rfl
          · have := hU (b', y) (by simp [e]); rw [hfr y hy] at this; cases this) $$ Hu
        with ⟨Hu, Hts⟩
      imodintro
      iexists swift.insAll U b' o ()
      iframe Hu Hts
      ipureintro
      intro K hK
      obtain ⟨b2, y2⟩ := K
      rw [swift.insAll_lookup] at hK ⊢
      by_cases e : b2 = b' ∧ y2 ∈ o
      · rw [if_pos e]; rfl
      · rw [if_neg e] at hK ⊢; exact hU _ hK
    · imodintro
      iexists U
      iframe Hu Htx
      ipureintro
      intro K hK
      obtain ⟨b2, y2⟩ := K
      rw [swift.insAll_lookup]
      by_cases e : b2 = b' ∧ y2 ∈ o
      · rw [if_pos e]; rfl
      · rw [if_neg e]; exact hU _ hK
  imod Hx with ⟨%U', Hu, %hU', Hts⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hRt : ∀ y, Rt.lookup (b', y) = none := by
    intro y
    cases e : Rt.lookup (b', y)
    · rfl
    · have := h4 (b', y) (Or.inl (by simp [e])); simp at this; omega
  have hOut : ∀ y, Out.lookup (b', y) = none := by
    intro y
    cases e : Out.lookup (b', y)
    · rfl
    · have := h4 (b', y) (Or.inr (by simp [e])); simp at this; omega
  have hCl : ∀ y, Cl.lookup (b', y) = none := by
    intro y
    cases e : Cl.lookup (b', y) with
    | none => rfl
    | some c => have := h5 _ c e; rw [hRt y] at this; cases this
  imod swift.store_insSync γ γo sn b' M o Rt Cl hnd (fun y _ => ⟨hRt y, hCl y⟩) ho
    $$ [HM Hc Hm Ht Hts] with ⟨Hc, Hm, Hcls⟩
  · iframe HM Hc Hm Ht Hts
  imodintro
  iframe Hcls
  iexists swift.insAll Rt b' o .sync, Out, swift.insAll Cl b' o .sync, U'
  iframe Ha Hc Hm Hu
  isplitr
  rotate_left
  · ipureintro; exact hU'
  ipureintro
  refine ⟨fun K hK => ?_, fun K hc hK => ?_, fun K hK => ?_, fun K hK => ?_, fun K c hc => ?_⟩
  · obtain ⟨b2, y2⟩ := K
    rw [swift.insAll_lookup]
    by_cases e : b2 = b' ∧ y2 ∈ o
    · rw [if_pos e]; rfl
    · rw [if_neg e]
      rw [swift.insAll_lookup, if_neg e] at hK
      exact h1 _ hK
  · obtain ⟨b2, y2⟩ := K
    simp only at hc; subst hc
    left; rw [swift.insAll_lookup, if_pos ⟨rfl, hcov y2 hK⟩]; rfl
  · obtain ⟨b2, y2⟩ := K
    rw [swift.insAll_lookup] at hK
    by_cases e : b2 = b' ∧ y2 ∈ o
    · obtain ⟨rfl, -⟩ := e; exact hOut y2
    · rw [if_neg e] at hK; exact h3 _ hK
  · obtain ⟨b2, y2⟩ := K
    rw [swift.insAll_lookup] at hK
    by_cases e : b2 = b' ∧ y2 ∈ o
    · simp [e.1]
    · rw [if_neg e] at hK; have := h4 _ hK; simp only at this ⊢; omega
  · obtain ⟨b2, y2⟩ := K
    rw [swift.insAll_lookup] at hc ⊢
    by_cases e : b2 = b' ∧ y2 ∈ o
    · rw [if_pos e] at hc ⊢; cases hc; rfl
    · rw [if_neg e] at hc ⊢; exact h5 _ c hc

/-- **A run-loop step on the node state** (as `swift.run_upd`) that keeps the epoch, every
command's rows and every sequence's commands. -/
theorem swift.run_updD (E : CoPset) (hE : ↑swift.nodeN ⊆ E) (γ : sp.Names) (γv γe γo : GName) {sn : swift.StN}
    (k : Nat) (w w' : swift.LView) (f : sp.RState → sp.RState) (Q : IProp netDistGF)
    (hw : ∀ st, swift.viewOf st = w → swift.viewOf (f st) = w')
    (hep : ∀ st, swift.viewOf st = w → swift.epochOf (f st) = swift.epochOf st)
    (hacc : ∀ st, swift.viewOf st = w → (∀ b x, (b, x) ∈ st.accR → b ≤ st.cballot) →
      ∀ b x, (b, x) ∈ (f st).accR → b ≤ (f st).cballot)
    (hrows : ∀ st, swift.viewOf st = w → ∀ b y, swift.rowsOf (f st) b y = swift.rowsOf st b y)
    (hloc : ∀ st, swift.viewOf st = w → ∀ b y, y ∈ st.locAt b → y ∈ (f st).locAt b)
    (hX : ∀ st, (f st).repR = st.repR ∧ (f st).ballot = st.ballot ∧ ∀ p ∈ st.accR, p ∈ (f st).accR := by
      intro st; exact ⟨rfl, rfl, fun p h => by first | exact h | exact List.mem_cons_of_mem _ h⟩) :
    inv swift.nodeN (swift.nodeInvD γ γv γe γo sn k) ∗ ghostVar γv (1 : Qp).half w ∗
      (∀ st, ⌜swift.viewOf st = w⌝ -∗ sp.nodeSt γ k (1 : Qp).half st ={E \ ↑swift.nodeN}=∗
        sp.nodeSt γ k (1 : Qp).half (f st) ∗ Q) ⊢
    |={E}=> ghostVar γv (1 : Qp).half w' ∗ Q := by
  iintro ⟨#Hinv, Hw, Hstep⟩
  iinv Hinv with Hi Hclose
  iunfold swift.nodeInvD at Hi
  imod Hi
  icases Hi with ⟨%st, %O, Hst, Hw2, He, HO, HS, HX, %Hacc, %Hok⟩
  ihave %Heq := ghostVar_agree γv w (1 : Qp).half (swift.viewOf st) (1 : Qp).half $$ Hw Hw2
  imod Hstep $$ %st %Heq.symm Hst with ⟨Hst, HQ⟩
  imod ghostVar_update_halves w' γv w (swift.viewOf st) $$ Hw Hw2 with ⟨Hw, Hw2⟩
  imod Hclose $$ [Hst Hw2 He HO HS HX] with -
  · inext
    iunfold swift.nodeInvD
    iexists f st, O
    iframe Hst HO
    isplitl [Hw2]
    · rw [hw st Heq.symm]; iexact Hw2
    isplitl [He]
    · rw [hep st Heq.symm]; iexact He
    have hc : (f st).cballot = st.cballot := congrArg Prod.snd (hep st Heq.symm)
    isplitl [HS]
    · rw [hc]; iexact HS
    isplitl [HX]
    · iapply (swift.nodeX_mono γ sn st (f st) (Nat.le_of_eq (hX st).2.1.symm) (hX st).1 hc
        (hX st).2.2)
      iexact HX
    · ipureintro
      refine ⟨hacc st Heq.symm Hacc, fun b y => ?_⟩
      have hk := Hok b y
      revert hk
      rcases O.lookup (b, y) with _ | rv
      · intro hk; show swift.rowsOf (f st) b y = _; rw [hrows st Heq.symm]; exact hk
      · intro hk; show rv = _ ∧ _; rw [hrows st Heq.symm]
        exact ⟨hk.1, hloc st Heq.symm b y hk.2⟩
  imodintro
  iframe

/-- Open the node invariant for a descriptor's step on `y` in its epoch `b`: the replica's
state `st` has ballot and `cballot` `b`, and `y`'s rows are the token's. The step `f` changes
only `y`'s rows (to `rv'`) and keeps the sequences and the acceptances' bound. -/
theorem swift.desc_upd (γ : sp.Names) (γv γe γo : GName) {sn : swift.StN} (k : Nat) (q : Qp) (b : Nat)
    (y : sp.CmdId) (rv rv' : swift.RowV) (f : sp.RState → sp.RState) (Q : IProp netDistGF)
    (hv : ∀ st, swift.viewOf (f st) = swift.viewOf st)
    (hep : ∀ st, swift.epochOf (f st) = swift.epochOf st)
    (haccf : ∀ st, st.ballot = b → st.cballot = b → (∀ b x, (b, x) ∈ st.accR → b ≤ st.cballot) →
      ∀ b x, (b, x) ∈ (f st).accR → b ≤ (f st).cballot)
    (hrows : ∀ st, rv = swift.rowsOf st b y → ∀ b' y', swift.rowsOf (f st) b' y' =
      if (b, y) = (b', y') then rv' else swift.rowsOf st b' y')
    (hX : ∀ st, (f st).repR = st.repR ∧ (f st).ballot = st.ballot ∧ ∀ p ∈ st.accR, p ∈ (f st).accR := by
      intro st; exact ⟨rfl, rfl, fun p h => by first | exact h | exact List.mem_cons_of_mem _ h⟩) :
    inv swift.nodeN (swift.nodeInvD γ γv γe γo sn k) ∗ swift.epochTok γe q (b, b) ∗
      swift.rowTok γo b y rv ∗
      (∀ st, ⌜st.ballot = b ∧ st.cballot = b ∧ rv = swift.rowsOf st b y ∧ y ∈ st.locAt b⌝ -∗
        sp.nodeSt γ k (1 : Qp).half st ={⊤ \ ↑swift.nodeN}=∗ sp.nodeSt γ k (1 : Qp).half (f st) ∗ Q) ⊢
    |={⊤}=> swift.epochTok γe q (b, b) ∗ swift.rowTok γo b y rv' ∗ Q := by
  iintro ⟨#Hinv, Hep, Htok, Hstep⟩
  iinv Hinv with Hi Hclose
  iunfold swift.nodeInvD at Hi
  imod Hi
  icases Hi with ⟨%st, %O, Hst, Hw2, He, HO, HS, HX, %Hacc, %Hok⟩
  unfold swift.epochTok swift.rowTok
  ihave %Heq := ghostVar_agree γe (b, b) q (swift.epochOf st) (1 : Qp).half $$ Hep He
  have hb : st.ballot = b := by have := congrArg Prod.fst Heq; exact this.symm
  have hc : st.cballot = b := by have := congrArg Prod.snd Heq; exact this.symm
  ihave %Hlk := ghost_map_lookup $$ HO Htok
  have hrv : rv = swift.rowsOf st b y ∧ y ∈ st.locAt b := by
    have := Hok b y; rw [Hlk] at this; exact this
  imod Hstep $$ %st %(⟨hb, hc, hrv.1, hrv.2⟩ : _ ∧ _ ∧ _ ∧ _) Hst with ⟨Hst, HQ⟩
  imod ghost_map_update rv' $$ HO Htok with ⟨HO, Htok⟩
  imod Hclose $$ [Hst Hw2 He HO HS HX] with -
  · inext
    iunfold swift.nodeInvD
    iexists f st, O.insert (b, y) rv'
    iframe Hst HO
    isplitl [Hw2]
    · rw [hv st]; iexact Hw2
    isplitl [He]
    · rw [hep st]; iexact He
    have hc' : (f st).cballot = st.cballot := congrArg Prod.snd (hep st)
    isplitl [HS]
    · rw [hc']
      iapply (swift.storeD_upd γ γo sn st.cballot O (b, y) rv' (by simp [Hlk]))
      iexact HS
    isplitl [HX]
    · iapply (swift.nodeX_mono γ sn st (f st) (Nat.le_of_eq (hX st).2.1.symm) (hX st).1 hc'
        (hX st).2.2)
      iexact HX
    · ipureintro
      refine ⟨haccf st hb hc Hacc, swift.rowsOk_step st (f st) O b y rv' Hok (by simp [Hlk]) ?_
        (hrows st hrv.1)⟩
      have := congrArg (fun w : swift.LView => w.2.2.2) (hv st); exact this
  imodintro
  iframe

variable [swift.Assumptions] in
instance swift.baseIs_persistent (γ : sp.Names) (b : Nat) (B : List sp.CmdId) :
    Persistent (swift.baseIs γ b B) := by
  unfold swift.baseIs; infer_instance

variable [swift.Assumptions] in
/-- **A pre-acceptance from `y`'s descriptor** (`handlePropose`'s `MFastAck`) in its epoch `b`:
`upd_preaccept'` through `nodeInvD`, with the row token showing it is the first. -/
theorem swift.preaccept_dstep (γ : sp.Names) (γc γm γl γv γe γo : GName) {sn : swift.StN} (N r k : Nat) (fr : Bool)
    (l : List GoString) (q : Qp) (b : Nat) (y : sp.CmdId) (s : sp.Seq) (B D P : List sp.CmdId)
    (rv : swift.RowV) (hr : r < N) (hk : nodeOf l r = some k) (hAQ : r ∈ sp.AQ N b)
    (hy : y ∈ s.map Prod.fst) (hD : D = sp.depsIn s y) (hB : y ∉ B)
    (hlast : P.getLast? = some y) (hLP : r = sp.leaderOf N b → P = sp.kpOf s B y)
    (hP : ∀ z ∈ sp.kpOf s B y, z ∈ P) (hrv : rv.1 = none ∧ rv.2.1 = none) (W' : List w64) :
    sp.inv γ γc γm γl ∗ sp.cfg γc γm N fr l ∗ inv swift.nodeN (swift.nodeInvD γ γv γe γo sn k) ∗
      swift.epochTok γe q (b, b) ∗ swift.rowTok γo b y rv ∗ sp.locLb γ r b s ∗
      swift.baseIs γ b B ∗ sp.predPre γ k (some (sp.PEv.preaccept b y D, W')) ⊢
    |={⊤}=> swift.epochTok γe q (b, b) ∗ swift.rowTok γo b y (some D, some P, rv.2.2) ∗
      (sp.predPost γ k (some (sp.PEv.preaccept b y D, W')) ∗
        sp.preacc γ r b y D ∗ sp.pathIs γ r b y P) := by
  iintro ⟨#Hinv, #Hcfg, #Hninv, Hep, Htok, #Hlb, #HB, Hpre⟩
  iapply (swift.desc_upd γ γv γe γo k q b y rv (some D, some P, rv.2.2)
    (fun st => st.preaccepted b y D P) iprop(sp.predPost γ k (some (sp.PEv.preaccept b y D, W')) ∗
      sp.preacc γ r b y D ∗ sp.pathIs γ r b y P)
    (fun _ => rfl) (fun _ => rfl) (fun st _ _ hacc => hacc)
    (fun st hrv' b' y' => by rw [swift.rowsOf_preaccepted, ← hrv']))
  iframe Hninv Hep Htok
  iintro %st ⟨%hb, %hc, %hrv', %hyl⟩ Hst
  subst hb
  have hpre : st.preAt st.ballot y = none := by
    have := congrArg Prod.fst hrv'; rw [← hrv.1]; exact this.symm
  have hpath : st.pathAt st.ballot y = none := by
    have := congrArg (fun v : swift.RowV => v.2.1) hrv'; rw [← hrv.2]; exact this.symm
  iapply (sp.upd_preaccept' (⊤ \ ↑swift.nodeN) swift.nodeN_diff N fr l r k st y s B D P hr hk hAQ hy
    hD hB hlast hLP hP hpre hpath W')
  iframe Hinv Hcfg Hst Hlb Hpre
  iunfold swift.baseIs at HB
  icases HB with (%H | ⟨%M, #HM, %HBM⟩)
  · ileft; ipureintro; exact H
  · iright; iexists M; iframe HM; ipureintro; exact HBM

/-- **A commit from `y`'s descriptor**, the acceptance case by its persistent fact: as
`commit_dstep`, through `upd_commit'`. -/
theorem swift.commit_dstep' (γ : sp.Names) (γc γm γl γv γe γo : GName) {sn : swift.StN} (N r k : Nat) (fr : Bool)
    (l : List GoString) (q : Qp) (b : Nat) (y : sp.CmdId) (rv : swift.RowV)
    (hr : r < N) (hk : nodeOf l r = some k) (hrv : rv.2.2.2 = false) (W' : List w64) :
    sp.inv γ γc γm γl ∗ sp.cfg γc γm N fr l ∗ inv swift.nodeN (swift.nodeInvD γ γv γe γo sn k) ∗
      swift.epochTok γe q (b, b) ∗ swift.rowTok γo b y rv ∗
      (⌜r = sp.leaderOf N b⌝ ∨ sp.accepted γ r b y ∨
        ∃ M, sp.syncIs γ b M ∗ ⌜y ∈ sp.syncOrder M⌝) ∗
      sp.predPre γ k (some (sp.PEv.commit b y, W')) ⊢
    |={⊤}=> swift.epochTok γe q (b, b) ∗ swift.rowTok γo b y (rv.1, rv.2.1, rv.2.2.1, true) ∗
      (sp.predPost γ k (some (sp.PEv.commit b y, W')) ∗ sp.committed γ r b y) := by
  iintro ⟨#Hinv, #Hcfg, #Hninv, Hep, Htok, #Hw, Hpre⟩
  iapply (swift.desc_upd γ γv γe γo k q b y rv (rv.1, rv.2.1, rv.2.2.1, true)
    (fun st => st.committed b y) iprop(sp.predPost γ k (some (sp.PEv.commit b y, W')) ∗
      sp.committed γ r b y)
    (fun _ => rfl) (fun _ => rfl) (fun st _ _ hacc => hacc)
    (fun st hrv' b' y' => by rw [swift.rowsOf_committed, ← hrv']))
  iframe Hninv Hep Htok
  iintro %st ⟨%hb, %hc, %hrv', %hyl⟩ Hst
  subst hb
  have hnot : (st.ballot, y) ∉ st.comR := by
    intro h
    have := congrArg (fun v : swift.RowV => v.2.2.2) hrv'
    simp only [swift.rowsOf] at this
    rw [hrv] at this
    exact absurd h (by simpa using this)
  iapply (sp.upd_commit' (⊤ \ ↑swift.nodeN) swift.nodeN_diff N fr l r k st y hr hk hyl hnot W')
  iframe Hinv Hcfg Hst Hw Hpre

end lemmas

end Perennial.github_com.imdea_software.swiftpaxos
