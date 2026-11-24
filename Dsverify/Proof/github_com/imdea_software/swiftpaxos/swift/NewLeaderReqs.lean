/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/NewLeaderReqs.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
**Phase 4 (round N2, sv-swc): the descriptor side's statements `fillNewLeaderAckN` needs**
(D56: N1-R1, N1-R2; notes/swift-shared-changes.md "Round N2 requests").

`fillNewLeaderAckN` (recovery.go:417) reports the replica's entries of its `cballot` `c`, from
four collections: the execution log (`execLog`, under `execL`), the last `MSync`, the stopped
descriptors (`cmdDescs`, `IterCb`), and the pending proposals (`proposes`, skipping
`delivered`'s). `sp.upd_report` (Steps.lean) needs, for the report `R`, each entry's witness
(`sp.entryWit`) and the pure facts h4-h9 of the node state. The run loop knows the last `MSync`
and `proposes`/`handled` (`localOk`); what it cannot know is what the descriptors and the
delivery left: the execution log's and the stopped descriptors' entries and what they cover.

* `swift.repEntW`: a report entry's witness without the node state (`sp.entryWit` with the
  replica's pre-acceptance as its persistent `sp.preacc` fragment; `swift.repEntW_entryWit`
  turns it into `entryWit` once the node state is at hand, over `sp.preacc_own`).
* `swift.coverOk`: the pure coverage of `c`'s rows by the execution log's entries `XS` and the
  stopped descriptors' entries `S` (with the base `B`, the last `MSync`'s order), and `delivered`'s
  commands `dl` among `XS`'s.
* **`swift.N1R1`** (structure, data and laws). Round 51 (D70 (1)): no snapshot; frame lemmas
  over the exclusive pieces the run loop holds while it runs `fillNewLeaderAckN`, each given
  back: the frozen record `Fz c X` (from the stopped epoch's pin half, `freeze`/`thaw`),
  `execL`'s contents (`exec`), one entry of the stopped view (`desc`, keyed), `delivInv`'s body
  (`deliv`). The epoch's identity is `recInvB`'s `epStoppedXc` `cballot` (NewLeaderSpecs.lean).
* **`swift.N1R2 R1`**: `coverOk` at the report, over `Fz`, the held reads and the node
  invariant's body.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.NewLeaderSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

/-- **The coverage of `c`'s rows** (see the file header; `sp.upd_report`'s h5, h6, h9 for the
entries `XS ++ S`, the rest of h5/h6 by the base `B`):
1. every entry is of `c`'s sequence, at most `COMMIT`, accepted or committed at `c` if its phase
   says so, agreeing with the replica's pre-acceptance and acceptance at `c`, and (phase `START`)
   its dependencies are of the sequence `s` of `c` before it;
2. every command accepted, committed or pre-accepted at `c` is an entry, or of the base;
3. the commands `delivered` has are entries of the execution log;
4. a stopped descriptor's `proposeDep` (`Pd`, by command) is of the dependencies of `s`. -/
def swift.coverOk (N r c : Nat) (st : sp.RState) (s : sp.Seq) (B : List sp.CmdId)
    (XS S : List sp.RepEntry) (dl : List sp.CmdId) (Pd : List (sp.CmdId × List sp.CmdId)) : Prop :=
  (∀ e ∈ XS ++ S, e.id ∈ st.locAt c ∧ e.phase.toNat ≤ 3 ∧
    (e.phase.toNat ≥ 2 → (c, e.id) ∈ st.accR ∨ (c, e.id) ∈ st.comR) ∧
    (∀ D, st.preAt c e.id = some D → e.phase.toNat ≥ 2 ∨ (e.phase.toNat = 1 ∧ e.dep = D)) ∧
    ((c, e.id) ∈ st.accR ∨ (c, e.id) ∈ st.comR →
      e.phase.toNat ≥ 2 ∨ (r = sp.leaderOf N c ∧ e.phase.toNat ≥ 1)) ∧
    (e.phase.toNat = 0 → ∀ d ∈ e.dep, d ∈ sp.depsIn s e.id)) ∧
  (∀ y, (c, y) ∈ st.accR ∨ (c, y) ∈ st.comR ∨ (st.preAt c y).isSome →
    y ∈ (XS ++ S).map (·.id) ∨ y ∈ B) ∧
  (∀ y ∈ dl, y ∈ XS.map (·.id)) ∧
  (∀ p ∈ Pd, ∀ d ∈ p.2, d ∈ sp.depsIn s p.1)

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions]

/-- **A report entry's witness, state-free** (see the file header): `sp.entryWit` with the
`PRE_ACCEPT` disjunct's `st.preAt c e.id = some e.dep` as `sp.preacc γ r c e.id e.dep`. -/
def swift.repEntW (γ : sp.Names) (N r c : Nat) (e : sp.RepEntry) : IProp netDistGF :=
  iprop(sp.cmdIs γ e.id e.cmd ∗
    (⌜e.phase.toNat = 0⌝ ∨ (⌜e.phase.toNat = 1⌝ ∗ sp.preacc γ r c e.id e.dep) ∨
      (⌜e.phase.toNat ≥ 2 ∨ r = sp.leaderOf N c⌝ ∗ ∃ s' : sp.Seq,
        sp.locLb γ (sp.leaderOf N c) c s' ∗
        ⌜e.id ∈ s'.map Prod.fst ∧ e.dep.Perm (sp.depsIn s' e.id)⌝)))

instance swift.repEntW_persistent (γ : sp.Names) (N r c : Nat) (e : sp.RepEntry) :
    Persistent (swift.repEntW γ N r c e) := by
  unfold swift.repEntW; infer_instance

/-- A stopped descriptor's fields that `fillNewLeaderAckN` reads (`propose`, `phase`, `cmd`,
`dep`, `proposeDep`), at fraction `q`, with the values `p ph op key vs dsl D pdsl PD`. Round 51
(50-5, N4's R1-b): the two slices' contents read-only (`↦*□`: the report aliases them). -/
def swift.descRepFields (d : Loc) (q : Iris.Qp) (p : Loc) (ph : w64) (op : w8) (key : w64)
    (vs dsl pdsl : GoSlice) (D PD : List swift.CommandId) : IProp netDistGF :=
  iprop(typedPointsto (swift.dfld d go!"propose") p (DFrac.own q) ∗
    typedPointsto (swift.dfld d go!"phase") ph (DFrac.own q) ∗
    typedPointsto (swift.dfld d go!"cmd") (state.Command.mk op key vs) (DFrac.own q) ∗
    typedPointsto (swift.dfld d go!"dep") dsl (DFrac.own q) ∗ dsl ↦*□ D ∗
    typedPointsto (swift.dfld d go!"proposeDep") pdsl (DFrac.own q) ∗ pdsl ↦*□ PD)

/-- **A stopped descriptor's read** (round 51, D70 (1)): its key `k` in the stopped view, its
location `d`, the fraction `q` and the values `fillNewLeaderAckN` reads; `y`/`c` are the
proposal's command id and command (meaningful when `p ≠ null`). -/
structure swift.DescRead where
  k : GoString
  d : Loc
  q : Iris.Qp
  p : Loc
  ph : w64
  op : w8
  key : w64
  vs : GoSlice
  dsl : GoSlice
  pdsl : GoSlice
  D : List swift.CommandId
  PD : List swift.CommandId
  y : sp.CmdId
  c : sp.Cmd

/-- The read's fields (`swift.descRepFields` at the read's values). -/
abbrev swift.DescRead.fields (r : swift.DescRead) : IProp netDistGF :=
  swift.descRepFields r.d r.q r.p r.ph r.op r.key r.vs r.dsl r.pdsl r.D r.PD

/-- **A read's claim** (round 59, D84 (2)): with a proposal, the stored home's claim on its rest
record of the stopped ballot `c` at the read's command (`descRestH`'s `K = (c, y)`; a home with a
proposal is stored, `descRestT` has `propose = null`). `R1.desc` hands it out with the read's
fields, and the report holds it until after N1-R2, which finds the read's own record by it
(clause 1: the record's `rowPhaseOk` at the read's values). -/
def swift.rdCl (γcl : GName) (c : Nat) (r : swift.DescRead) : IProp netDistGF :=
  iprop(⌜r.p = null⌝ ∨ ∃ γi : GName, swift.claimTok γcl (c, r.y) (.rest r.d γi))

/-- The read's report entry: none without a proposal. -/
def swift.DescRead.entry (r : swift.DescRead) : Option sp.RepEntry :=
  if r.p = null then none else some ⟨r.y, r.ph, r.c, r.D.map toCmdId⟩

/-- The descriptors' context at `x`'s names (`recInvB`'s first conjunct; persistent). -/
abbrev swift.descCtxX (γ : sp.Names) (γc γm : GName) (x : swift.RunX) (rp : Loc) :
    IProp netDistGF :=
  swift.descCtxE γ γc γm x.γl x.γw x.γv x.γe x.γo x.γx x.γxe x.γxm x.γxp x.γxu x.γrp x.γcg x.γout x.γcl
    x.γdc x.γdl x.str rp x.rr x.N x.r x.k

end defs

section lemmas
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions]

/-- `repEntW` is `sp.entryWit` at the replica's node state (`sp.preacc_own`). -/
theorem swift.repEntW_entryWit (E : CoPset) (hE : ↑sp.spN ⊆ E) (γ : sp.Names) (γc γm γl : GName)
    (N : Nat) (fr : Bool) (l : List GoString) (r k c : Nat) (st : sp.RState) (e : sp.RepEntry)
    (hr : r < N) (hk : nodeOf l r = some k) :
    sp.inv γ γc γm γl ∗ sp.cfg γc γm N fr l ∗ sp.nodeSt γ k (1 : Iris.Qp).half st ∗
      swift.repEntW γ N r c e ⊢
      |={E}=> sp.nodeSt γ k (1 : Iris.Qp).half st ∗ sp.entryWit γ N r c st e := by
  iintro ⟨#Hinv, #Hcfg, Hst, #Hw⟩
  iunfold swift.repEntW at Hw
  icases Hw with ⟨#Hc, (%h0 | ⟨%h1, #Hpre⟩ | ⟨%h2, %s', #Hlb, %hs⟩)⟩
  · imodintro
    iframe Hst
    iunfold sp.entryWit
    iframe Hc
    ileft; ipureintro; exact Or.inl h0
  · imod sp.preacc_own (γ := γ) (γc := γc) (γm := γm) (γl := γl) E hE N fr l r k st c e.id e.dep
      hr hk $$ [Hst] with ⟨Hst, %hp⟩
    · iframe Hinv Hcfg Hst Hpre
    imodintro
    iframe Hst
    iunfold sp.entryWit
    iframe Hc
    ileft; ipureintro; exact Or.inr ⟨h1, hp⟩
  · imodintro
    iframe Hst
    iunfold sp.entryWit
    iframe Hc
    iright
    isplitr
    · ipureintro; exact h2
    iexists s'
    iframe Hlb
    ipureintro; exact hs

end lemmas

section reqs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions]

/-- **A stopped descriptor's read facts** (round 51; persistent): no proposal, or the proposal
behind its `*GPropose` (N4's R1-a, as `propIs`), of the read's command id `y` keyed by the view's
key (`str y = k`, 50-6), its command's value slice, and the entry's facts `W`; and (N4's R1-c) the
`proposeDep`'s facts for the key's command, whether or not `propose` is set. Round 54 (D74 (1),
53-3): `W` only when `y` is not a command of the frozen record `Xi` (a delivered follower does not
adopt the leader's dependencies, swift.go:643; such a read is never reported: `IterCb`'s `seen`
has the log's ids, `delivered` ⊆ `X`). Round 54 (D76, N6's request (2)): a `START` read's
dependencies are fewer than `2^62`. -/
def swift.descReadOk (str : swift.CommandId → GoString) (Xi : List sp.CmdId)
    (W : sp.RepEntry → IProp netDistGF)
    (Wd : sp.CmdId → List sp.CmdId → IProp netDistGF) (r : swift.DescRead) : IProp netDistGF :=
  iprop((⌜r.p = null⌝ ∨ ∃ (pp w mu : Loc) (addr : GoString) (vs' : GoSlice) (ts : w64),
      r.p ↦□ replica.defs.GPropose.mk pp w mu false addr ∗
      pp ↦□ replica.defs.Propose.mk r.y.seq r.y.cl (state.Command.mk r.c.op r.c.key vs') ts ∗
      ⌜r.op = r.c.op ∧ r.key = r.c.key ∧ str (ofCmdId r.y) = r.k ∧
        (r.ph = W64 0 → r.D.length < 2 ^ 62)⌝ ∗ r.vs ↦*□ r.c.val ∗
      (⌜r.y ∈ Xi⌝ ∨ W ⟨r.y, r.ph, r.c, r.D.map toCmdId⟩)) ∗
    (⌜r.pdsl = slice.nil⌝ ∨ ∀ z : sp.CmdId, ⌜str (ofCmdId z) = r.k⌝ -∗ Wd z (r.PD.map toCmdId)))

/-- A read's key fact (round 52, N4's 50-6 request, keyed form): with a proposal, the read's
command is the key's (`descReadOk`'s `str (ofCmdId r.y) = r.k`). -/
theorem swift.descReadOk_key (str : swift.CommandId → GoString) (Xi : List sp.CmdId)
    (W : sp.RepEntry → IProp netDistGF)
    (Wd : sp.CmdId → List sp.CmdId → IProp netDistGF) (r : swift.DescRead) :
    swift.descReadOk str Xi W Wd r ⊢ ⌜r.p ≠ null → str (ofCmdId r.y) = r.k⌝ := by
  iintro H
  iunfold swift.descReadOk at H
  icases H with ⟨(%Hn | ⟨%pp, %w, %mu, %addr, %vs', %ts, -, -, %Hk, -⟩), -⟩
  · ipureintro; intro h; exact absurd Hn h
  · ipureintro; intro _; exact Hk.2.2.1

/-- **Every entry of `S` sits under a key of the stopped view** (round 52, N4's 50-6 request,
keyed form): the reads `SR` taken at keys of `Mc` (`desc`'s `r.k = k`), each with its key fact
(`swift.descReadOk_key`), and `S` the reads' entries. -/
theorem swift.S_keyed (str : swift.CommandId → GoString) (Mc : GMap GoString GoInterface)
    (SR : List swift.DescRead) (S : List sp.RepEntry)
    (hk : ∀ r ∈ SR, (Mc !! r.k).isSome) (hy : ∀ r ∈ SR, r.p ≠ null → str (ofCmdId r.y) = r.k)
    (hS : ∀ e ∈ S, ∃ r ∈ SR, r.entry = some e) :
    ∀ e ∈ S, (Mc !! str (ofCmdId e.id)).isSome := by
  intro e he
  obtain ⟨r, hr, hre⟩ := hS e he
  unfold swift.DescRead.entry at hre
  by_cases hp : r.p = null
  · rw [if_pos hp] at hre; cases hre
  · rw [if_neg hp] at hre
    cases hre
    rw [hy r hr hp]; exact hk r hr

/-- **The reads' entries** (round 54, D76, N6's request (1); pure): with frame lemmas there is no
snapshot, so `S` is the run loop's: the entries of the reads it reports (`IterCb` visits every key
of the stopped view once; a read whose id is `seen` is reported from the log or the `MSync`). Over
all reads `SR`, every read with `propose` set has its entry in `SR.filterMap DescRead.entry` (the
direction N1-R2's `∀ e ∈ S, ∃ r ∈ SR, r.entry = some e` does not give), and conversely. -/
theorem swift.S_complete (SR : List swift.DescRead) :
    (∀ r ∈ SR, r.p ≠ null → ∃ e ∈ SR.filterMap swift.DescRead.entry, r.entry = some e) ∧
    (∀ e ∈ SR.filterMap swift.DescRead.entry, ∃ r ∈ SR, r.entry = some e) := by
  refine ⟨fun r hr hp => ?_, fun e he => ?_⟩
  · have he : r.entry = some ⟨r.y, r.ph, r.c, r.D.map toCmdId⟩ := by
      unfold swift.DescRead.entry; rw [if_neg hp]
    exact ⟨_, List.mem_filterMap.mpr ⟨r, hr, he⟩, he⟩
  · obtain ⟨r, hr, he⟩ := List.mem_filterMap.mp he
    exact ⟨r, hr, he⟩

/-- Two whole points-to's of one field (round 58; `swift.loc_pt_excl`'s argument). -/
theorem swift.pt_excl_loc (l : Loc) (a b : Loc) :
    typedPointsto l a (DFrac.own 1) ∗ typedPointsto l b (DFrac.own 1) ⊢ (False : IProp netDistGF) := by
  simp only [typedPointsto_unseal, typedPointstoWrap, typedPointstoDef_heap]
  iintro ⟨⟨N1', -⟩, ⟨N2', -⟩⟩
  icombine N1' N2' gives %Hv
  exfalso; have := DFrac.valid_own_op Hv.1; simp at this

/-- **The stopped view is injective** (round 58, D82 (1)): two keys with the same descriptor `d`
would give two `descFree DF d`, each owning `d`'s `msgs` whole. -/
theorem swift.descsMap_inj (DF : Loc → IProp netDistGF) (Mc : GMap GoString GoInterface)
    (k k' : GoString) (d : Loc)
    (hk : Mc !! k = some (interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #d))
    (hk' : Mc !! k' = some (interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #d)) :
    ([∗map] _k ↦ v ∈ Mc, ∃ d : Loc,
      ⌜v = interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #d⌝ ∗ swift.descFree DF d) ⊢
      ⌜k' = k⌝ := by
  by_cases h : k' = k
  · exact BI.pure_intro h
  iintro H
  icases (BigSepM.bigSepM_delete hk).1 $$ H with ⟨⟨%d1, %h1, H1⟩, H⟩
  have hk2 : (GMap.delete k Mc) !! k' =
      some (interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #d) := by
    rw [GMap.lookup_delete_ne _ (Ne.symm h)]; exact hk'
  icases (BigSepM.bigSepM_delete hk2).1 $$ H with ⟨⟨%d2, %h2, H2⟩, -⟩
  have e1 : d = d1 := swift.mkOk_desc_inj _ _ h1
  have e2 : d = d2 := swift.mkOk_desc_inj _ _ h2
  subst e1 e2
  iunfold swift.descFree at H1 H2
  icases H1 with ⟨%m1, %s1, %sl1, %fa1, Hm1, -⟩
  icases H2 with ⟨%m2, %s2, %sl2, %fa2, Hm2, -⟩
  iexfalso
  iapply swift.pt_excl_loc _ m1 m2
  iframe

/-- `swift.descsMap_inj` for every pair of keys (round 58). -/
theorem swift.descsMap_injAll (DF : Loc → IProp netDistGF) (Mc : GMap GoString GoInterface) :
    ([∗map] _k ↦ v ∈ Mc, ∃ d : Loc,
      ⌜v = interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #d⌝ ∗ swift.descFree DF d) ⊢
      ⌜∀ (k k' : GoString) (d : Loc),
        Mc !! k = some (interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #d) →
        Mc !! k' = some (interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #d) →
        k' = k⌝ := by
  refine (BI.forall_intro fun k => BI.forall_intro fun k' => BI.forall_intro fun d => ?_).trans
    ((BI.forall_mono fun _ => (BI.forall_mono fun _ => BI.pure_forall.2).trans
      BI.pure_forall.2).trans BI.pure_forall.2)
  by_cases hk : Mc !! k = some (interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #d)
  · by_cases hk' : Mc !! k' = some (interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #d)
    · exact (swift.descsMap_inj DF Mc k k' d hk hk').trans (BI.pure_mono fun h _ _ => h)
    · exact BI.pure_intro (fun _ h => absurd h hk')
  · exact BI.pure_intro (fun h _ => absurd h hk)

/-- **N1-R1 (descriptor side; D56), round 51 (D70 (1)): frame lemmas.** No snapshot: each read
lemma takes the exclusive pieces the run loop holds while it runs `fillNewLeaderAckN` and gives
them back. The stopped epoch's identity is the `cballot` `c` of `recInvB`'s `epStoppedXc`.
* `Fz c X` (exclusive): the stopped epoch `c` with its execution record `X` frozen
  (lifecycle-table 11b.10-11b.11, 51-1). `freeze` takes it from the stopped epoch's pin half
  (the `γxp` half of `epStoppedXc`), `thaw` gives the half back; `fillNewLeaderAckN` holds `Fz`
  from its start to its end. Round 52 (D71 (1)): implemented as `delivInv`'s frozen mode
  (NewLeaderDesc.lean's `swift.fzX`); the statement is unchanged.
* `W c e`, `Wd c z D` (persistent): a read entry's facts (`W_wit`: its report witness
  `repEntW`), and a `proposeDep`'s facts. N1-R2 consumes them. Round 58 (D82 (3)): `WX c e`
  (persistent), a log entry's own facts (from its `exEntOk`), which `exec` gives per entry of `XS`
  and N1-R2 takes besides `W`.
* `exec`: on `execL`'s contents (the record's half of `γx`, its entries' `exEntOkE`): the record
  is `Fz`'s, and the log's entries `XS` (ids those of `X`) with their facts.
* `desc`: on ONE entry of the stopped view (`descFree DF d`, the key `k`): the read fields
  (lent; the run loop keeps them until after the report: they pin the read values, 11b.10
  51-3) and the read's facts (`swift.descReadOk`). Round 57 (D80 (4)): with the stopped view `Mc`
  at `k` and the stopped epoch's commit record and registration (`swift.stopPS`'s first part,
  given back), for a stored home's key fact. Round 58 (D82 (1)): the home at the stopped ballot
  `c` (`x.DR γ c`), and the view injective at `d` (`swift.descsMap_inj`: each entry's `descFree`
  owns `msgs` whole).
* `deliv`: on `delivInv`'s body (opened by `delivered.Has`'s atomic update): `delivered`'s
  commands are `X`'s.
* `Wd_seq` (round 54, D76, N6's request (3)): a `proposeDep`'s facts against the run loop's
  sequence `s` of `c` (its `locLb`, `bs ++ hd`): when `s` has `z`, the dependencies are of
  `depsIn s z`, and fewer than `2^62` (R1-a's key-to-command link is `descReadOk`'s
  `str (ofCmdId z) = r.k`). -/
structure swift.N1R1 (rp : Loc) (γ : sp.Names) (γc γm : GName) (x : swift.RunX) : Type where
  Fz : Nat → List swift.ExE → IProp netDistGF
  W : Nat → sp.RepEntry → IProp netDistGF
  Wd : Nat → sp.CmdId → List sp.CmdId → IProp netDistGF
  W_pers : ∀ c e, Persistent (W c e)
  Wd_pers : ∀ c z D, Persistent (Wd c z D)
  WX : Nat → sp.RepEntry → IProp netDistGF
  WX_pers : ∀ c e, Persistent (WX c e)
  W_wit : ∀ c e, W c e ⊢ swift.repEntW γ x.N x.r c e
  freeze : ∀ c : Nat, swift.descCtxX γ γc γm x rp ∗ ghostVar x.γxp (1 : Iris.Qp).half c ⊢
    |={⊤}=> ∃ X : List swift.ExE, Fz c X
  thaw : ∀ (c : Nat) (X : List swift.ExE), swift.descCtxX γ γc γm x rp ∗ Fz c X ⊢
    |={⊤}=> ghostVar x.γxp (1 : Iris.Qp).half c
  exec : ∀ (c : Nat) (X : List swift.ExE) (es : List swift.commandStaticDesc) (bX : Nat)
      (X' : List swift.ExE), es.length = X'.length →
    swift.descCtxX γ γc γm x rp ∗ Fz c X ∗ ghostVar x.γx (1 : Iris.Qp).half (bX, X') ∗
      ([∗list] i ↦ e ∈ X', ∃ esi : swift.commandStaticDesc, ⌜es[i]? = some esi⌝ ∗
        swift.exEntOkE γ x.N x.r bX e esi) ⊢
      |={⊤}=> Fz c X ∗ ghostVar x.γx (1 : Iris.Qp).half (bX, X') ∗ ⌜bX = c ∧ X' = X⌝ ∗
        ∃ XS : List sp.RepEntry,
          ⌜XS.length = es.length ∧ XS.map (·.id) = X.map (fun e => toCmdId e.1)⌝ ∗
          ([∗list] i ↦ esi ∈ es, ∃ (e : sp.RepEntry) (vs : GoSlice),
            ⌜XS[i]? = some e ∧ toCmdId esi.cmdId' = e.id ∧
              (if sint.Z esi.phase' < 1 then 1 else (sint.Z esi.phase').toNat) = e.phase.toNat ∧
              esi.cmd' = state.Command.mk e.cmd.op e.cmd.key vs⌝ ∗ vs ↦*□ e.cmd.val ∗
            ∃ D : List swift.CommandId, esi.dep' ↦*□ D ∗ ⌜D.map toCmdId = e.dep⌝) ∗
          ([∗list] e ∈ XS, W c e) ∗ [∗list] e ∈ XS, WX c e
  desc : ∀ (c : Nat) (X : List swift.ExE) (k : GoString) (d : Loc) (Mc : GMap GoString GoInterface),
    Mc !! k = some (interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #d) →
    (∀ k', Mc !! k' = some (interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #d) → k' = k) →
    Function.Injective x.str →
    swift.descCtxX γ γc γm x rp ∗ Fz c X ∗
      (▷ ∃ g : swift.DescG, swift.incInv g Mc ∗ ⌜g.ev.b = c⌝ ∗ swift.cgG x g) ∗
      swift.descFree (swift.descDF (x.DR γ c)) d ⊢
      |={⊤}=> Fz c X ∗ (▷ ∃ g : swift.DescG, swift.incInv g Mc ∗ ⌜g.ev.b = c⌝ ∗ swift.cgG x g) ∗
        ∃ r : swift.DescRead, ⌜r.k = k ∧ r.d = d⌝ ∗ r.fields ∗ swift.rdCl x.sn.γcl c r ∗
        (r.fields -∗ swift.rdCl x.sn.γcl c r -∗ swift.descFree (swift.descDF (x.DR γ c)) d) ∗
        swift.descReadOk x.str (X.map (fun e => toCmdId e.1)) (W c) (Wd c) r
  deliv : ∀ (c : Nat) (X : List swift.ExE) (γa γrm : GName),
    Function.Injective x.str →
    Fz c X ∗ swift.delivInv γ x.N x.r x.γdl x.γx x.γxp x.γxm γa x.γxe γrm x.str ⊢
      Fz c X ∗ ∃ M : GMap GoString GoInterface,
        github_com.orcaman.concurrent_map.cmapView x.γdl M ∗
        (github_com.orcaman.concurrent_map.cmapView x.γdl M -∗
          swift.delivInv γ x.N x.r x.γdl x.γx x.γxp x.γxm γa x.γxe γrm x.str) ∗
        ⌜∀ y : sp.CmdId, (M !! x.str (ofCmdId y)).isSome →
          y ∈ X.map (fun e => toCmdId e.1)⌝
  Wd_seq : ∀ (c : Nat) (z : sp.CmdId) (D : List sp.CmdId) (s : sp.Seq),
    swift.descCtxX γ γc γm x rp ∗ Wd c z D ∗ sp.locLb γ x.r c s ⊢
      |={⊤}=> ⌜z ∈ s.map Prod.fst → (∀ d ∈ D, d ∈ sp.depsIn s z) ∧ D.length < 2 ^ 62⌝

/-- **The node invariant's body** at the state `st` and the rows `O` (round 49, gap 49-6: what
the run loop holds once it has opened `nodeInvD` at `x`'s names for `upd_report`; `nodeSt`, the
view's and the epoch's halves, the rows' authority, the store and the pure part). -/
abbrev swift.nodeBody (γ : sp.Names) (x : swift.RunX) (st : sp.RState)
    (O : GMap (Nat × sp.CmdId) swift.RowV) : IProp netDistGF :=
  iprop(sp.nodeSt γ x.k (1 : Iris.Qp).half st ∗
    ghostVar x.γv (1 : Iris.Qp).half (swift.viewOf st) ∗
    ghostVar x.γe (1 : Iris.Qp).half (swift.epochOf st) ∗ ghostMapAuth x.γo 1 O ∗
    swift.storeD γ x.γo x.sn st.cballot O ∗
    ⌜(∀ b y, (b, y) ∈ st.accR → b ≤ st.cballot) ∧ swift.rowsOk st O⌝)

/-- **N1-R2 (descriptor side; D56)**, round 51 (D70 (1)): at the report (`upd_report`'s
`nodeInvD` opening, the body `swift.nodeBody`), with the frozen epoch `Fz c X`, the log's entries
`XS` (ids `X`'s), the reads `SR` of the stopped view `Mc` (every key read, 50-6; their fields still
held: they pin the read values, 11b.10 51-3), the entries `S` of the reads, the `proposeDep`s
`Pd` read at the keys of their commands (N4's R1-c), and `delivered`'s commands `dl` among `X`'s:
the coverage `swift.coverOk`, and (N4's R2-a) a log entry of the base is reported as the
`MSync` `M0` has it. Round 53: with the replica's `locLb` of its sequence `s` of `c` (the one
`upd_report` takes; clause 4 compares `pdW`'s prefixes with it, `swift.pd_deps`), and every read's
entry reported (`IterCb` skips only `seen` ids: the log's, the `MSync`'s, earlier reads'; for the
rest records of clause 2). Round 56 (R2-a): the base with the ballot's leader's `locLb` of
`syncSeq M` (`syncObj`'s, `msgOk (.sync)`). Round 56 (D79 (1), 52-3): with the stopped epoch's commit record and
its registration (`swift.stopPS`'s first part, given back), the reads' key facts (`descReadOk`'s
`str (ofCmdId r.y) = r.k`) and `str` injective: a rest record's incarnation is live in the stopped
view at its command's key, so its read reports it (clause 2). Round B1 (D82 (4)): with the stopped
epoch's free permit, unspent (given back): a `released` record of `c` holds it spent
(`retWhy .released`), so there is none (clause 2). Round 59 (D84 (2)): with the reads' claims
(`swift.rdCl`, given back): a read with a proposal finds its own rest record (clause 1). -/
abbrev swift.N1R2 (rp : Loc) (γ : sp.Names) (γc γm : GName) (x : swift.RunX)
    (R1 : swift.N1R1 rp γ γc γm x) : Prop :=
  ∀ (E : CoPset), ↑swift.nodeN ⊆ E → ↑sp.spN ⊆ E \ ↑swift.nodeN →
    ↑swift.delivN ⊆ E \ ↑swift.nodeN → ∀ (c : Nat) (X : List swift.ExE) (XS S : List sp.RepEntry) (SR : List swift.DescRead)
    (γdc : GName) (Mc : GMap GoString GoInterface) (dl : List sp.CmdId)
    (Pd : List (sp.CmdId × List sp.CmdId)) (st : sp.RState)
    (O : GMap (Nat × sp.CmdId) swift.RowV) (s : sp.Seq) (B : List sp.CmdId)
    (M0 : Option sp.SyncMsg),
    st.cballot = c → s.map Prod.fst = st.locAt c → B <+: st.locAt c →
    XS.map (·.id) = X.map (fun e => toCmdId e.1) →
    (∀ e ∈ S, ∃ r ∈ SR, r.entry = some e) →
    (∀ k v, Mc !! k = some v → ∃ r ∈ SR, r.k = k ∧
      v = interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #r.d) →
    (∀ p ∈ Pd, ∃ r ∈ SR, x.str (ofCmdId p.1) = r.k ∧ r.pdsl ≠ slice.nil ∧
      p.2 = r.PD.map toCmdId) →
    (∀ y ∈ dl, y ∈ X.map (fun e => toCmdId e.1)) →
    (∀ r ∈ SR, ∀ e, r.entry = some e → e.id ∈ (XS ++ S).map (·.id) ∨ e.id ∈ B) →
    (∀ r ∈ SR, r.p ≠ null → x.str (ofCmdId r.y) = r.k) → Function.Injective x.str →
    swift.descCtxX γ γc γm x rp ∗ R1.Fz c X ∗
      (▷ ∃ g : swift.DescG, swift.incInv g Mc ∗ ⌜g.ev.b = c⌝ ∗ swift.cgG x g) ∗
      swift.freeP x.γcg c ∗
      ghostMapAuth x.γout (1 : Iris.Qp).half (∅ : GMap (Nat × sp.CmdId) (Nat × Iris.Qp)) ∗
      github_com.orcaman.concurrent_map.cmapView γdc Mc ∗ ([∗list] r ∈ SR, r.fields) ∗
      ([∗list] r ∈ SR, swift.rdCl x.sn.γcl c r) ∗
      ([∗list] e ∈ XS ++ S, R1.W c e) ∗ ([∗list] e ∈ XS, R1.WX c e) ∗
      ([∗list] p ∈ Pd, R1.Wd c p.1 p.2) ∗
      (⌜c = 0 ∧ B = [] ∧ M0 = none⌝ ∨
        ∃ M : sp.SyncMsg, ⌜M0 = some M⌝ ∗ sp.syncIs γ c M ∗
          sp.locLb γ (sp.leaderOf x.N c) c (sp.syncSeq M) ∗ ⌜B = sp.syncOrder M⌝) ∗
      sp.locLb γ x.r c s ∗ swift.nodeBody γ x st O ⊢
      |={E \ ↑swift.nodeN}=> R1.Fz c X ∗
        (▷ ∃ g : swift.DescG, swift.incInv g Mc ∗ ⌜g.ev.b = c⌝ ∗ swift.cgG x g) ∗
        swift.freeP x.γcg c ∗
        ghostMapAuth x.γout (1 : Iris.Qp).half (∅ : GMap (Nat × sp.CmdId) (Nat × Iris.Qp)) ∗
        github_com.orcaman.concurrent_map.cmapView γdc Mc ∗ ([∗list] r ∈ SR, r.fields) ∗
        ([∗list] r ∈ SR, swift.rdCl x.sn.γcl c r) ∗
        swift.nodeBody γ x st O ∗
        ⌜swift.coverOk x.N x.r c st s B XS S dl Pd ∧
          ∀ M, M0 = some M → ∀ e ∈ XS, e.id ∈ B →
            e.phase.toNat = 3 ∧ ∃ p ∈ M, p.1 = e.id ∧ e.dep.Perm p.2.2⌝

end reqs

end Perennial.github_com.imdea_software.swiftpaxos

end
