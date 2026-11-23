/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/DeliverE.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
**SWC-2, round S2** (notes/prove-swift.md §52): `deliver` against the reply channel's real object
`swift.RCh` and `reply.specE`. This replaces `deliver.specI` (Deliver.lean), which stays with its
proof until the descriptor side switches over (D54).

* **The execution ticket** `swift.xTix γxu b x` (D-SWC2-3): an exclusive ghost-map element at the
  key `(b, toCmdId x)`, the same key as the row token's. `deliver` consumes it when it executes
  `x`. The lock invariant then keeps the ticket of every executed command, so a ticket held by
  `deliver` proves `x` is not executed yet in `b`: that is the record's `Nodup`. One ghost map
  `γxu` covers every epoch, because its keys carry the ballot. The tickets are minted from the
  authority `swift.xuAuth γxu U` (`swift.xTix_mint`), together with the row token (T28/T28b). The
  authority's home is the descriptor side's business: `nodeInvD`, next to the rows' authority
  `O`, with `dom U ⊆ dom O` (proposal D-SWC2-5, notes §52). It cannot live in `execLInv`,
  because T28 (`handleProposal`, `handleSync`) runs without `execL`.
* `swift.exEntOkE`: `exEntOk` with `exRepOk` (what the leader's reply needs of every executed
  entry).
* `swift.execLInvE`: `execLInv` with `exEntOkE`, the executed commands' tickets and `Nodup`.
* `swift.descCtxE`: `descCtx` (Deliver.lean) with `execL`'s invariant `execLInvE` and the ticket
  map `γxu`. At the switch-over it replaces `descCtx`; until then it is a separate copy, so the
  existing proofs keep `descCtx`.
* `swift.ldrPrefix`: at the ballot's leader, the leader's sequence prefix that has `x`, with `x`'s
  dependencies a permutation of `depsIn` there (`exRepOk`'s own part).
* `swift.Replica.deliver.specE`: the spec (proof: DeliverProofE.lean).
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.client.NodeGhost
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.ReplyDefs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable [swift.Assumptions]

/-- **The execution ticket** of `x` in epoch `b` (exclusive; see the file header). Round 46: the
key's ticket `swift.xTixK` (RetBase.lean, below the store, which keeps the tickets with the
tokens); the authority `swift.xuAuth` is there too. -/
def swift.xTix (γxu : GName) (b : Nat) (x : swift.CommandId) : IProp netDistGF :=
  swift.xTixK γxu (b, toCmdId x)

/-- **A follower's executed entry's leader facts** (rounds 53-54, D73 (1), D74 (2); 52-1, 53-4):
at `b`'s leader nothing (`exRepOk` has its own sequence); at a follower the leader's sequence with
the command and the executed dependencies (`depWhy`'s leader-prefix disjunct: the leader's ack's
`sp.locDeps`, or a sync entry's leader `locLb` of `syncSeq M`). From the descriptor's `depWhy` at
`COMMIT` (T15). -/
def swift.exFolW (γ : sp.Names) (N r b : Nat) (e : swift.ExE) : IProp netDistGF :=
  iprop(⌜r = sp.leaderOf N b⌝ ∨
    (∃ D : List sp.CmdId, sp.locDeps γ (sp.leaderOf N b) b (toCmdId e.1) D ∗
      ⌜(e.2.2.map toCmdId).Perm D⌝))

instance swift.exFolW_persistent (γ : sp.Names) (N r b : Nat) (e : swift.ExE) :
    Persistent (swift.exFolW γ N r b e) := by
  unfold swift.exFolW; infer_instance

/-- An execution-record entry's facts with the reply's (`exRepOk`). Round 52 (51-5, D71 (3);
49-4): with the command's registration `cmdIs` (from the descriptor's `repPre`'s `propIs`, T15),
for the report's witness (`swift.exec_wit`, NewLeaderDesc.lean). Round 53 (52-1): and at a
follower the leader's facts (`swift.exFolW`). -/
def swift.exEntOkE (γ : sp.Names) (N r b : Nat) (e : swift.ExE) (es : swift.commandStaticDesc) :
    IProp netDistGF :=
  iprop(swift.exEntOk γ N r b e es ∗ swift.exRepOk γ N r b e ∗ sp.cmdIs γ (toCmdId e.1) e.2.1 ∗
    swift.exFolW γ N r b e)

instance swift.exEntOkE_persistent (γ : sp.Names) (N r b : Nat) (e : swift.ExE)
    (es : swift.commandStaticDesc) : Persistent (swift.exEntOkE γ N r b e es) := by
  unfold swift.exEntOkE; infer_instance

/-- **`execL`'s lock invariant, SWC-2's form**: `execLInv` (Deliver.lean) with `exEntOkE`, the
tickets of the executed commands, and no command executed twice. -/
def swift.execLInvE (γ : sp.Names) (γx γxe γxm γxu : GName) (N r : Nat) (rp : Loc) :
    IProp netDistGF :=
  iprop(∃ (sl : GoSlice) (es : List swift.commandStaticDesc) (bX : Nat) (X : List swift.ExE)
      (stp : Loc),
    swift.fld rp go!"execLog" ↦ sl ∗ sl ↦* es ∗ ownSliceCap swift.commandStaticDesc sl (DFrac.own 1) ∗
    ghostVar γx (1 : Qp).half (bX, X) ∗ ghostVar γxe (1 : Qp).half (bX, stp) ∗
    state.ownState stp (swift.applyX X) ∗
    swift.exLb γxm bX X ∗
    ([∗list] i ↦ e ∈ X, ∃ esi : swift.commandStaticDesc, ⌜es[i]? = some esi⌝ ∗
      swift.exEntOkE γ N r bX e esi) ∗
    ([∗list] e ∈ X, swift.xTix γxu bX e.1) ∗
    ⌜es.length = X.length ∧ swift.depsBefore X ∧ (X.map Prod.fst).Nodup⌝)

/-- `descCtx` (Deliver.lean) with `execL`'s invariant `execLInvE` and the tickets' map `γxu`
(see the file header). -/
def swift.descCtxE (γ : sp.Names) (γc γm γl γw γv γe γo γx γxe γxm γxp γxu γrp γcg γout γcl : GName)
    (γdc : ChanNames) (γdl : GName) (str : swift.CommandId → GoString)
    (rp rr : Loc) (N r k : Nat) : IProp netDistGF :=
  iprop(∃ (me : w32) (fr : Bool) (l : List GoString) (dm : GoSlice) (dc : Loc) (ex dr oe : Bool)
      (γa γrm : GName) (rc : Loc) (γrc : ChanNames),
    swift.fld rp go!"Replica" ↦□ rr ∗ replica.isReplica rr γ γc γm γw N me ∗
    ⌜sp.rid me = r ∧ 0 ≤ sint.Z me ∧ r < N ∧ 1 ≤ N ∧ N ≤ 7 ∧ nodeOf l r = some k⌝ ∗
    replica.fld rr go!"Exec" ↦□ ex ∗ replica.fld rr go!"Dreply" ↦□ dr ∗
    swift.fld rp go!"optExec" ↦□ oe ∗
    sp.inv γ γc γm γl ∗ sp.cfg γc γm N fr l ∗
    inv swift.nodeN (swift.nodeInvD γ γv γe γo ⟨γxm, γout, γcl, str, N, r, γxu, γrp, γcg⟩ k) ∗
    swift.fld rp go!"delivered" ↦□ dm ∗
    github_com.orcaman.concurrent_map.isCMapV dm γdl swift.deliveredR ∗
    inv swift.delivN (swift.delivInv γ N r γdl γx γxp γxm γa γxe γrm str) ∗
    swift.fld rp go!"deliverChan" ↦□ dc ∗ isChanBag γdc dc (fun (_ : swift.CommandId) => iprop(True)) ∗
    sync.isMutex (swift.fld rp go!"execL") (swift.execLInvE γ γx γxe γxm γxu N r rp) ∗
    globalAddr swift.ExecHook ↦□ func.nil ∗
    sync.isMutex (swift.fld rp go!"acceptL") (swift.acceptInv γ r rp γa) ∗
    swift.fld rp go!"recheckChan" ↦□ rc ∗ isChanBag γrc rc (fun (_ : swift.CommandId) => iprop(True)) ∗
    swift.anyInv rp ∗
    -- L2 (notes/prove-s2-e.md): the node's claimed ghost, for its protocol steps' resolutions
    client.nodeGhostOk γ (sp.PNode.rep k))

set_option synthInstance.maxSize 32768 in
set_option synthInstance.maxHeartbeats 8000000 in
instance swift.descCtxE_persistent (γ : sp.Names)
    (γc γm γl γw γv γe γo γx γxe γxm γxp γxu γrp γcg γout γcl : GName)
    (γdc : ChanNames) (γdl : GName)
    (str : swift.CommandId → GoString) (rp rr : Loc) (N r k : Nat) :
    Persistent (swift.descCtxE γ γc γm γl γw γv γe γo γx γxe γxm γxp γxu γrp γcg γout γcl γdc γdl str rp rr N r k) := by
  unfold swift.descCtxE; infer_instance

/-- **The leader's prefix fact** for `x` (`exRepOk`'s own part; see the file header). -/
def swift.ldrPrefix (γ : sp.Names) (N r b : Nat) (x : swift.CommandId) (dv : swift.DescV) :
    IProp netDistGF :=
  iprop(⌜r ≠ sp.leaderOf N b⌝ ∨ ∃ s : sp.Seq, sp.locLb γ r b s ∗
    ⌜(toCmdId x, dv.c) ∈ s ∧ (dv.D.map toCmdId).Perm (sp.depsIn s (toCmdId x))⌝)

instance swift.ldrPrefix_persistent (γ : sp.Names) (N r b : Nat) (x : swift.CommandId)
    (dv : swift.DescV) : Persistent (swift.ldrPrefix γ N r b x dv) := by
  unfold swift.ldrPrefix sp.locLb; infer_instance

/-- **What `deliver` needs of the descriptor for the reply** (round 46, D-SWC2-6): nothing before
a proposal (`deliver` returns at once), else `replyPre`, the command well formed and the leader's
prefix fact. Round 52 (51-5, D71 (3); 49-3): and the proposal's `propIs` (its `*GPropose`, the
`Propose`, the value slice, `cmdIs`), which `descSt` thereby carries to the depositors (T19, T7e:
`stopFacts`) and to `deliver` (T15: `exEntOkE`'s `cmdIs`). -/
def swift.repPre (γ : sp.Names) (N r b : Nat) (x : swift.CommandId) (dv : swift.DescV) :
    IProp netDistGF :=
  iprop(⌜dv.propose = null⌝ ∨
    (swift.replyPre γ N r b x dv ∗ ⌜dv.c.wf⌝ ∗ swift.ldrPrefix γ N r b x dv ∗
      swift.propIs γ dv.propose (toCmdId x) dv.c))

/-- `repPre`'s proposal facts (round 52, 51-5): no proposal, or its `propIs`. -/
theorem swift.repPre_propIs (γ : sp.Names) (N r b : Nat) (x : swift.CommandId) (dv : swift.DescV) :
    swift.repPre γ N r b x dv ⊢ ⌜dv.propose = null⌝ ∨ swift.propIs γ dv.propose (toCmdId x) dv.c := by
  iintro H
  iunfold swift.repPre at H
  icases H with (%Hn | ⟨-, -, -, HpI⟩)
  · ileft; ipureintro; exact Hn
  · iright; iexact HpI

instance swift.repPre_persistent (γ : sp.Names) (N r b : Nat) (x : swift.CommandId)
    (dv : swift.DescV) : Persistent (swift.repPre γ N r b x dv) := by
  unfold swift.repPre; infer_instance

/-- **The owner's ticket at `deliver`** (round 46, D-SWC2-6; gap 46-1): nothing before a proposal,
else the ticket or `x`'s execution in `b` (a descriptor that executed `x` and is delivered again:
`deliver` returns at `delivered.Has`, by the owner's epoch pin). -/
def swift.tixD (γxu γxm : GName) (b : Nat) (x : swift.CommandId) (dv : swift.DescV) :
    IProp netDistGF :=
  iprop(⌜dv.propose = null⌝ ∨ swift.xTix γxu b x ∨ swift.exIn γxm b x)

/-- The key's ticket or use at `x`'s key, as `deliver` takes it (round 46). -/
theorem swift.tixOr_to (γxu γxm : GName) (b : Nat) (x : swift.CommandId) :
    swift.tixOr γxu γxm (b, toCmdId x) ⊢ swift.xTix γxu b x ∨ swift.exIn γxm b x := by
  iintro H
  iunfold swift.tixOr at H
  icases H with (H | ⟨%x', %hx, #He⟩)
  · ileft; iunfold swift.xTix; iexact H
  · have : x' = x := by
      have := congrArg ofCmdId hx
      simpa using this
    subst this
    iright; iexact He

/-- Back (round 46). -/
theorem swift.tixOr_of (γxu γxm : GName) (b : Nat) (x : swift.CommandId) :
    swift.xTix γxu b x ∨ swift.exIn γxm b x ⊢ swift.tixOr γxu γxm (b, toCmdId x) := by
  iintro H
  iunfold swift.tixOr
  icases H with (H | #He)
  · ileft; iunfold swift.xTix at H; iexact H
  · iright; iexists x; iframe He; ipureintro; rfl

/-- Two tickets of one key: impossible. -/
theorem swift.xTix_excl (γxu : GName) (b : Nat) (x y : swift.CommandId) (h : toCmdId x = toCmdId y) :
    swift.xTix γxu b x ∗ swift.xTix γxu b y ⊢ (False : IProp netDistGF) := by
  unfold swift.xTix swift.xTixK
  rw [h]
  iintro ⟨H1, H2⟩
  icombine H1 H2 gives %Hv
  exfalso; have := DFrac.valid_own_op Hv.1; simp at this

/-- **A held ticket: `x` is not executed** (the record keeps the executed ones' tickets). -/
theorem swift.xTix_notin (γxu : GName) (b : Nat) (X : List swift.ExE) (x : swift.CommandId) :
    ([∗list] e ∈ X, swift.xTix γxu b e.1) ∗ swift.xTix γxu b x ⊢
      ([∗list] e ∈ X, swift.xTix γxu b e.1) ∗ swift.xTix γxu b x ∗ ⌜x ∉ X.map Prod.fst⌝ := by
  by_cases hx : x ∈ X.map Prod.fst
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    iintro ⟨HX, Ht⟩
    ihave ⟨He, -⟩ := (BigSepL.bigSepL_mem_acc (Φ := fun e : swift.ExE => swift.xTix γxu b e.1) he) $$ HX
    iexfalso
    iapply swift.xTix_excl γxu b e.1 e.1 rfl
    iframe He Ht
  · iintro ⟨HX, Ht⟩
    iframe HX Ht
    ipureintro; exact hx

/-- **Minting a ticket** (with the row token, T28/T28b): a key not minted yet. -/
theorem swift.xTix_mint (γxu : GName) (U : GMap (Nat × sp.CmdId) Unit) (b : Nat)
    (x : swift.CommandId) (E : CoPset) (h : U.lookup (b, toCmdId x) = none) :
    swift.xuAuth γxu U ⊢ |={E}=> swift.xuAuth γxu (U.insert (b, toCmdId x) ()) ∗ swift.xTix γxu b x := by
  unfold swift.xuAuth swift.xTix swift.xTixK
  iintro Ha
  imod ghost_map_insert (γ := γxu) (b, toCmdId x) () h $$ Ha with ⟨Ha, Ht⟩
  imodintro
  iframe Ha Ht

/-- The tickets' authority, allocated empty (at the replica's start). -/
theorem swift.xuAuth_alloc (E : CoPset) :
    ⊢ |={E}=> ∃ γxu, swift.xuAuth γxu (∅ : GMap (Nat × sp.CmdId) Unit) := by
  unfold swift.xuAuth
  imod ghost_map_alloc_empty (GF := netDistGF) (K := Nat × sp.CmdId) (V := Unit) with ⟨%γxu, Ha⟩
  imodintro
  iexists γxu
  iexact Ha

/-- `execLInvE` at a new epoch's start (empty record): what `execLInv`'s reset gives, with no
ticket and `Nodup` trivially. -/
theorem swift.execLInvE_empty (γ : sp.Names) (γx γxe γxm γxu : GName) (N r : Nat) (rp : Loc)
    (sl : GoSlice) (bX : Nat) (stp : Loc) :
    swift.fld rp go!"execLog" ↦ sl ∗ sl ↦* ([] : List swift.commandStaticDesc) ∗
      ownSliceCap swift.commandStaticDesc sl (DFrac.own 1) ∗
      ghostVar γx (1 : Qp).half (bX, ([] : List swift.ExE)) ∗ ghostVar γxe (1 : Qp).half (bX, stp) ∗
      state.ownState stp (swift.applyX []) ⊢
      swift.execLInvE γ γx γxe γxm γxu N r rp := by
  iintro ⟨Hl, Hs, Hc, Hx, Hxe, Ho⟩
  iunfold swift.execLInvE
  iexists sl, [], bX, [], stp
  iframe Hl Hs Hc Hx Hxe Ho
  isplitr
  · iunfold swift.exLb; iapply BigSepL.bigSepL_nil.2; iempintro
  isplitr
  · iapply BigSepL.bigSepL_nil.2; iempintro
  isplitr
  · iapply BigSepL.bigSepL_nil.2; iempintro
  ipureintro
  refine ⟨rfl, fun i e h => by simp at h, List.nodup_nil⟩

end defs

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [swift.Assumptions]

/-- **`r.deliver(desc, cmdId)`, SWC-2's form** (replaces `deliver.specI`; see the file header):
as `deliver.specI`, with
- the reply channel's object `swift.RCh γ γc γm rp rcp bw` of the `epochRd`'s epoch (no `RC`
  parameter: `reply.specE`);
- `descCtxE` (`execL`'s invariant `execLInvE`);
- the persistent facts the reply needs: `replyPre`, `⌜dv.c.wf⌝`, the leader's prefix
  `ldrPrefix`;
- the execution ticket `xTix γxu b x`. It is consumed if `x` executes: the post gives it back
  or gives `x`'s execution (`exIn`). -/
abbrev swift.Replica.deliver.specE (str : swift.CommandId → GoString)
    (γdl : GName) (MP : GoInterface → IProp netDistGF) : Prop :=
  ∀ (γ : sp.Names) (γc γm γl γw γv γe γo γx γxe γxm γxp γxu γrp γcg γout γcl : GName) (γdc γd : ChanNames)
    (rp rr d : Loc) (N r k : Nat) (q qp : Qp) (b : Nat) (bw : w32) (stp rcp : Loc) (dv : swift.DescV)
    (x : swift.CommandId) (Rs Ret : IProp netDistGF),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      swift.descCtxE γ γc γm γl γw γv γe γo γx γxe γxm γxp γxu γrp γcg γout γcl γdc γdl str rp rr N r k ∗
      swift.epochRd γe γxe rp rr q b bw stp rcp ∗ swift.ownRdr rp γdl ∗ swift.epochPinQ γxp qp b ∗
      swift.RCh γ γc γm rp rcp bw ∗
      swift.descF d γd MP dv ∗ Rs ∗ □ swift.slotB MP γxm b x ∗
      (if decide (dv.phase = swift.phCOMMIT ∧ dv.propose ≠ null) then sp.committed γ r b (toCmdId x)
        else True) ∗
      swift.execWhy γ γxm N r b x dv ∗
      swift.repPre γ N r b x dv ∗ swift.tixD γxu γxm b x dv ∗
      (⌜dv.seq = false⌝ ∨ swift.slotOk MP γd γxm rp d b x dv Rs Ret) }}
    (App (App (Val (rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"deliver")) (Val #d))
      (Val #x))
  {{ (fin : Bool), RET #fin;
      swift.epochRd γe γxe rp rr q b bw stp rcp ∗ swift.ownRdr rp γdl ∗ swift.epochPinQ γxp qp b ∗
      if fin then swift.exIn γxm b x ∗ Ret
      else swift.descF d γd MP dv ∗ Rs ∗ swift.tixD γxu γxm b x dv }}

end specs

end Perennial.github_com.imdea_software.swiftpaxos
