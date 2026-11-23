/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/RunSpecs.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The run loop's context and the internal specs of the callees of its handlers (the swift
group's; not frozen), stated over the local invariant (Proof/swift/Local.lean):

* `swift.runCtx`: the persistent facts every run-loop handler uses (the embedded replica, its
  id and `N`, the protocol invariant and configuration, the node invariant, `delivered` with its
  reader borrowing right, `cntL`).
* `swift.descRun γd rp`: the run loop's share of the descriptors' machinery (§1.2 of
  notes/prove-swift.md): `cmdDescs` (at a half: the descriptors' goroutines read it) and its
  persistent entries `descIs γd d x`. Its full content (epoch tokens, sequential descriptors,
  unclaimed ones) comes with the descriptors' proofs.
* `swift.propFacts`: what a proposal's descriptor gets with the `*GPropose` (the facts its
  `upd_preaccept` needs): the replica's sequence `s` of its ballot as a `locLb`, `x` last, the
  base `B` (a prefix of `s`), the dependencies `D = lkDeps` before `x`, the path `P` of the hash
  `H` with its conditions; (round 14) `ld` iff `r` leads `b` (of `N`), `s` duplicate-free.
* Specs (hypotheses of the handlers' proofs): `CommandId.String`, `getDepAndHashes`,
  `getCmdDescWith` (a proposal); `recordLeaderHash`'s is RecordLeaderHash.lean's `specT`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.Local
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.ShInv

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable [swift.Assumptions]

/-- `cntL`'s lock invariant (S4): `seqnum` and `routineCount`. (The leader's numbering facts,
HUB-REQUEST M3, come with `recordLeaderHash`'s proof.) -/
def swift.cntLInv (rp : Loc) : IProp netDistGF :=
  iprop(∃ (n c : w64), swift.fld rp go!"seqnum" ↦ n ∗ swift.fld rp go!"routineCount" ↦ c)

/-- The run loop's persistent context (see the file header). -/
def swift.runCtx (γ : sp.Names) (γc γm γl γw γv : GName) (rp : Loc) (N r k : Nat) :
    IProp netDistGF :=
  iprop(∃ (rr : Loc) (me : w32) (fr : Bool) (l : List GoString) (dm : GoSlice),
    swift.fld rp go!"Replica" ↦□ rr ∗ replica.isReplica rr γ γc γm γw N me ∗
    ⌜sp.rid me = r ∧ 0 ≤ sint.Z me ∧ r < N ∧ 1 ≤ N ∧ N ≤ 7 ∧ nodeOf l r = some k⌝ ∗
    sp.inv γ γc γm γl ∗ sp.cfg γc γm N fr l ∗
    inv swift.nodeN (swift.nodeInv γ γv k) ∗
    swift.fld rp go!"delivered" ↦□ dm ∗
    github_com.orcaman.concurrent_map.isCMap dm swift.deliveredR ∗
    swift.readerBorrow dm swift.deliveredR ∗
    sync.isMutex (swift.fld rp go!"cntL") (swift.cntLInv rp))

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 1000000 in
instance swift.runCtx_persistent (γ : sp.Names) (γc γm γl γw γv : GName) (rp : Loc)
    (N r k : Nat) : Persistent (swift.runCtx γ γc γm γl γw γv rp N r k) := by
  unfold swift.runCtx; infer_instance

/-- Descriptor `d` is command `x`'s (persistent; a `cmdDescs` entry's fact). -/
def swift.descIs (γd : GName) (d : Loc) (x : sp.CmdId) : IProp netDistGF :=
  ghostMapElem γd d DFrac.discard x

/-- What `proposeDeps[x] = D` says of the run loop's sequence `s` (round N6, D75 (3)): `x` is in
`s`, `D` is of `x`'s dependencies in `s` (`getDepAndHashes`' `lkDeps` when `x` was appended),
and `D` is short (`depWf`). Kept by appends (`swift.propDepOk_append`). -/
def swift.propDepOk (s : sp.Seq) (x : swift.CommandId) (D : List swift.CommandId) : Prop :=
  toCmdId x ∈ s.map Prod.fst ∧ (∀ d ∈ D, toCmdId d ∈ sp.depsIn s (toCmdId x)) ∧
    D.length < 2 ^ 62

theorem swift.propDepOk_append (s u : sp.Seq) (x : swift.CommandId) (D : List swift.CommandId)
    (h : swift.propDepOk s x D) : swift.propDepOk (s ++ u) x D := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by rw [List.map_append]; exact List.mem_append_left _ h1, fun d hd => ?_, h3⟩
  rw [sp.depsIn_append_of_mem s u _ h1]; exact h2 d hd

/-- `proposeDeps` (P4, fork e411c02; the run loop's only, reset with `cmdDescs` by `handleSync`):
each handled proposal's dependencies (read-only slices, shared with its `proposeMsg`). Round N6
(D75 (3)): at the run loop's sequence `s` (`bs ++ hd`, inside `runInv`'s/`recInvB`'s
existential), each entry with its `swift.propDepOk`. -/
def swift.propDepsOwn (rp : Loc) (s : sp.Seq) : IProp netDistGF :=
  iprop(∃ (pdm : Loc) (PD : GMap swift.CommandId GoSlice), swift.fld rp go!"proposeDeps" ↦ pdm ∗
    pdm ↦$ PD ∗ [∗map] x ↦ sl ∈ PD, ∃ D : List swift.CommandId, sl ↦*□ D ∗ ⌜swift.propDepOk s x D⌝)

/-- What `cmdDescs`' entries say: a descriptor (round 23, D18 G6: no command; a pooled
descriptor is reused for other commands, so a replica-lifetime record `descIs` cannot be kept;
the command link is the descriptors' invariant's, `descEnt`'s `k = str y`). `γd` is unused. -/
def swift.descR (_γd : GName) : GoString → GoInterface → IProp netDistGF :=
  fun _ v => iprop(∃ d : Loc,
    ⌜v = interface.mkOk (go.GoType.PointerType swift.commandDesc.ty) #d⌝ ∗
    -- round 46 (D60, O1-a): the entry's `successorsL` mutex (an existing entry's, for `depSpecR`)
    sync.isMutex (swift.dfld d go!"successorsL") (swift.succInv d))

/-- The run loop's share of the descriptors' machinery (see the file header). -/
def swift.descRun (γd : GName) (rp : Loc) : IProp netDistGF :=
  iprop(∃ dm : GoSlice, typedPointsto (swift.fld rp go!"cmdDescs") dm (DFrac.own (1 : Qp).half) ∗
    github_com.orcaman.concurrent_map.isCMap dm (swift.descR γd) ∗
    ∃ s, swift.propDepsOwn rp s)

/-- The base of ballot `b`: none in ballot 0, else its `MSync`'s order. -/
def swift.baseIs (γ : sp.Names) (b : Nat) (B : List sp.CmdId) : IProp netDistGF :=
  iprop(⌜b = 0 ∧ B = []⌝ ∨ ∃ M, sp.syncIs γ b M ∗ ⌜B = sp.syncOrder M⌝)

/-- What a proposal's descriptor gets (see the file header): replica `r` handled `x` (command
`c`) last in its sequence `s` of ballot `b` (with base `B`), with dependencies `D` (the Go
slice `dep`) and hash `H` of path `P` (the slice `hs`). -/
def swift.propFacts (γ : sp.Names) (N r b : Nat) (ld : Bool) (x : sp.CmdId) (c : sp.Cmd)
    (s : sp.Seq) (B D P : List sp.CmdId) (H : swift.SHash) : IProp netDistGF :=
  iprop(sp.locLb γ r b s ∗ swift.baseIs γ b B ∗ sp.startHash P H.H'.arr ∗
    ⌜s.getLast? = some (x, c) ∧ x ∉ (s.dropLast).map Prod.fst ∧
      D = sp.lkDeps s.dropLast c ∧ P.getLast? = some x ∧
      (ld = true → P = swift.idsOfKey (s.dropLast.drop B.length) c.key ++ [x]) ∧
      (∀ z ∈ swift.idsOfKey (s.dropLast.drop B.length) c.key, z ∈ P) ∧
      (ld = true ↔ sp.leaderOf N b = r) ∧ B <+: (s.dropLast).map Prod.fst ∧
      (s.map Prod.fst).Nodup⌝)

instance swift.propFacts_persistent (γ : sp.Names) (N r b : Nat) (ld : Bool) (x : sp.CmdId)
    (c : sp.Cmd) (s : sp.Seq) (B D P : List sp.CmdId) (H : swift.SHash) :
    Persistent (swift.propFacts γ N r b ld x c s B D P H) := by
  unfold swift.propFacts swift.baseIs sp.locLb; infer_instance

end defs

section lemmas
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable [swift.Assumptions]

/-- `proposeDeps`' facts survive an append to the sequence (round N6). -/
theorem swift.propDepsOwn_append (rp : Loc) (s u : sp.Seq) :
    swift.propDepsOwn rp s ⊢ swift.propDepsOwn rp (s ++ u) := by
  iunfold swift.propDepsOwn
  iintro ⟨%pdm, %PD, Hf, Hm, Hents⟩
  iexists pdm, PD
  iframe Hf Hm
  have hm : ∀ {x : swift.CommandId} {sl : GoSlice},
      (iprop(∃ D : List swift.CommandId, sl ↦*□ D ∗ ⌜swift.propDepOk s x D⌝) : IProp netDistGF) ⊢
        iprop(∃ D : List swift.CommandId, sl ↦*□ D ∗ ⌜swift.propDepOk (s ++ u) x D⌝) := by
    intro x sl
    iintro ⟨%D, #HD, %hD⟩
    iexists D
    iframe HD
    ipureintro; exact swift.propDepOk_append s u x D hD
  iapply (BigSepM.bigSepM_mono_of_forall hm)
  iexact Hents

/-- An empty `proposeDeps` (`handleSync`'s reset, the allocation) at any sequence. -/
theorem swift.propDepsOwn_empty (rp pdm : Loc) (s : sp.Seq) :
    swift.fld rp go!"proposeDeps" ↦ pdm ∗ pdm ↦$ (∅ : GMap swift.CommandId GoSlice) ⊢
      swift.propDepsOwn rp s := by
  iintro ⟨Hf, Hm⟩
  iunfold swift.propDepsOwn
  iexists pdm, ∅
  iframe Hf Hm
  iapply BigSepM.bigSepM_empty.2
  itrivial

end lemmas

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions]

/-- `cmdId.String()` (through a pointer): some string (round 16: `isPkgInit swift`;
proved, CmdStr.lean). -/
abbrev swift.CommandId.String.specI : Prop :=
  ∀ (p : Loc) (x : swift.CommandId),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      (p ↦ x : IProp netDistGF) }}
    (App (Val #(methods (go.GoType.PointerType swift.CommandId.ty) go!"String" #p)) (Val #()))
  {{ (s : GoString), RET #s; p ↦ x }}

/-- `r.getDepAndHashes(cmd, x)` (a put or a get: one key): `x`'s dependencies along the
sequence `s ++ hd` (the keys' `lightKeyInfo`s, the model's `lkDeps`), and the hash of the path
its key's hash log appends (`hlogOk`'s consequences), the keys and hash logs then along
`hd ++ [(x, c)]`; (round 14) both slices non-nil (`handlePropose` tests `pm.dep != nil`).
(Round 7: the premises `c.isPut ∨ c.isGet` (`keysOf` of a scan reads its
value; `getConflictCmds` returns `C` for any non-get, `lkDeps` only for a put) and the sequence's
length bound (`lightKeyInfo.add` appends to `C`).) -/
abbrev swift.Replica.getDepAndHashes.specI : Prop :=
  ∀ (rp km hm : Loc) (kM : GMap w64 GoInterface) (hM : GMap w64 Loc) (s hd : sp.Seq) (ld : Bool)
    (K : sp.CmdId → Prop) (Λ : w64 → w64 → List sp.CmdId → Prop)
    (x : swift.CommandId) (c : sp.Cmd) (vs : GoSlice),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      swift.fld rp go!"keys" ↦ km ∗ swift.keysOwn km kM (s ++ hd) ∗
      swift.fld rp go!"hlog" ↦ hm ∗ swift.hlogOwn hm hM ld hd K Λ ∗
      ⌜toCmdId x ∉ (s ++ hd).map Prod.fst ∧ ¬ K (toCmdId x) ∧ (c.isPut ∨ c.isGet) ∧
        (s ++ hd).length + 1 < 2 ^ 63⌝ }}
    (App (App (Val (rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"getDepAndHashes"))
      (Val #(state.Command.mk c.op c.key vs))) (Val #x))
  {{ (dep hs : GoSlice) (kM' : GMap w64 GoInterface) (hM' : GMap w64 Loc) (P : List sp.CmdId)
      (H : swift.SHash), RET (PairV #dep #hs);
      swift.fld rp go!"keys" ↦ km ∗ swift.keysOwn km kM' (s ++ hd ++ [(toCmdId x, c)]) ∗
      swift.fld rp go!"hlog" ↦ hm ∗ swift.hlogOwn hm hM' ld (hd ++ [(toCmdId x, c)]) K Λ ∗
      dep ↦* ((sp.lkDeps (s ++ hd) c).map ofCmdId) ∗ ownSliceCap swift.CommandId dep (DFrac.own 1) ∗
      hs ↦* [H] ∗ ownSliceCap swift.SHash hs (DFrac.own 1) ∗ sp.startHash P H.H'.arr ∗
      ⌜P.getLast? = some (toCmdId x) ∧
        (ld = true → P = swift.idsOfKey hd c.key ++ [toCmdId x]) ∧
        (∀ z ∈ swift.idsOfKey hd c.key, z ∈ P)⌝ ∗ ⌜dep ≠ slice.nil ∧ hs ≠ slice.nil⌝ }}

/-- A proposal message for `x`'s descriptor (P4, fork e411c02, SWB-11): `pm` (read-only) with the
proposal `gp` (read-only, D16), the dependencies `dep` and hashes `hs` (read-only), the
leader's number `sq`, and their facts; (change log C22) the replica's number of `x`, the
`Seqnum` of its fast ack (`sq` if it leads `b`, else 0). -/
def swift.propMsgR (γ : sp.Names) (pm gp : Loc) (x : swift.CommandId) (c : sp.Cmd)
    (dep hs : GoSlice) (sq : w64) (N r b : Nat) (ld : Bool) (s : sp.Seq) (B D P : List sp.CmdId)
    (H : swift.SHash) : IProp netDistGF :=
  iprop(pm ↦□ swift.proposeMsg.mk gp dep hs sq ∗ swift.propIs γ gp (toCmdId x) c ∗
    dep ↦*□ (D.map ofCmdId) ∗ hs ↦*□ [H] ∗ ⌜dep ≠ slice.nil ∧ hs ≠ slice.nil⌝ ∗
    swift.propFacts γ N r b ld (toCmdId x) c s B D P H ∗
    sp.numIs γ r b (toCmdId x) (if ld then sq else W64 (-1)))

end specs

end Perennial.github_com.imdea_software.swiftpaxos
