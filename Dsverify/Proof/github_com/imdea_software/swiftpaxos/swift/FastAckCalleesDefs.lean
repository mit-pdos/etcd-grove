/-
The definitions, specs and lemmas of `FastAckCallees.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RecSync
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.NewSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.AcceptLDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.SeqBound
public import Perennial.Proof.bytes
import all Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Inv

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace sp

/-- A command is not among its own dependencies in a sequence. -/
theorem depsIn_not_self (s : Seq) (x : CmdId) : x ∉ depsIn s x := by
  intro h
  unfold depsIn at h
  split at h
  · rename_i c _
    obtain ⟨t1, q', t2, ht1, hq', -⟩ := (mem_lkDeps (before s x) c x).mp h
    have hmem : q' ∈ before s x := by rw [ht1]; simp
    unfold before at hmem
    have := List.all_eq_true.mp List.all_takeWhile q' hmem
    simp [hq'] at this
  · simp at h

section ghost
variable [GoGlobalContext] [G : GooseGlobalGS .hasLC netDistGF] [π : NetProtoGS] [GobFmt]
variable {γ : Names} {γc γm γl : GName}

/-- A pre-acceptance's dependencies do not contain the command (an identity step of
`node_step`). -/
theorem preacc_notSelf (E : CoPset) (hE : ↑spN ⊆ E) (N : Nat) (fr : Bool) (l : List GoString)
    (r k : Nat) (st : RState) (r' b : Nat) (y : CmdId) (D : List CmdId) (hr : r < N)
    (hk : nodeOf l r = some k) :
    inv γ γc γm γl ∗ cfg γc γm N fr l ∗ nodeSt γ k (1 : Qp).half st ∗ preacc γ r' b y D ⊢
    |={E}=> nodeSt γ k (1 : Qp).half st ∗ ⌜y ∉ D⌝ := by
  iintro ⟨#Hinv, #Hcfg, Hst, #Hpre⟩
  imod node_step E hE N fr l r k st none
    (fun s' => iprop(⌜s' = st ∧ y ∉ D⌝)) hr hk $$ [Hst]
    with ⟨%st', Hst, -, %Heq⟩
  · iframe Hinv Hcfg Hst
    isplitl []
    · iunfold predPre; itrivial
    unfold stepUpd
    iintro %S %mC %mL %mS %mA %mP %mCo %mR %mPa %HH HC HL HS HA HP HCo HRp HPa
    obtain ⟨HI, Hsr, Hrs, Hrepr⟩ := HH
    iunfold preacc at Hpre
    ihave %HlkP := ghost_map_lookup $$ HP Hpre
    have hpre : S.pre r' b y = some D := by rw [← Hrepr.pre]; exact HlkP
    obtain ⟨-, -, -, hD, -⟩ := HI.pre_ok _ _ _ _ hpre
    imodintro
    iexists S, mL, mS, mA, mP, mCo, mR, mPa
    iframe
    ipureintro
    refine ⟨⟨HI, Hsr, Hrepr, rfl, rfl, PState.le_refl S, fun _ _ => rfl, rfl⟩, Hrs, ?_⟩
    rw [hD]; exact depsIn_not_self _ _
  obtain ⟨rfl, h⟩ := Heq
  imodintro
  iframe Hst
  ipureintro; exact h

end ghost
end sp

/-- A duplicate-free list of `int32`s has at most `2^32` entries (P3's bound). -/
theorem swift.nodup_w32_len (l : List w32) (h : l.Nodup) : l.length ≤ 2 ^ 32 := by
  have := swift.nodup_nat_len (l := l.map BitVec.toNat) (n := 2 ^ 32)
    (swift.nodup_map_on _ l (fun x _ y _ e => BitVec.eq_of_toNat_eq e) h)
    (by intro a ha; obtain ⟨z, -, rfl⟩ := List.mem_map.mp ha; exact z.isLt)
  simpa using this

section dstep
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [swift.Assumptions]

/-- `preacc_notSelf` from a descriptor's tokens. -/
theorem swift.preacc_notSelf_row (γ : sp.Names) (γc γm γl γv γe γo : GName) {sn : swift.StN} (N r k : Nat)
    (fr : Bool) (l : List GoString) (q : Qp) (b : Nat) (y : sp.CmdId) (rv : swift.RowV)
    (r' b' : Nat) (z : sp.CmdId) (D : List sp.CmdId) (hr : r < N) (hk : nodeOf l r = some k) :
    sp.inv γ γc γm γl ∗ sp.cfg γc γm N fr l ∗ inv swift.nodeN (swift.nodeInvD γ γv γe γo sn k) ∗
      swift.epochTok γe q (b, b) ∗ swift.rowTok γo b y rv ∗ sp.preacc γ r' b' z D ⊢
    |={⊤}=> swift.epochTok γe q (b, b) ∗ swift.rowTok γo b y rv ∗ ⌜z ∉ D⌝ := by
  iintro ⟨#Hinv, #Hcfg, #Hninv, Hep, Htok, #Hpre⟩
  iapply (swift.desc_upd ⊤ (fun _ _ => CoPset.mem_full) swift.nodeN_diff γ γv γe γo k q b y rv rv (fun st => st) iprop(⌜z ∉ D⌝)
    (fun _ => rfl) (fun _ => rfl) (fun _ _ _ hacc => hacc)
    (fun st hrv b' y' => by
      split
      · rename_i h; obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact hrv.symm
      · rfl))
  iframe Hninv Hep Htok
  iintro %st ⟨%hb, %hc, %hrv, %hyl⟩ Hst
  iapply (sp.preacc_notSelf (⊤ \ ↑swift.nodeN) swift.nodeN_diff N fr l r k st r' b' z D hr hk)
  iframe Hinv Hcfg Hst Hpre

/-- A follower's `depsOk` (allowing `d = x`) on dependencies without `x` is N2. -/
theorem swift.depsOk_N2 (c : swift.DC) (b : Nat) (D : List sp.CmdId) (x : swift.CommandId)
    (hx : toCmdId x ∉ D) :
    swift.depsOk c b (D.map ofCmdId) x ⊢
      [∗list] d ∈ D, iprop(sp.accepted c.γ c.r b d ∨ sp.committed c.γ c.r b d) := by
  unfold swift.depsOk
  induction D with
  | nil => iintro -; iapply BigSepL.bigSepL_nil.2; itrivial
  | cons d D ih =>
    simp only [List.map_cons]
    iintro ⟨Hd, HD⟩
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hd]
    · icases Hd with (%h | Hd)
      · exfalso; apply hx; rw [← h]; simp
      · simp only [swift.toCmdId_ofCmdId]; iexact Hd
    · iapply (ih (fun h => hx (List.mem_cons_of_mem _ h))) $$ HD

end dstep

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions]

/-- `(&dep1).Equals(dep2)` on any lists: some Boolean. -/
abbrev swift.Dep.Equals.specAny : Prop :=
  ∀ (dp : Loc) (d1 d2 : GoSlice) (dq dq1 dq2 : DFrac) (l1 l2 : List swift.CommandId),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      typedPointsto dp d1 dq ∗ d1 ↦*{dq1} l1 ∗ d2 ↦*{dq2} l2 }}
    (App (Val (dp @!! go.GoType.PointerType swift.Dep.ty @!! go!"Equals")) (Val #d2))
  {{ (bb : Bool), RET #bb; typedPointsto dp d1 dq ∗ d1 ↦*{dq1} l1 ∗ d2 ↦*{dq2} l2 }}

/-- `SHashesEq(hs1, hs2)` on any read-only lists: some Boolean. -/
abbrev swift.SHashesEq.specAny : Prop :=
  ∀ (s1 s2 : GoSlice) (l1 l2 : List swift.SHash),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      s1 ↦*□ l1 ∗ s2 ↦*□ l2 }}
    (App (App (Val (@! swift.SHashesEq)) (Val #s1)) (Val #s2))
  {{ (bb : Bool), RET #bb; True }}

/-- What a light slow ack sent through the batcher needs (`batchSlowP` but the operation):
the sending context, the read-only `*MLightSlowAck`, its model ack sent by this replica with
its witness. -/
def swift.slowOpP (γ : sp.Names) (γc γm : GName) (rp l : Loc) : IProp netDistGF :=
  iprop(∃ (N : Nat) (me : w32) (sa : swift.MLightSlowAck) (s : sp.SlowAck),
    swift.sendCtxN γ γc γm rp N me ∗ l ↦□ sa ∗
    ⌜swift.slowAckRepr sa s ∧ s.rep = me⌝ ∗ sp.msgOk γ γc γm (.lightSlowAck s))

/-- `b.SendLightSlowAck(l)`. -/
abbrev swift.Batcher.SendLightSlowAck.specI : Prop :=
  ∀ (γ : sp.Names) (γc γm : GName) (rp b l : Loc),
  {{ swift.batcherH γ γc γm rp b ∗ swift.slowOpP γ γc γm rp l }}
    (App (Val (b @!! go.GoType.PointerType swift.Batcher.ty @!! go!"SendLightSlowAck")) (Val #l))
  {{ RET #(); True }}

/-- `b.SendLightSlowAckClient(l, cid)`. -/
abbrev swift.Batcher.SendLightSlowAckClient.specI : Prop :=
  ∀ (γ : sp.Names) (γc γm : GName) (rp b l : Loc) (cid : w32),
  {{ swift.batcherH γ γc γm rp b ∗ swift.slowOpP γ γc γm rp l }}
    (App (App (Val (b @!! go.GoType.PointerType swift.Batcher.ty @!! go!"SendLightSlowAckClient"))
      (Val #l)) (Val #cid))
  {{ RET #(); True }}

end specs

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions]

omit [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps] [swift.Assumptions] in
/-- `slice_array` at any fraction (as `swift.handler.slice_array_dq`). -/
theorem swift.slice_array_dq' {V : Type} [ZeroVal V] [TypedPointsto (GF := netDistGF) V] (l : Loc)
    (n : Int) (a : GoArray V n) (dq : DFrac) (hn : n < 2 ^ 63) :
    (typedPointsto l a dq : IProp netDistGF) ⊢ slice.mk l (W64 n) (W64 n) ↦*{dq} a.arr := by
  obtain ⟨arr⟩ := a
  iintro H
  icases array_len _ _ _ _ $$ H with %Hn
  rw [ownSlice_unseal]; unfold ownSliceDef
  iright
  have : sint.Z (W64 n) = n := by subst Hn; word
  simp only
  rw [this]
  iframe H
  ipureintro; omega

end proofs

end Perennial.github_com.imdea_software.swiftpaxos
