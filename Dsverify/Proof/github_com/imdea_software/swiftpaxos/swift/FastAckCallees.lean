/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/FastAckCallees.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`fastAckFromLeader`'s acceptance path's callees and facts (round 11, notes/prove-swift.md §17):
* `sp.depsIn_not_self`, `sp.preacc_notSelf`, `swift.preacc_notSelf_row`: a pre-acceptance's
  dependencies do not contain the command (`PInv.pre_ok`: `D = depsIn … y`), so a follower's
  `depsOk` (which allows `d = x`) gives N2 (`swift.depsOk_N2`);
* `swift.Dep.Equals.specAny`, `swift.SHashesEq.specAny`: the comparisons on any lists return
  some Boolean (their values only decide what is sent; any is safe for the proof);
* `swift.Batcher.SendLightSlowAck.specI`/`SendLightSlowAckClient.specI`: the batcher's slow-ack
  operations (`batchSlowP`, read-only ack).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RecSync
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.NewSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.AcceptL
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
variable [GoGlobalContext] [G : GooseGlobalGS .hasLC netDistGF] [π : NetProtoGS]
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
  iapply (swift.desc_upd γ γv γe γo k q b y rv rv (fun st => st) iprop(⌜z ∉ D⌝)
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
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
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
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions]

theorem swift.Batcher.SendLightSlowAck.wp_proof : swift.Batcher.SendLightSlowAck.specI (hG := hG) := by
  intro γ γc γm rp b l
  wp_start as ⟨#Hb, Hop⟩
  iunfold swift.batcherH at Hb
  icases Hb with ⟨%fa, %ls, %γ1, %γ2, #Hbs, #Hfa, #Hls⟩
  ihave #Hbs2 := Hbs
  iStructNamedPrefix Hbs2 "B"
  wp_auto
  wp_apply wp_bag_send (t := swift.BatcherOp.ty) γ2 ls _ (swift.batchSlowP γ γc γm rp) $$ [Hop]
  · iframe Hls
    iunfold swift.slowOpP at Hop
    icases Hop with ⟨%N, %me, %sa, %s, #Hc, #Hl, %Hs, #Hok⟩
    iunfold swift.batchSlowP
    iexists N, me, l, sa, s
    iframe Hc Hl Hok
    ipureintro; exact ⟨rfl, Hs⟩
  iapply HΦ; itrivial

theorem swift.Batcher.SendLightSlowAckClient.wp_proof :
    swift.Batcher.SendLightSlowAckClient.specI (hG := hG) := by
  intro γ γc γm rp b l cid
  wp_start as ⟨#Hb, Hop⟩
  iunfold swift.batcherH at Hb
  icases Hb with ⟨%fa, %ls, %γ1, %γ2, #Hbs, #Hfa, #Hls⟩
  ihave #Hbs2 := Hbs
  iStructNamedPrefix Hbs2 "B"
  wp_auto
  wp_apply wp_bag_send (t := swift.BatcherOp.ty) γ2 ls _ (swift.batchSlowP γ γc γm rp) $$ [Hop]
  · iframe Hls
    iunfold swift.slowOpP at Hop
    icases Hop with ⟨%N, %me, %sa, %s, #Hc, #Hl, %Hs, #Hok⟩
    iunfold swift.batchSlowP
    iexists N, me, l, sa, s
    iframe Hc Hl Hok
    ipureintro; exact ⟨rfl, Hs⟩
  iapply HΦ; itrivial

theorem swift.Dep.Equals.wp_proofAny : swift.Dep.Equals.specAny (hG := hG) := by
  intro dp d1 d2 dq dq1 dq2 l1 l2
  haveI := swift.hlog.cmdId_intoValInj (sem := sem)
  wp_start as ⟨Hdp, Hd1, Hd2⟩
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  ihave %Hl1 := ownSlice_len $$ Hd1
  ihave %Hl2 := ownSlice_len $$ Hd2
  wp_if_destruct
  · have hlen : l1.length = l2.length := by rw [Hl1.1, Hl2.1, Hif]
    have hdl := Hif
    wp_apply (wp_map_make1 (K := swift.CommandId) (V := Unit)) as %m1 Hm1
    wp_apply (wp_map_make1 (K := swift.CommandId) (V := Unit)) as %m2 Hm2
    ihave HI : (∃ (i : w64) (s1 s2 : GMap swift.CommandId Unit), "i" ∷ i_ptr ↦ i ∗
        "Hm1" ∷ m1 ↦$ s1 ∗ "Hm2" ∷ m2 ↦$ s2 ∗
        "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z d1.len⌝ :
        IProp netDistGF) $$ [i Hm1 Hm2]
    · iexists W64 0, ∅, ∅; iframe; ipureintro; refine ⟨by word, by word⟩
    wp_for HI
    wp_if_destruct
    · have hil1 : sint.nat i < l1.length := by have := Hi.1; word
      have hil2 : sint.nat i < l2.length := by have := Hi.1; word
      obtain ⟨x, hx⟩ : ∃ x, l1[sint.nat i]? = some x := ⟨_, List.getElem?_eq_getElem hil1⟩
      obtain ⟨y, hy⟩ : ∃ y, l2[sint.nat i]? = some y := ⟨_, List.getElem?_eq_getElem hil2⟩
      have hb1 : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z d1.len := ⟨Hi.1, Hif⟩
      have hb2 : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z d2.len := ⟨Hi.1, by rw [← hdl]; exact Hif⟩
      have hix : l1[(sint.Z i).toNat]? = some x := by rw [show (sint.Z i).toNat = sint.nat i by word, hx]
      have hiy : l2[(sint.Z i).toNat]? = some y := by rw [show (sint.Z i).toNat = sint.nat i by word, hy]
      rw [ite_eq_left hb1]
      wp_apply (wp_load_slice_index (V := swift.CommandId) d1 (sint.Z i) _ _ x Hi.1) $$ [Hd1] as Hd1
      · iframe; ipureintro; exact hix
      wp_bind (App (Val (GoInstruction (Convert go.untypedBool go.bool))) _)
      iapply (wp_wand (Φ := fun v => iprop(⌜v = #(decide (x = y))⌝ ∗ d2 ↦*{dq2} l2))) $$ [Hd2]
      · rw [ite_eq_left hb2]
        wp_apply (wp_load_slice_index (V := swift.CommandId) d2 (sint.Z i) _ _ y Hi.1) $$ [Hd2] as Hd2
        · iframe; ipureintro; exact hiy
        wp_if_destruct
        · iframe; ipureintro; congr 2; cases x; cases y; simp_all
        · iframe; ipureintro; congr 2; cases x; cases y; simp_all
      iintro %v ⟨%hv, Hd2⟩
      subst hv
      wp_if_destruct
      · -- the same id at `i`
        wp_for_post
        iframe
        iexists i + W64 1, s1, s2
        iframe
        ipureintro
        refine ⟨by word, by word⟩
      · rw [ite_eq_left hb1]
        wp_apply (wp_load_slice_index (V := swift.CommandId) d1 (sint.Z i) _ _ x Hi.1) $$ [Hd1] as Hd1
        · iframe; ipureintro; exact hix
        wp_apply (wp_map_lookup2 _ _ m2 s2 x) $$ Hm2 as Hm2
        have hxy : x ≠ y := Hif
        let s1' := if (s2 !! x).isSome then s1 else <[x := ()]> s1
        let s2' := if (s2 !! x).isSome then GMap.delete x s2 else s2
        wp_bind (If _ _ _)
        iapply (wp_wand (Φ := fun v => iprop(m1 ↦$ s1' ∗ m2 ↦$ s2' ∗ d1 ↦*{dq1} l1 ∗
            seen1_ptr ↦ m1 ∗ seen2_ptr ↦ m2 ∗ dep1_ptr ↦ d1 ∗ i_ptr ↦ i ∗ ⌜v = executeVal⌝)))
          $$ [Hm1 Hm2 Hd1 seen1 seen2 dep1 i]
        · wp_if_destruct
          · rw [ite_eq_left hb1]
            wp_apply (wp_load_slice_index (V := swift.CommandId) d1 (sint.Z i) _ _ x Hi.1) $$ [Hd1] as Hd1
            · iframe; ipureintro; exact hix
            wp_apply (wp_mapDelete m2 s2 x) $$ Hm2 as Hm2
            simp only [s1', s2', Hif, ↓reduceIte]
            iframe
          · rw [ite_eq_left hb1]
            wp_apply (wp_load_slice_index (V := swift.CommandId) d1 (sint.Z i) _ _ x Hi.1) $$ [Hd1] as Hd1
            · iframe; ipureintro; exact hix
            wp_apply (wp_mapInsert _ m1 s1 x (zero_val Unit)) $$ Hm1 as Hm1
            have hc : (s2 !! x).isSome = false := by simpa using Hif
            simp only [s1', s2', hc, Bool.false_eq_true, ↓reduceIte]
            iframe
        iintro %v ⟨Hm1, Hm2, Hd1, seen1, seen2, dep1, i, %hv⟩
        subst hv
        wp_auto
        rw [ite_eq_left hb2]
        wp_apply (wp_load_slice_index (V := swift.CommandId) d2 (sint.Z i) _ _ y Hi.1) $$ [Hd2] as Hd2
        · iframe; ipureintro; exact hiy
        wp_apply (wp_map_lookup2 _ _ m1 s1' y) $$ Hm1 as Hm1
        wp_if_destruct
        · rw [ite_eq_left hb2]
          wp_apply (wp_load_slice_index (V := swift.CommandId) d2 (sint.Z i) _ _ y Hi.1) $$ [Hd2] as Hd2
          · iframe; ipureintro; exact hiy
          wp_apply (wp_mapDelete m1 s1' y) $$ Hm1 as Hm1
          wp_for_post
          iframe
          iexists i + W64 1, _, _
          iframe
          ipureintro
          refine ⟨by word, by word⟩
        · rw [ite_eq_left hb2]
          wp_apply (wp_load_slice_index (V := swift.CommandId) d2 (sint.Z i) _ _ y Hi.1) $$ [Hd2] as Hd2
          · iframe; ipureintro; exact hiy
          wp_apply (wp_mapInsert _ m2 s2' y (zero_val Unit)) $$ Hm2 as Hm2
          wp_for_post
          iframe
          iexists i + W64 1, _, _
          iframe
          ipureintro
          refine ⟨by word, by word⟩
    · wp_apply (wp_map_len_lt (K := swift.CommandId) (V := Unit) m1 s1) $$ [$Hm1] as ⟨Hm1, %hs1⟩
      wp_apply (wp_map_len_lt (K := swift.CommandId) (V := Unit) m2 s2) $$ [$Hm2] as ⟨Hm2, %hs2⟩
      wp_if_destruct
      · wp_apply (wp_map_len_lt (K := swift.CommandId) (V := Unit) m1 s1) $$ [$Hm1] as ⟨Hm1, -⟩
        iapply HΦ; iframe
      · iapply HΦ; iframe
  · iapply HΦ; iframe


omit [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [swift.Assumptions] in
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

theorem swift.SHashesEq.wp_proofAny [bytes.Assumptions] (wp_Equal : bytes.Equal.spec (GF := netDistGF)) :
    swift.SHashesEq.specAny (hG := hG) := by
  intro s1 s2 l1 l2
  wp_start as ⟨#Hs1, #Hs2⟩
  ihave %Hl1 := ownSlice_len $$ Hs1
  ihave %Hl2 := ownSlice_len $$ Hs2
  wp_auto
  wp_if_destruct
  rotate_left
  · iapply HΦ; itrivial
  ihave HI : (∃ i : w64, "i" ∷ i_ptr ↦ i ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z s1.len⌝ : IProp netDistGF) $$ [i]
  · iexists _; iframe; ipureintro; refine ⟨by word, by word⟩
  wp_for HI
  wp_if_destruct
  · have hil : sint.nat i < l1.length := by word
    obtain ⟨x, hx⟩ : ∃ x, l1[sint.nat i]? = some x := ⟨_, List.getElem?_eq_getElem hil⟩
    rw [if_pos (by word)]
    wp_apply (wp_load_slice_index (V := swift.SHash) s1 (sint.Z i) l1 _ x
      Hi.1) $$ [Hs1] as -
    · iframe #; ipureintro; rw [show (sint.Z i).toNat = sint.nat i by word, hx]
    have Hleq : s1.len = s2.len := by assumption
    icases typedPointsto_split _ _ _ $$ h with h
    simp only [TypedPointsto.typedPointstoDef]
    icases h with ⟨H, -⟩
    ipersist H
    ihave #Hh := swift.slice_array_dq' _ 32 _ DFrac.discard (by decide) $$ H
    ihave HJ : (∃ k : w64, "i" ∷ i_ptr ↦ k ∗
        "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z s2.len⌝ : IProp netDistGF) $$ [i]
    · iexists _; iframe; ipureintro; word
    wp_for HJ
    wp_if_destruct
    · have hkl : sint.nat k < l2.length := by word
      obtain ⟨y, hy⟩ : ∃ y, l2[sint.nat k]? = some y := ⟨_, List.getElem?_eq_getElem hkl⟩
      rw [if_pos (by word)]
      wp_apply (wp_load_slice_index (V := swift.SHash) s2 (sint.Z k) l2 _ y
        Hk.1) $$ [Hs2] as -
      · iframe #; ipureintro; rw [show (sint.Z k).toNat = sint.nat k by word, hy]
      icases typedPointsto_split _ _ _ $$ g with g
      simp only [TypedPointsto.typedPointstoDef]
      icases g with ⟨G, -⟩
      ipersist G
      ihave #Hg := swift.slice_array_dq' _ 32 _ DFrac.discard (by decide) $$ G
      rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, go.arrayIndexRef_0,
        show W64 32 - W64 0 = W64 32 from rfl]
      wp_apply wp_Equal $$ [Hh Hg] as -
      · iframe #
      wp_if_destruct
      · wp_for_post
        wp_for_post
        iframe
        iexists _
        iframe
        ipureintro
        refine ⟨by word, by word⟩
      · wp_for_post
        iframe
        iexists _
        iframe
        ipureintro; word
    · wp_for_post
      iapply HΦ; itrivial
  · iapply HΦ; itrivial

end proofs

end Perennial.github_com.imdea_software.swiftpaxos
