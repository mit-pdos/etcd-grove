/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/Steps.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The replica's ghost steps (MR5, notes/prove-swift.md §2): each handler's ghost update is one
opening of `sp.inv` with one model transition (`Spec/swift/Model/Steps.lean`), applied to the
replica's own node state `nodeSt γ k ½ st` (MR4: `st` is exactly its rows of `PState`).

* `sp.node_step` is the generic part: open `sp.inv`, find the protocol state `S` (switching from
  the "nothing happened yet" disjunct to the configured one if needed: `PInv_emptyInit`), check
  `S.rs r = st`, run the step's update of the protocol ghost maps (`stepUpd`), write the
  replica's new state into both halves of its node's entry and close.
* `sp.upd_*`: one per transition (handle, preaccept, accept, commit, newBallot, report,
  computeSync, takeSync), each stated over the replica's own state `st` and the persistent facts
  the step needs, giving the new `nodeSt` and the persistent facts the step's messages carry.

These open `sp.inv`'s body (decision D5's T2-1: `Proof/swift/` counts as inside the swift
package), hence `import all Spec.swift.Inv`.
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Inv
import all Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Inv

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace sp

/-! ## Pure helpers -/

/-- An empty state is its replicas' initial state. -/
theorem PState.empty_rs (S : PState) (h : S.empty) : ({ S with rs := fun _ => RState.init } : PState) = S := by
  cases S; congr; funext r; exact (h.2.2.2.2.2.2.2.2 r).symm

/-- Nothing happened and every replica is in its initial state: the invariant holds (the first
replica step switches `invBody`'s disjunct with this). -/
theorem PState.PInv_emptyInit (S : PState) (h : S.empty) (N : Nat) (fr : Bool) :
    ({ S with rs := fun _ => RState.init } : PState).PInv N fr := by
  obtain ⟨hl, hs, ha, hp, hpa, hc, hr, hG, -⟩ := h
  refine ⟨fun r b => ?_, fun r => ?_, fun r b x h => ?_, fun r b x D h => ?_,
    fun r b x P h => ?_, fun r b x h => ?_, fun r b R h => ?_, fun b M h => ?_,
    fun r b => ?_, ?_⟩
  · simp [hl]
  · simp [RState.init]
  · exact absurd h (ha r b x)
  · simp [hp] at h
  · simp [hpa] at h
  · exact absurd h (hc r b x)
  · simp [hr] at h
  · simp [hs] at h
  · refine ⟨by simp [hl, RState.locAt, RState.init], fun x => by simp [ha, RState.init],
      fun x => by simp [hp, RState.preAt, RState.init], fun x => by simp [hpa, RState.pathAt, RState.init],
      fun x => by simp [hc, RState.init], by simp [hr, RState.repAt, RState.init]⟩
  · simp [hG]

theorem nodeOf_lt {l : List GoString} {r k : Nat} (h : nodeOf l r = some k) : k < 5 := by
  unfold nodeOf at h
  cases hl : l[r]? with
  | none => rw [hl] at h; cases h
  | some a =>
    rw [hl] at h
    simp only [Option.bind_some] at h
    obtain ⟨hlt, -⟩ := List.idxOf?_eq_some_iff.mp h
    have h5 : replicaAddrs.length = 5 := rfl
    omega

theorem nodeOf_inj {l : List GoString} (hnd : l.Nodup) {r1 r2 k : Nat}
    (h1 : nodeOf l r1 = some k) (h2 : nodeOf l r2 = some k) : r1 = r2 := by
  unfold nodeOf at h1 h2
  cases e1 : l[r1]? with
  | none => rw [e1] at h1; cases h1
  | some a1 =>
    cases e2 : l[r2]? with
    | none => rw [e2] at h2; cases h2
    | some a2 =>
      rw [e1] at h1; rw [e2] at h2
      simp only [Option.bind_some] at h1 h2
      have ha1 := (List.idxOf?_eq_some_iff.mp h1)
      have ha2 := (List.idxOf?_eq_some_iff.mp h2)
      have hk1 : replicaAddrs[k]? = some a1 := by
        obtain ⟨hlt, heq, -⟩ := ha1; rw [List.getElem?_eq_getElem hlt, heq]
      have hk2 : replicaAddrs[k]? = some a2 := by
        obtain ⟨hlt, heq, -⟩ := ha2; rw [List.getElem?_eq_getElem hlt, heq]
      rw [hk1] at hk2; cases hk2
      have b2 := (List.getElem?_eq_some_iff.mp e2)
      obtain ⟨l2, g2⟩ := b2
      exact (List.Nodup.getElem?_inj l2 hnd).mp (e2.trans e1.symm) |>.symm

section ghost
variable [GoGlobalContext] [G : GooseGlobalGS .hasLC netDistGF]
variable {γ : Names} {γc γm γl : GName}

instance nodeSt_timeless (k : Nat) (q : Qp) (st : RState) : Timeless (nodeSt γ k q st) := by
  unfold nodeSt; infer_instance

instance cfg_timeless (N : Nat) (fr : Bool) (l : List GoString) :
    Timeless (cfg γc γm N fr l) := by
  unfold cfg confIs memIs; infer_instance

omit [GoGlobalContext] in
theorem cfg_nodup (N : Nat) (fr : Bool) (l : List GoString) :
    cfg γc γm N fr l ⊢ ⌜l.Nodup⌝ := by
  unfold cfg memIs
  iintro ⟨%c, -, ⟨-, %H⟩, -⟩
  ipureintro; exact H.1

/-- L2: the relation of a replica step's states: an identity (`none`, a read), or the predicted
event `e`'s real effect (D's `okR`, `apR`) with some path `P`. -/
def stepRel (N : Nat) (S S' : PState) (r : Nat) : Option PEv → Prop
  | none => S' = S
  | some e => ∃ P, okR N S (.rep r) e P ∧ S' = apR N S (.rep r) e P

/-- L2: the replica node `k`'s half of its future words before a step (`ev`: the step's event
and the words after it; nothing for an identity step). -/
def predPre (γ : Names) (k : Nat) : Option (PEv × List w64) → IProp netDistGF
  | none => iprop(emp)
  | some (e, W) => iprop(⌜PEvWf e⌝ ∗
      ghostMapElem γ.pred (PNode.rep k) (DFrac.own (1 : Qp).half) (encP e ++ W))

theorem predPre_some (γ : Names) (k : Nat) (e : PEv) (W : List w64) :
    predPre γ k (some (e, W)) = iprop(⌜PEvWf e⌝ ∗
      ghostMapElem γ.pred (PNode.rep k) (DFrac.own (1 : Qp).half) (encP e ++ W)) := rfl

/-- L2: the node's half after the step. -/
def predPost (γ : Names) (k : Nat) : Option (PEv × List w64) → IProp netDistGF
  | none => iprop(emp)
  | some (_, W) => ghostMapElem γ.pred (PNode.rep k) (DFrac.own (1 : Qp).half) W

theorem predPost_some (γ : Names) (k : Nat) (e : PEv) (W : List w64) :
    predPost γ k (some (e, W)) = ghostMapElem γ.pred (PNode.rep k) (DFrac.own (1 : Qp).half) W :=
  rfl

/-- A replica step's update of the protocol's ghost maps, from a protocol state `S` with `PInv`
in which the replica `r`'s state is `st`: a new state `S'` with `PInv`, represented by the new
maps, the same commands and `G`, an extension of `S` (`S.le S'`, change log C12: the client
node's history keeps its invariant, `HistOk_mono`), the other replicas' states unchanged, and the
step's facts `Q` at the replica's new state. -/
def stepUpd (γ : Names) (N : Nat) (fr : Bool) (r : Nat) (st : RState) (e : Option PEv)
    (Q : RState → IProp netDistGF) : IProp netDistGF :=
  iprop(∀ (S : PState) (mC : GMap CmdId Cmd) (mL : GMap (Nat × Nat × Nat) CmdId)
      (mS : GMap Nat SyncMsg) (mA : GMap (Nat × Nat × CmdId) Unit)
      (mP : GMap (Nat × Nat × CmdId) (List CmdId)) (mCo : GMap (Nat × Nat × CmdId) Unit)
      (mR : GMap (Nat × Nat) Report) (mPa : GMap (Nat × Nat × CmdId) (List CmdId)),
    ⌜S.PInv N fr ∧ S.syncRows N ∧ S.rs r = st ∧ Repr S mC mL mS mA mP mCo mR mPa⌝ -∗
    ghostMapAuth γ.cmds 1 mC -∗ ghostMapAuth γ.loc 1 mL -∗ ghostMapAuth γ.sync 1 mS -∗
    ghostMapAuth γ.acc 1 mA -∗ ghostMapAuth γ.pre 1 mP -∗ ghostMapAuth γ.com 1 mCo -∗
    ghostMapAuth γ.rep 1 mR -∗ ghostMapAuth γ.path 1 mPa ==∗
    ∃ (S' : PState) (mL' : GMap (Nat × Nat × Nat) CmdId) (mS' : GMap Nat SyncMsg)
      (mA' : GMap (Nat × Nat × CmdId) Unit) (mP' : GMap (Nat × Nat × CmdId) (List CmdId))
      (mCo' : GMap (Nat × Nat × CmdId) Unit) (mR' : GMap (Nat × Nat) Report)
      (mPa' : GMap (Nat × Nat × CmdId) (List CmdId)),
      ⌜S'.PInv N fr ∧ S'.syncRows N ∧ Repr S' mC mL' mS' mA' mP' mCo' mR' mPa' ∧ S'.cmds = S.cmds ∧
        S'.G = S.G ∧ S.le S' ∧ (∀ r', r' ≠ r → S'.rs r' = S.rs r') ∧ stepRel N S S' r e⌝ ∗
      ghostMapAuth γ.cmds 1 mC ∗ ghostMapAuth γ.loc 1 mL' ∗ ghostMapAuth γ.sync 1 mS' ∗
      ghostMapAuth γ.acc 1 mA' ∗ ghostMapAuth γ.pre 1 mP' ∗ ghostMapAuth γ.com 1 mCo' ∗
      ghostMapAuth γ.rep 1 mR' ∗ ghostMapAuth γ.path 1 mPa' ∗ Q (S'.rs r))

/-- `stepUpd` with the numbering (change log C22): the step also gets `sp.inv`'s numbering
authority (with `numOk` against the sequences) and gives it back, with `numOk` against the new
sequences. -/
def stepUpdN (γ : Names) (N : Nat) (fr : Bool) (l : List GoString) (r : Nat) (st : RState)
    (e : Option PEv) (Q : RState → IProp netDistGF) : IProp netDistGF :=
  iprop(∀ (S : PState) (mC : GMap CmdId Cmd) (mL : GMap (Nat × Nat × Nat) CmdId)
      (mS : GMap Nat SyncMsg) (mA : GMap (Nat × Nat × CmdId) Unit)
      (mP : GMap (Nat × Nat × CmdId) (List CmdId)) (mCo : GMap (Nat × Nat × CmdId) Unit)
      (mR : GMap (Nat × Nat) Report) (mPa : GMap (Nat × Nat × CmdId) (List CmdId))
      (mNu : GMap (Nat × Option (Nat × CmdId)) w64),
    ⌜S.PInv N fr ∧ S.syncRows N ∧ S.rs r = st ∧ Repr S mC mL mS mA mP mCo mR mPa ∧
      (numOk N l S.loc mNu ∧ numCnt l S.loc mNu ∧ ∀ r' b', (S.loc r' b').length < 2 ^ 31)⌝ -∗
    ghostMapAuth γ.cmds 1 mC -∗ ghostMapAuth γ.loc 1 mL -∗ ghostMapAuth γ.sync 1 mS -∗
    ghostMapAuth γ.acc 1 mA -∗ ghostMapAuth γ.pre 1 mP -∗ ghostMapAuth γ.com 1 mCo -∗
    ghostMapAuth γ.rep 1 mR -∗ ghostMapAuth γ.path 1 mPa -∗ ghostMapAuth γ.num 1 mNu ==∗
    ∃ (S' : PState) (mL' : GMap (Nat × Nat × Nat) CmdId) (mS' : GMap Nat SyncMsg)
      (mA' : GMap (Nat × Nat × CmdId) Unit) (mP' : GMap (Nat × Nat × CmdId) (List CmdId))
      (mCo' : GMap (Nat × Nat × CmdId) Unit) (mR' : GMap (Nat × Nat) Report)
      (mPa' : GMap (Nat × Nat × CmdId) (List CmdId)) (mNu' : GMap (Nat × Option (Nat × CmdId)) w64),
      ⌜S'.PInv N fr ∧ S'.syncRows N ∧ Repr S' mC mL' mS' mA' mP' mCo' mR' mPa' ∧ S'.cmds = S.cmds ∧
        S'.G = S.G ∧ S.le S' ∧ (∀ r', r' ≠ r → S'.rs r' = S.rs r') ∧
        (numOk N l S'.loc mNu' ∧ numCnt l S'.loc mNu') ∧ stepRel N S S' r e⌝ ∗
      ghostMapAuth γ.cmds 1 mC ∗ ghostMapAuth γ.loc 1 mL' ∗ ghostMapAuth γ.sync 1 mS' ∗
      ghostMapAuth γ.acc 1 mA' ∗ ghostMapAuth γ.pre 1 mP' ∗ ghostMapAuth γ.com 1 mCo' ∗
      ghostMapAuth γ.rep 1 mR' ∗ ghostMapAuth γ.path 1 mPa' ∗ ghostMapAuth γ.num 1 mNu' ∗
      Q (S'.rs r))

theorem predsOf_rep_head {N : Nat} {mW : GMap PNode (List w64)} {l : List GoString} {r k : Nat}
    {e : PEv} {W' : List w64} (hr : r < N) (hk : nodeOf l r = some k)
    (hW : mW.lookup (PNode.rep k) = some (encP e ++ W')) (he : PEvWf e) :
    predsOf N mW l (.rep r) = e :: decodeP W' := by
  simp only [predsOf, if_pos hr, hk, hW, Option.getD_some]
  exact decodeP_enc he W'

theorem predsOf_rep_upd {N : Nat} {mW : GMap PNode (List w64)} {l : List GoString} {r k : Nat}
    {W' : List w64} (hnd : l.Nodup) (hr : r < N) (hk : nodeOf l r = some k) :
    Cut.upd (predsOf N mW l) (.rep r) (decodeP W') = predsOf N (mW.insert (PNode.rep k) W') l := by
  funext d
  unfold Cut.upd
  cases d with
  | cl k' =>
    simp only [reduceCtorEq, if_false, predsOf]
    split
    · rw [GMap.lookup_insert_ne _ _ (by simp)]
    · rfl
  | rep r' =>
    by_cases e : r' = r
    · subst e; simp [predsOf, hr, hk]
    · simp only [Nd.rep.injEq, e, if_false, predsOf]
      split
      · cases h : nodeOf l r' with
        | none => rfl
        | some k' =>
          simp only
          have hkk : PNode.rep k ≠ PNode.rep k' := by
            intro hh; cases hh; exact e (nodeOf_inj hnd h hk)
          rw [GMap.lookup_insert_ne _ _ hkk]
      · rfl

attribute [local instance] cfg_timeless_acc in
/-- **L2's part across a replica's real step** (its predicted event `e`, the head of its node's
future words): the node's half loses `e`'s words; the strategy follows (`StratOk.rep`; the first
replica step after a client event starts it, with nothing committed). -/
theorem l2_rep_step (E : CoPset) (N : Nat) (fr : Bool) (l : List GoString) (r k : Nat)
    (S S' : PState) (sh : SHist) (e : PEv) (W' : List w64) (hr : r < N)
    (hk : nodeOf l r = some k) (hnd : l.Nodup) (he : PEvWf e) (hI : S.PInv N fr)
    (hH : HistOk N fr sh S) (hreg : ∀ x cm, Ev.inv x cm ∈ SHist.hist sh → S.cmds x = some cm)
    (hrel : stepRel N S S' r (some e)) :
    cfg γc γm N fr l ∗ ▷ l2Inv γ γc γm γl S sh ∗
      ghostMapElem γ.pred (PNode.rep k) (DFrac.own (1 : Qp).half) (encP e ++ W') ⊢
    |={E}=> ▷ l2Inv γ γc γm γl S' sh ∗
      ghostMapElem γ.pred (PNode.rep k) (DFrac.own (1 : Qp).half) W' := by
  obtain ⟨P, hok, rfl⟩ := hrel
  have hn : Nd.rep r ∈ l2Nodes N := by unfold l2Nodes; simp [hr]
  iintro ⟨#Hcfg, Hown, Hw⟩
  unfold l2Inv
  icases Hown with ⟨%mG, %mW, %mRg, %G, %mSl, HG, HmG, HGs, HRg, >HW, >%HRgW, >HWs, HH2, Hlin, HSl, HSls, #Hph⟩
  ihave %HlkW := ghost_map_lookup $$ HW Hw
  icases (BigSepM.bigSepM_insert_acc
    (show Iris.Std.PartialMap.get? mW (PNode.rep k) = some (encP e ++ W') from HlkW))
    $$ HWs with ⟨⟨Ht, Hw2, #Hr⟩, HWs⟩
  ihave Hwf := (ghostMapElem_halves γ.pred (PNode.rep k) (encP e ++ W')).2 $$ [Hw Hw2]
  · isplitl [Hw]
    · iexact Hw
    · iexact Hw2
  imod ghost_map_update W' $$ HW Hwf with ⟨HW, Hwf⟩
  icases (ghostMapElem_halves γ.pred (PNode.rep k) W').1 $$ Hwf with ⟨Hw, Hw2⟩
  ihave HWs := HWs $$ %W' [Ht Hw2]
  · iframe Ht Hw2 Hr
  have hhd := predsOf_rep_head (N := N) (l := l) hr hk HlkW he
  have hreg' : ∀ n, (mW.lookup n).isSome → ((mW.insert (PNode.rep k) W').lookup n).isSome := by
    intro n h; rw [GMap.lookup_insert_eq_iff]; split
    · rfl
    · exact h
  iframe Hw
  imodintro
  inext
  iexists mG, mW.insert (PNode.rep k) W', mRg, G, mSl
  iframe HG HmG HGs HRg HW HWs HH2 Hlin HSl HSls
  isplitr
  · ipureintro
    intro n
    rw [HRgW, GMap.lookup_insert_eq_iff]
    split
    · next ee => subst ee; rw [HlkW]; rfl
    · rfl
  icases Hph with (%Ha | ⟨%c0, #Hc0, %Hb, (%Hb1 | ⟨%fr0, %l0, #Hcfg0, %Hb2⟩)⟩)
  · ileft; ipureintro; exact Ha
  · ihave %Hcc := cfg_conf N fr l c0 $$ [Hcfg Hc0]
    · iframe Hcfg Hc0
    obtain ⟨hN, -⟩ := Hcc
    iright; iexists c0; iframe Hc0
    isplitr
    · ipureintro; exact ⟨fun n hn => hreg' n (Hb.1 n hn), Hb.2⟩
    iright; iexists fr, l
    rw [hN]
    iframe Hcfg
    ipureintro
    obtain ⟨-, hG0, hnr⟩ := Hb1
    subst hG0
    have h0 : StratOk N fr (l2Nodes N) S sh (predsOf N mW l) [] :=
      ⟨hI, hH, hreg, List.nil_prefix, by simp, fun x v h => absurd h (hnr x v)⟩
    have := StratOk.rep h0 hn hhd hok
    rw [predsOf_rep_upd hnd hr hk] at this
    exact this
  · ihave %Hag := cfg_agree (γc := γc) (γm := γm) c0.n N fr0 fr l0 l $$ [Hcfg0 Hcfg]
    · iframe Hcfg0 Hcfg
    obtain ⟨hN, rfl, rfl⟩ := Hag
    iright; iexists c0; iframe Hc0
    isplitr
    · ipureintro; exact ⟨fun n hn => hreg' n (Hb.1 n hn), Hb.2⟩
    iright; iexists fr0, l0
    iframe Hcfg0
    ipureintro
    rw [hN] at Hb2 ⊢
    have := StratOk.rep Hb2 hn hhd hok
    rw [predsOf_rep_upd hnd hr hk] at this
    exact this

/-- **The generic replica step, with the numbering** (change log C22): replica `r` (node `k`, in
the configuration `N fr l`), with its node state's half `st`, runs a step's update; its node
state becomes the step's. -/
theorem node_stepN (E : CoPset) (hE : ↑spN ⊆ E) (N : Nat) (fr : Bool) (l : List GoString)
    (r k : Nat) (st : RState) (ev : Option (PEv × List w64)) (Q : RState → IProp netDistGF)
    (hr : r < N) (hk : nodeOf l r = some k) :
    inv γ γc γm γl ∗ cfg γc γm N fr l ∗ nodeSt γ k (1 : Qp).half st ∗ predPre γ k ev ∗
      stepUpdN γ N fr l r st (ev.map Prod.fst) Q ⊢
    |={E}=> ∃ st', nodeSt γ k (1 : Qp).half st' ∗ predPost γ k ev ∗ Q st' := by
  unfold inv stepUpdN
  iintro ⟨#Hinv, #Hcfg, Hst, Hpre, Hupd⟩
  ihave %Hnd := cfg_nodup N fr l $$ Hcfg
  iinv Hinv with Hi Hclose
  unfold invBody
  icases Hi with ⟨%S, %mC, %mL, %mS, %mA, %mP, %mCo, %mR, %mN, %sh, %mD, %mQ, %mK, %mPa, >HC, >HL, >HS, >HA, >HP, >HCo, >HRp, >HN, HH, HD, Hown, HQ, HK, >HPa, >%Hrepr, >Hnodes, >Hproto, HQs, >%Hcl, >%Hdom, Hcmds, Hconns, HNu⟩
  -- the replica's node entry
  unfold nodeSt
  ihave %HlkN := ghost_map_lookup $$ HN Hst
  -- the configured protocol state (switching from the empty disjunct if needed)
  ihave %HS0 : ⌜∃ S0 : PState, S0.PInv N fr ∧ S0.syncRows N ∧ Repr S0 mC mL mS mA mP mCo mR mPa ∧
      S0.cmds = S.cmds ∧ S0.G = S.G ∧ S0.loc = S.loc ∧
      (∀ r' k', r' < N → nodeOf l r' = some k' → mN.lookup k' = some (S0.rs r')) ∧
      HistOk N fr sh S0 ∧ decOk N S0 mD ∧ S0 = S⌝ $$ [Hproto]
  · icases Hproto with (%H | ⟨%N', %fr', %l', #Hcfg', %H⟩)
    · ipureintro
      refine ⟨{ S with rs := fun _ => RState.init }, PState.PInv_emptyInit S H.1 N fr,
        fun b M h => by simp [H.1.2.1] at h, ⟨Hrepr.cmds, Hrepr.loc, Hrepr.sync, Hrepr.acc, Hrepr.pre, Hrepr.path, Hrepr.com,
          Hrepr.rep⟩, rfl, rfl, rfl, fun r' k' _ hk' => ?_,
        HistOk_mono (H.2.2.1 N fr) (PState.le_rs _) rfl,
        (fun x v hx => by rw [H.2.2.2 x] at hx; cases hx), PState.empty_rs S H.1⟩
      rw [H.2.1 k', ite_eq_left_iff.mpr (fun h => absurd (nodeOf_lt hk') h)]
    · ihave %Hag := cfg_agree (γc := γc) (γm := γm) N N' fr fr' l l' $$ [Hcfg Hcfg']
      · isplitl []
        · iexact Hcfg
        · iexact Hcfg'
      obtain ⟨rfl, rfl, rfl⟩ := Hag
      ipureintro
      exact ⟨S, H.1, H.2.2.1, Hrepr, rfl, rfl, rfl, H.2.1, H.2.2.2.1, H.2.2.2.2, rfl⟩
  obtain ⟨S0, HI0, Hsr0, Hrepr0, Hc0, HG0, Hl0, Hnodes0, HH0, HD0, hS0⟩ := HS0
  subst hS0
  -- the numbering (change log C22): `numOk` against the configuration
  iunfold numInv at HNu
  icases HNu with ⟨%mNu, >HNu, >HNo⟩
  ihave %Hnum0 : ⌜numOk N l S0.loc mNu ∧ numCnt l S0.loc mNu⌝ $$ [HNo]
  · icases HNo with (%Hno | ⟨%N2, %fr2, %l2, #Hcfg2, %Hok⟩)
    · ipureintro
      refine ⟨fun r' b' x s h => (by rw [Hno.1] at h; cases h), fun r' k' n _ hn => ?_⟩
      have := Hno.2 k' n hn
      omega
    · ihave %Hag := cfg_agree (γc := γc) (γm := γm) N N2 fr fr2 l l2 $$ [Hcfg Hcfg2]
      · isplitl []
        · iexact Hcfg
        · iexact Hcfg2
      obtain ⟨rfl, rfl, rfl⟩ := Hag
      ipureintro; rw [Hl0]; exact Hok
  have Hst0 : S0.rs r = st := by
    have := Hnodes0 r k hr hk
    rw [HlkN] at this; cases this; rfl
  -- the step
  -- D22 (2): the sequences are shorter than `2 ^ 31` (D13's bound)
  have Hlen0 : ∀ r' b', (S0.loc r' b').length < 2 ^ 31 :=
    loc_bound HI0 (fun x => (Hrepr0.cmds x).trans (by rw [Hc0])) Hcl Hdom.2
  imod Hupd $$ %S0 %mC %mL %mS %mA %mP %mCo %mR %mPa %mNu
      %(⟨HI0, Hsr0, Hst0, Hrepr0, Hnum0.1, Hnum0.2, Hlen0⟩ : _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
      HC HL HS HA HP HCo HRp HPa HNu
    with ⟨%S', %mL', %mS', %mA', %mP', %mCo', %mR', %mPa', %mNu', %HH',
      HC, HL, HS, HA, HP, HCo, HRp, HPa, HNu, HQ'⟩
  obtain ⟨HI', Hsr', Hrepr', Hc', HG', Hle', Hrs', Hnum', hrel⟩ := HH'
  -- the history and the decided results (change log C12): the step is an extension
  have HHist' : HistOk N fr sh S' := HistOk_mono HH0 Hle' Hc'
  have HD' : decOk N S' mD := fun x v hx => by
    obtain ⟨b, hpc, hres⟩ := HD0 x v hx
    obtain ⟨hpc', hres'⟩ := PState.possiblyChosen_le HI0 Hle' hpc
    exact ⟨b, hpc', hres'.trans hres⟩
  -- the node's entry: both halves to the new state
  icases (BigSepM.bigSepM_insert_acc
    (show Iris.Std.PartialMap.get? mN k = some st from HlkN)) $$ Hnodes with ⟨Hst2, Hnodes⟩
  ihave Hfull := (ghostMapElem_halves γ.node k st).2 $$ [Hst Hst2]
  · isplitl [Hst]
    · iexact Hst
    · iexact Hst2
  imod ghost_map_update (S'.rs r) $$ HN Hfull with ⟨HN, Hfull⟩
  icases (ghostMapElem_halves γ.node k (S'.rs r)).1 $$ Hfull with ⟨Hst, Hst2⟩
  ihave Hnodes := Hnodes $$ %(S'.rs r) Hst2
  -- L2: the node's predicted event (if any) and the strategy (`l2_rep_step`)
  ihave Hpair : |={E \ ↑spN}=> ▷ l2Inv γ γc γm γl S' sh ∗ predPost γ k ev $$ [Hown Hpre]
  · rcases ev with _ | ⟨e, W'⟩
    · have hS' : S' = S0 := hrel
      subst hS'
      iframe Hown
      iunfold predPost
      imodintro; itrivial
    · iunfold predPre at Hpre
      icases Hpre with ⟨%he, Hw⟩
      iunfold predPost
      iapply (l2_rep_step (E \ ↑spN) N fr l r k S0 S' sh e W' hr hk Hnd he HI0 HH0
        (fun x cm h => (Hrepr0.cmds x).symm.trans (Hdom.1 x cm h)) hrel)
      iframe Hcfg Hown Hw
  imod Hpair with ⟨Hown, Hpost⟩
  imod Hclose $$ [HC HL HS HA HP HCo HRp HN HH HD Hown HQ HK HPa Hnodes HQs Hcmds Hconns HNu]
    with -
  · inext
    iexists S', mC, mL', mS', mA', mP', mCo', mR', mN.insert k (S'.rs r), sh, mD, mQ, mK,
      mPa'
    iframe
    isplitr
    · ipureintro; exact Hrepr'
    isplitr
    · iright
      iexists N, fr, l
      iframe Hcfg
      ipureintro
      refine ⟨HI', fun r' k' hr' hk' => ?_, Hsr', HHist', HD'⟩
      rw [GMap.lookup_insert_eq_iff]
      by_cases hkk : k = k'
      · subst hkk
        have := nodeOf_inj Hnd hk hk'
        subst this
        simp
      · rw [if_neg hkk, Hrs' r' (fun h => hkk (by subst h; rw [hk] at hk'; cases hk'; rfl))]
        exact Hnodes0 r' k' hr' hk'
    isplitr
    · ipureintro; exact Hcl
    isplitr
    · ipureintro; exact Hdom
    unfold numInv
    iexists mNu'
    iframe HNu
    iright
    iexists N, fr, l
    iframe Hcfg
    ipureintro; exact Hnum'
  imodintro
  iexists S'.rs r
  iframe

/-- **The generic replica step**: replica `r` (node `k`, in the configuration `N fr l`), with
its node state's half `st`, runs a step's update; its node state becomes the step's (the
numbering unchanged: `node_stepN`). -/
theorem node_step (E : CoPset) (hE : ↑spN ⊆ E) (N : Nat) (fr : Bool) (l : List GoString)
    (r k : Nat) (st : RState) (ev : Option (PEv × List w64)) (Q : RState → IProp netDistGF)
    (hr : r < N) (hk : nodeOf l r = some k) :
    inv γ γc γm γl ∗ cfg γc γm N fr l ∗ nodeSt γ k (1 : Qp).half st ∗ predPre γ k ev ∗
      stepUpd γ N fr r st (ev.map Prod.fst) Q ⊢
    |={E}=> ∃ st', nodeSt γ k (1 : Qp).half st' ∗ predPost γ k ev ∗ Q st' := by
  iintro ⟨#Hinv, #Hcfg, Hst, Hpre, Hupd⟩
  iapply node_stepN E hE N fr l r k st ev Q hr hk
  iframe Hinv Hcfg Hst Hpre
  unfold stepUpdN stepUpd
  iintro %S %mC %mL %mS %mA %mP %mCo %mR %mPa %mNu %HH HC HL HS HA HP HCo HRp HPa HNu
  obtain ⟨HI, Hsr, Hrs, Hrepr, Hnum⟩ := HH
  imod Hupd $$ %S %mC %mL %mS %mA %mP %mCo %mR %mPa %(⟨HI, Hsr, Hrs, Hrepr⟩ : _ ∧ _ ∧ _ ∧ _)
      HC HL HS HA HP HCo HRp HPa
    with ⟨%S', %mL', %mS', %mA', %mP', %mCo', %mR', %mPa', %HH',
      HC, HL, HS, HA, HP, HCo, HRp, HPa, HQ⟩
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := HH'
  imodintro
  iexists S', mL', mS', mA', mP', mCo', mR', mPa', mNu
  iframe
  ipureintro
  exact ⟨a1, a2, a3, a4, a5, a6, a7, ⟨numOk_mono Hnum.1 a6.loc, numCnt_mono Hnum.2.1 a6.loc⟩, a8⟩

/-! ## The numbering (change log C22, M3): pure helpers -/

/-- The numbering after replica `r` (node `k`) numbered `x` in `b`: `n` if it leads (and its
next number becomes `n + 1`), else 0. -/
def numUpd (mNu : GMap (Nat × Option (Nat × CmdId)) w64) (r b k : Nat) (x : CmdId) (n : w64)
    (ld : Bool) : GMap (Nat × Option (Nat × CmdId)) w64 :=
  if ld then (mNu.insert (r, some (b, x)) n).insert (k, none) (n + 1)
  else mNu.insert (r, some (b, x)) (W64 (-1))

omit [GoGlobalContext] G in
theorem numUpd_num (mNu : GMap (Nat × Option (Nat × CmdId)) w64) (r b k : Nat) (x : CmdId)
    (n : w64) (ld : Bool) (r' b' : Nat) (y : CmdId) :
    (numUpd mNu r b k x n ld).lookup (r', some (b', y)) =
      if r = r' ∧ b = b' ∧ x = y then some (if ld then n else W64 (-1))
      else mNu.lookup (r', some (b', y)) := by
  unfold numUpd
  cases ld <;> simp [GMap.lookup_insert_eq_iff]

omit [GoGlobalContext] G in
theorem numUpd_hi (mNu : GMap (Nat × Option (Nat × CmdId)) w64) (r b k : Nat) (x : CmdId)
    (n : w64) (ld : Bool) (k' : Nat) :
    (numUpd mNu r b k x n ld).lookup (k', none) =
      if ld = true ∧ k = k' then some (n + 1) else mNu.lookup (k', none) := by
  unfold numUpd
  cases ld <;> simp [GMap.lookup_insert_eq_iff]

omit [GoGlobalContext] G in
/-- **Numbering a handled command keeps `numOk`**: `x` appended to `r`'s sequence of `b`; as
`b`'s leader, numbered with its next number `n` (above all its numbers, `n + 1` not
overflowing). -/
theorem numOk_handle {N : Nat} {l : List GoString} {loc : Nat → Nat → List CmdId}
    {mNu : GMap (Nat × Option (Nat × CmdId)) w64} (hnd : l.Nodup) (r b k : Nat) (x : CmdId)
    (n : w64) (ld : Bool) (h : numOk N l loc mNu) (hx : x ∉ loc r b)
    (hk : nodeOf l r = some k) (hhi : mNu.lookup (k, none) = some n)
    (hld : ld = true ↔ leaderOf N b = r) (h0 : 0 ≤ sint.Z n)
    (hov : ld = true → sint.Z (n + 1) = sint.Z n + 1) :
    numOk N l (fun r' b' => if r' = r ∧ b' = b then loc r b ++ [x] else loc r' b')
      (numUpd mNu r b k x n ld) := by
  have hidx : ∀ z ∈ loc r b, (loc r b ++ [x]).idxOf z = (loc r b).idxOf z := fun z hz => by
    rw [List.idxOf_append, if_pos hz]
  have hidxx : (loc r b ++ [x]).idxOf x = (loc r b).length := by
    rw [List.idxOf_append, if_neg hx]; simp
  -- the leader's old numbers in `b` are below `n`
  have hbelow : ld = true → ∀ y s, mNu.lookup (r, some (b, y)) = some s →
      y ∈ loc r b ∧ sint.Z s < sint.Z n := fun hl y s hy => by
    obtain ⟨hm, hL⟩ := h r b y s hy
    obtain ⟨-, hh, -⟩ := hL (hld.mp hl).symm
    obtain ⟨n', hn', hlt⟩ := hh k hk
    rw [hhi] at hn'; cases hn'
    exact ⟨hm, hlt⟩
  intro r' b' y s hy
  rw [numUpd_num] at hy
  split at hy
  · -- the new number
    rename_i he
    obtain ⟨rfl, rfl, rfl⟩ := he
    refine ⟨by simp, fun hL => ?_⟩
    have hl : ld = true := hld.mpr hL.symm
    subst hl
    simp only [if_true] at hy
    cases hy
    simp only [_root_.and_self, ite_true]
    refine ⟨h0, fun k' hk' => ⟨n + 1, ?_, ?_⟩, fun y' s' hy' => ?_⟩
    · rw [hk] at hk'; cases hk'; rw [numUpd_hi]; simp
    · rw [hov rfl]; omega
    · rw [numUpd_num] at hy'
      split at hy'
      · rename_i he; obtain ⟨-, -, rfl⟩ := he; cases hy'; simp
      · rename_i he
        obtain ⟨hm', hlt'⟩ := hbelow rfl y' s' hy'
        rw [hidxx, hidx y' hm']
        have := List.idxOf_lt_length_of_mem hm'
        constructor
        · intro hle; omega
        · intro hle; omega
  · -- an old number
    rename_i hne
    obtain ⟨hm, hL⟩ := h r' b' y s hy
    have hloc : ∀ z ∈ loc r' b', z ∈ (if r' = r ∧ b' = b then loc r b ++ [x] else loc r' b') :=
      fun z hz => by
        split
        · rename_i hrb; obtain ⟨rfl, rfl⟩ := hrb; exact List.mem_append_left _ hz
        · exact hz
    have hidx' : ∀ z ∈ loc r' b',
        (if r' = r ∧ b' = b then loc r b ++ [x] else loc r' b').idxOf z = (loc r' b').idxOf z :=
      fun z hz => by
        split
        · rename_i hrb; obtain ⟨rfl, rfl⟩ := hrb; exact hidx z hz
        · rfl
    refine ⟨hloc y hm, fun hL' => ?_⟩
    obtain ⟨h0', hh', hord⟩ := hL hL'
    refine ⟨h0', fun k' hk' => ?_, fun y2 s2 hy2 => ?_⟩
    · obtain ⟨n', hn', hlt⟩ := hh' k' hk'
      rw [numUpd_hi]
      split
      · rename_i hkk
        obtain ⟨hl, rfl⟩ := hkk
        rw [hhi] at hn'; cases hn'
        refine ⟨_, rfl, ?_⟩
        rw [hov hl]; omega
      · exact ⟨n', hn', hlt⟩
    · rw [numUpd_num] at hy2
      split at hy2
      · -- the other is the new number: `r` leads `b`, `y` came first
        rename_i he
        obtain ⟨rfl, rfl, rfl⟩ := he
        have hl : ld = true := hld.mpr hL'.symm
        subst hl
        simp only [if_true] at hy2
        cases hy2
        obtain ⟨hmy, hlt⟩ := hbelow rfl y s hy
        simp only [_root_.and_self, ite_true]
        rw [hidxx, hidx y hmy]
        have := List.idxOf_lt_length_of_mem hmy
        constructor
        · intro; omega
        · intro; omega
      · rw [hidx' y hm, hidx' y2 (h r' b' y2 s2 hy2).1]
        exact hord y2 s2 hy2

/-- **Numbering a handled command keeps the count** (D22 (2)): `x` (new) appended to `r`'s
sequence of `b < 2 ^ 31`; as `b`'s leader the node's next number grows by one. -/
theorem numCnt_handle {l : List GoString} {loc : Nat → Nat → List CmdId}
    {mNu : GMap (Nat × Option (Nat × CmdId)) w64} (hnd : l.Nodup) (r b k : Nat) (x : CmdId)
    (n : w64) (ld : Bool) (h : numCnt l loc mNu) (hk : nodeOf l r = some k)
    (hhi : mNu.lookup (k, none) = some n) (hb : b < 2 ^ 31)
    (hov : ld = true → sint.Z (n + 1) = sint.Z n + 1) :
    numCnt l (fun r' b' => if r' = r ∧ b' = b then loc r b ++ [x] else loc r' b')
      (numUpd mNu r b k x n ld) := by
  have hle : ∀ r', ∀ b', (loc r' b').length ≤
      (if r' = r ∧ b' = b then loc r b ++ [x] else loc r' b').length := fun r' b' => by
    split
    · rename_i e; obtain ⟨rfl, rfl⟩ := e; simp
    · exact Nat.le_refl _
  intro r' k' n' hk' hn'
  rw [numUpd_hi] at hn'
  split at hn'
  · rename_i e
    obtain ⟨hl, rfl⟩ := e
    cases hn'
    have hrr : r' = r := nodeOf_inj hnd hk' hk
    subst hrr
    have h1 := h r' k n hk hhi
    have h2 := locSum_succ (f := fun b' => (loc r' b').length)
      (g := fun b' => (if r' = r' ∧ b' = b then loc r' b ++ [x] else loc r' b').length)
      (hle r') b (by simp) (2 ^ 31) hb
    rw [hov hl]
    simp only [] at h2 ⊢
    omega
  · refine Int.le_trans (h r' k' n' hk' hn') ?_
    exact_mod_cast locSum_mono (hle r') _

/-! ## The steps -/

omit [GoGlobalContext] G in
/-- `syncRows` is kept by a step that keeps the `MSync`s and only adds rows. -/
theorem syncRows_mono {S S' : PState} {N : Nat} (H : S.syncRows N) (hs : S'.sync = S.sync)
    (hrows : ∀ r p, p ∈ (S.rs r).locR → p ∈ (S'.rs r).locR) : S'.syncRows N := by
  intro b M h
  rw [hs] at h
  obtain ⟨l, hl⟩ := H b M h
  exact ⟨l, hrows _ _ hl⟩

/-- The replica's new state after handling `x` in `b` (`PState.handle`'s row). -/
def RState.handled (st : RState) (b : Nat) (x : CmdId) : RState :=
  { st with locR := (b, st.locAt b ++ [x]) :: st.locR }

omit [GoGlobalContext] G in
theorem Repr_handle {S : PState} {mC mL mS mA mP mCo mR mPa}
    (H : Repr S mC mL mS mA mP mCo mR mPa) (r b : Nat) (x : CmdId) :
    Repr (S.handle r b x) mC (mL.insert (r, b, (S.loc r b).length) x) mS mA mP mCo mR mPa := by
  refine ⟨H.cmds, fun r' b' i => ?_, H.sync, H.acc, H.pre, H.path, H.com, H.rep⟩
  rw [GMap.lookup_insert_eq_iff]
  by_cases hrb : r' = r ∧ b' = b
  · obtain ⟨rfl, rfl⟩ := hrb
    have hl : (S.handle r' b' x).loc r' b' = S.loc r' b' ++ [x] := by simp [PState.handle]
    rw [hl]
    by_cases hi : (S.loc r' b').length = i
    · subst hi; simp
    · rw [if_neg (by simp [hi]), H.loc]
      rcases Nat.lt_or_gt_of_ne hi with h | h
      · rw [List.getElem?_append_right (by omega)]
        simp [List.getElem?_eq_none (by omega : (S.loc r' b').length ≤ i)]
        omega
      · rw [List.getElem?_append_left h]
  · rw [if_neg (by rintro ⟨rfl, rfl, -⟩; exact hrb ⟨rfl, rfl⟩), H.loc,
      PState.handle_loc_ne r b x r' b' hrb]

/-- **Handling a proposal** (`handleProposal`, the run loop): replica `r` appends the registered
command `x` to its sequence of its ballot `b` (it has not handled `x` in `b`; from ballot 1 its
sequence starts with the ballot's `MSync`'s order). It gets `x`'s place in its sequence. -/
theorem upd_handle (E : CoPset) (hE : ↑spN ⊆ E) (N : Nat) (fr : Bool) (l : List GoString)
    (r k : Nat) (st : RState) (x : CmdId) (c : Cmd) (hr : r < N) (hk : nodeOf l r = some k)
    (hn : x ∉ st.locAt st.ballot) (W' : List w64) :
    inv γ γc γm γl ∗ cfg γc γm N fr l ∗ nodeSt γ k (1 : Qp).half st ∗ predPre γ k (some (PEv.handle st.ballot x c, W')) ∗ cmdIs γ x c ∗
      (⌜st.ballot = 0⌝ ∨ ∃ M, syncIs γ st.ballot M ∗ ⌜syncOrder M <+: st.locAt st.ballot⌝) ⊢
    |={E}=> nodeSt γ k (1 : Qp).half (st.handled st.ballot x) ∗ predPost γ k (some (PEv.handle st.ballot x c, W')) ∗
      locAt γ r st.ballot (st.locAt st.ballot).length x := by
  iintro ⟨#Hinv, #Hcfg, Hst, Hpre, #Hc, #Hb⟩
  imod node_step E hE N fr l r k st (some (PEv.handle st.ballot x c, W'))
    (fun s => iprop(⌜s = st.handled st.ballot x⌝ ∗ locAt γ r st.ballot (st.locAt st.ballot).length x))
    hr hk $$ [Hst Hpre] with ⟨%st', Hst, Hpost, %Heq, #Hl⟩
  · iframe Hinv Hcfg Hst Hpre
    unfold stepUpd
    iintro %S %mC %mL %mS %mA %mP %mCo %mR %mPa %HH HC HL HS HA HP HCo HRp HPa
    obtain ⟨HI, Hsr, Hrs, Hrepr⟩ := HH
    unfold cmdIs
    ihave %Hlc := ghost_map_lookup $$ HC Hc
    have hloc : S.loc r st.ballot = st.locAt st.ballot := by rw [(HI.rows_ok r _).1, Hrs]
    ihave %Hbase : ⌜st.ballot > 0 → S.sync st.ballot ≠ none ∧ S.base st.ballot <+: S.loc r st.ballot⌝
      $$ [HS]
    · icases Hb with (%Hb0 | ⟨%M, #HM, %HMp⟩)
      · ipureintro; omega
      · unfold syncIs
        ihave %HlkS := ghost_map_lookup $$ HS HM
        ipureintro
        intro _
        rw [Hrepr.sync] at HlkS
        refine ⟨by rw [HlkS]; simp, ?_⟩
        unfold PState.base; rw [HlkS, hloc]; exact HMp
    have hfresh : mL.lookup (r, st.ballot, (S.loc r st.ballot).length) = none := by
      rw [Hrepr.loc]; simp
    imod ghost_map_insert_persist _ x hfresh $$ HL with ⟨HL, #Hnew⟩
    imodintro
    iexists S.handle r st.ballot x, _, mS, mA, mP, mCo, mR, mPa
    iframe
    isplitr
    · ipureintro
      refine ⟨PState.PInv_handle HI r _ x (by rw [← Hrepr.cmds]; simp [Hlc]) (by rw [hloc]; exact hn)
        hr (by rw [Hrs]) Hbase, syncRows_mono Hsr rfl (fun r' p hp => by
          simp only [PState.handle]; split <;> simp [hp]), Repr_handle Hrepr r _ x, rfl, rfl, PState.le_handle _ _ _, fun r' h => ?_, ⟨[], ⟨⟨by rw [← Hrepr.cmds]; simp [Hlc], by rw [hloc]; exact hn, hr, by rw [Hrs], Hbase⟩, trivial⟩, rfl⟩⟩
      simp [PState.handle, h]
    isplitr
    · ipureintro
      simp only [PState.handle, if_true, Hrs, RState.handled, hloc]
    · unfold locAt; rw [hloc]; iexact Hnew
  subst Heq
  imodintro
  iframe Hst Hpost
  iexact Hl

/-- The numbering's ghost update (helper of `upd_handleN`). -/
theorem numUpd_ghost (mNu : GMap (Nat × Option (Nat × CmdId)) w64) (r b k : Nat) (x : CmdId)
    (n : w64) (ld : Bool) :
    ⊢ ghostMapAuth γ.num 1 (mNu.insert (r, some (b, x)) (if ld then n else W64 (-1))) -∗
      ghostMapElem γ.num (k, (none : Option (Nat × CmdId))) (DFrac.own 1) n ==∗
    ghostMapAuth γ.num 1 (numUpd mNu r b k x n ld) ∗
      ghostMapElem γ.num (k, (none : Option (Nat × CmdId))) (DFrac.own 1)
        (if ld then n + 1 else n) := by
  cases ld
  · unfold numUpd
    simp only [Bool.false_eq_true, if_false]
    iintro H1 H2
    imodintro
    iframe
  · unfold numUpd
    simp only [if_true]
    iintro H1 H2
    imod ghost_map_update (n + 1) $$ H1 H2 with ⟨H1, H2⟩
    imodintro
    iframe

/-- **Handling a proposal, numbered** (change log C22, M3: `handleProposal`, the run loop):
`upd_handle`, and replica `r` (node `k`, its next number `n`) numbers `x` in its ballot `b`:
`n` if it leads `b` (its next number becomes `n + 1`), else 0 (the `Seqnum` of a follower's
fast ack). -/
theorem upd_handleN (E : CoPset) (hE : ↑spN ⊆ E) (N : Nat) (fr : Bool) (l : List GoString)
    (r k : Nat) (st : RState) (x : CmdId) (c : Cmd) (n : w64) (ld : Bool) (hr : r < N)
    (hk : nodeOf l r = some k) (hn : x ∉ st.locAt st.ballot)
    (hld : ld = true ↔ leaderOf N st.ballot = r) (h0 : 0 ≤ sint.Z n)
    (hb : st.ballot < 2 ^ 31) (W' : List w64) :
    inv γ γc γm γl ∗ cfg γc γm N fr l ∗ nodeSt γ k (1 : Qp).half st ∗ predPre γ k (some (PEv.handle st.ballot x c, W')) ∗ cmdIs γ x c ∗
      (⌜st.ballot = 0⌝ ∨ ∃ M, syncIs γ st.ballot M ∗ ⌜syncOrder M <+: st.locAt st.ballot⌝) ∗
      numHi γ k n ⊢
    |={E}=> nodeSt γ k (1 : Qp).half (st.handled st.ballot x) ∗ predPost γ k (some (PEv.handle st.ballot x c, W')) ∗
      locAt γ r st.ballot (st.locAt st.ballot).length x ∗
      numIs γ r st.ballot x (if ld then n else W64 (-1)) ∗ numHi γ k (if ld then n + 1 else n) ∗
      ⌜ld = true → sint.Z (n + 1) = sint.Z n + 1⌝ := by
  iintro ⟨#Hinv, #Hcfg, Hst, Hpre, #Hc, #Hb, Hhi⟩
  ihave %Hnd := cfg_nodup N fr l $$ Hcfg
  imod node_stepN E hE N fr l r k st (some (PEv.handle st.ballot x c, W'))
    (fun s => iprop(⌜s = st.handled st.ballot x⌝ ∗ locAt γ r st.ballot (st.locAt st.ballot).length x ∗
      numIs γ r st.ballot x (if ld then n else W64 (-1)) ∗ numHi γ k (if ld then n + 1 else n) ∗
      ⌜ld = true → sint.Z (n + 1) = sint.Z n + 1⌝))
    hr hk $$ [Hst Hpre Hhi] with ⟨%st', Hst, Hpost, %Heq, #Hl, #Hnum, Hhi, %Hov⟩
  · iframe Hinv Hcfg Hst Hpre
    unfold stepUpdN
    iintro %S %mC %mL %mS %mA %mP %mCo %mR %mPa %mNu %HH HC HL HS HA HP HCo HRp HPa HNu
    obtain ⟨HI, Hsr, Hrs, Hrepr, Hno, Hcnt, Hlen⟩ := HH
    unfold cmdIs
    ihave %Hlc := ghost_map_lookup $$ HC Hc
    have hloc : S.loc r st.ballot = st.locAt st.ballot := by rw [(HI.rows_ok r _).1, Hrs]
    ihave %Hbase : ⌜st.ballot > 0 → S.sync st.ballot ≠ none ∧ S.base st.ballot <+: S.loc r st.ballot⌝
      $$ [HS]
    · icases Hb with (%Hb0 | ⟨%M, #HM, %HMp⟩)
      · ipureintro; omega
      · unfold syncIs
        ihave %HlkS := ghost_map_lookup $$ HS HM
        ipureintro
        intro _
        rw [Hrepr.sync] at HlkS
        refine ⟨by rw [HlkS]; simp, ?_⟩
        unfold PState.base; rw [HlkS, hloc]; exact HMp
    have hfresh : mL.lookup (r, st.ballot, (S.loc r st.ballot).length) = none := by
      rw [Hrepr.loc]; simp
    imod ghost_map_insert_persist _ x hfresh $$ HL with ⟨HL, #Hnew⟩
    -- the number
    unfold numHi
    ihave %Hlhi := ghost_map_lookup $$ HNu Hhi
    -- D22 (2): the count bounds the next number below `2 ^ 62`: `n + 1` does not overflow
    have hov : ld = true → sint.Z (n + 1) = sint.Z n + 1 := fun _ => by
      have h1 := Hcnt r k n hk Hlhi
      have h2 := locSum_bound r (Hlen r)
      have h3 : sint.Z n ≤ 2 ^ 62 := by omega
      simp only [sint.Z] at h0 h3 ⊢
      rw [BitVec.toInt_add_of_not_saddOverflow]
      · simp
      · simp only [BitVec.saddOverflow, decide_eq_true_eq]; simp; omega
    have hxS : x ∉ S.loc r st.ballot := by rw [hloc]; exact hn
    have hnf : mNu.lookup (r, some (st.ballot, x)) = none := by
      cases h : mNu.lookup (r, some (st.ballot, x)) with
      | none => rfl
      | some s => exact absurd (Hno r st.ballot x s h).1 hxS
    imod ghost_map_insert_persist _ (if ld then n else W64 (-1)) hnf $$ HNu with ⟨HNu, #Hnn⟩
    imod numUpd_ghost (γ := γ) mNu r st.ballot k x n ld $$ HNu Hhi with ⟨HNu, Hhi⟩
    imodintro
    iexists S.handle r st.ballot x, _, mS, mA, mP, mCo, mR, mPa, numUpd mNu r st.ballot k x n ld
    iframe
    isplitr
    · ipureintro
      refine ⟨PState.PInv_handle HI r _ x (by rw [← Hrepr.cmds]; simp [Hlc]) (by rw [hloc]; exact hn)
        hr (by rw [Hrs]) Hbase, syncRows_mono Hsr rfl (fun r' p hp => by
          simp only [PState.handle]; split <;> simp [hp]), Repr_handle Hrepr r _ x, rfl, rfl,
        PState.le_handle _ _ _, fun r' h => ?_, ?_, ⟨[], ⟨⟨by rw [← Hrepr.cmds]; simp [Hlc], by rw [hloc]; exact hn, hr, by rw [Hrs], Hbase⟩, trivial⟩, rfl⟩⟩
      · simp [PState.handle, h]
      · unfold PState.handle
        exact ⟨numOk_handle Hnd r st.ballot k x n ld Hno hxS hk Hlhi hld h0 hov,
          numCnt_handle Hnd r st.ballot k x n ld Hcnt hk Hlhi hb hov⟩
    isplitr
    · ipureintro
      simp only [PState.handle, if_true, Hrs, RState.handled, hloc]
    unfold locAt numIs
    rw [hloc]
    iframe Hnew Hnn
    isplitl
    · cases ld
      · simp only [Bool.false_eq_true, if_false]
        iexact Hhi
      · simp only [if_true]
        iexact Hhi
    · ipureintro; exact hov
  subst Heq
  imodintro
  iframe Hst Hpost Hl Hnum Hhi
  ipureintro; exact Hov

/-- The lookups of a family of numbered commands (helper of `num_paths_all`). -/
theorem num_lookups_all (L b : Nat) (Λ : w64 → w64 → List CmdId → Prop)
    (mNu : GMap (Nat × Option (Nat × CmdId)) w64) (mPa : GMap (Nat × Nat × CmdId) (List CmdId))
    (mC : GMap CmdId Cmd) :
    ⊢ ghostMapAuth γ.num 1 mNu -∗ ghostMapAuth γ.path 1 mPa -∗ ghostMapAuth γ.cmds 1 mC -∗
      (□ ∀ (k s : w64) (P : List CmdId), ⌜Λ k s P⌝ -∗ ∃ (y : CmdId) (c : Cmd),
        numIs γ L b y s ∗ pathIs γ L b y P ∗ cmdIs γ y c ∗ ⌜c.key = k⌝) -∗
      ⌜∀ k s P, Λ k s P → ∃ y c, mNu.lookup (L, some (b, y)) = some s ∧
        mPa.lookup (L, b, y) = some P ∧ mC.lookup y = some c ∧ c.key = k⌝ := by
  iintro HNu HPa HC #Hs
  iapply pure_forall.2
  iintro %k
  iapply pure_forall.2
  iintro %s
  iapply pure_forall.2
  iintro %P
  by_cases hΛ : Λ k s P
  · ihave ⟨%y, %c, #Hn, #Hp, #Hc, %Hk⟩ := Hs $$ %k %s %P %hΛ
    unfold numIs pathIs cmdIs
    ihave %L1 := ghost_map_lookup $$ HNu Hn
    ihave %L2 := ghost_map_lookup $$ HPa Hp
    ihave %L3 := ghost_map_lookup $$ HC Hc
    ipureintro
    intro _
    exact ⟨y, c, L1, L2, L3, Hk⟩
  · ipureintro
    intro h
    exact absurd h hΛ

/-- **The leader's numbering against a family** (change log C22, M3; `num_paths` for every
member of a family `Λ` of numbered commands with their paths): `x`'s number is non-negative, its
path ends with it, and the paths of the key's members follow the numbers both ways. -/
theorem num_paths_all (E : CoPset) (hE : ↑spN ⊆ E) (N : Nat) (fr : Bool) (l : List GoString)
    (b : Nat) (x : CmdId) (s : w64) (P : List CmdId) (cx : Cmd)
    (Λ : w64 → w64 → List CmdId → Prop) :
    inv γ γc γm γl ∗ cfg γc γm N fr l ∗
      numIs γ (leaderOf N b) b x s ∗ pathIs γ (leaderOf N b) b x P ∗ cmdIs γ x cx ∗
      (□ ∀ (k s : w64) (P : List CmdId), ⌜Λ k s P⌝ -∗ ∃ (y : CmdId) (c : Cmd),
        numIs γ (leaderOf N b) b y s ∗ pathIs γ (leaderOf N b) b y P ∗ cmdIs γ y c ∗
        ⌜c.key = k⌝) ⊢
    |={E}=> ⌜0 ≤ sint.Z s ∧ P.getLast? = some x ∧ ∀ s' P', Λ cx.key s' P' →
      (sint.Z s ≤ sint.Z s' → P <+: P') ∧ (sint.Z s' ≤ sint.Z s → P' <+: P)⌝ := by
  unfold inv
  iintro ⟨#Hinv, #Hcfg, #Hnx, #Hpx, #Hcx, #Hs⟩
  iinv Hinv with Hi Hclose
  unfold invBody
  icases Hi with ⟨%S, %mC, %mL, %mS, %mA, %mP, %mCo, %mR, %mN, %sh, %mD, %mQ, %mK, %mPa, >HC, HL, HS, HA, HP, HCo, HRp, HN, HH, HD, Hown, HQ, HK, >HPa, >%Hrepr, Hnodes, >#Hproto, HQs, >%Hcl, >%Hdom, Hcmds, Hconns, HNu⟩
  iunfold numInv at HNu
  icases HNu with ⟨%mNu, >HNu, >#HNo⟩
  ihave %Hall := num_lookups_all (γ := γ) (leaderOf N b) b Λ mNu mPa mC $$ HNu HPa HC Hs
  unfold numIs pathIs cmdIs
  ihave %Lnx := ghost_map_lookup $$ HNu Hnx
  ihave %Lpx := ghost_map_lookup $$ HPa Hpx
  ihave %Lcx := ghost_map_lookup $$ HC Hcx
  ihave %Hres : ⌜0 ≤ sint.Z s ∧ P.getLast? = some x ∧ ∀ s' P', Λ cx.key s' P' →
      (sint.Z s ≤ sint.Z s' → P <+: P') ∧ (sint.Z s' ≤ sint.Z s → P' <+: P)⌝ $$ [Hproto HNo]
  · icases HNo with (%Hno | ⟨%N2, %fr2, %l2, #Hcfg2, %Hok⟩)
    · rw [Hno.1] at Lnx; cases Lnx
    icases Hproto with (%Hemp | ⟨%N1, %fr1, %l1, #Hcfg1, %Hpr⟩)
    · have := Hemp.1.2.2.2.2.1 (leaderOf N b) b x
      rw [← Hrepr.path] at this; rw [this] at Lpx; cases Lpx
    ihave %Hag1 := cfg_agree (γc := γc) (γm := γm) N N1 fr fr1 l l1 $$ [Hcfg Hcfg1]
    · isplitl []
      · iexact Hcfg
      · iexact Hcfg1
    ihave %Hag2 := cfg_agree (γc := γc) (γm := γm) N N2 fr fr2 l l2 $$ [Hcfg Hcfg2]
    · isplitl []
      · iexact Hcfg
      · iexact Hcfg2
    obtain ⟨rfl, rfl, rfl⟩ := Hag1
    obtain ⟨rfl, rfl, rfl⟩ := Hag2
    ipureintro
    have HI := Hpr.1
    rw [Hrepr.path] at Lpx
    rw [Hrepr.cmds] at Lcx
    obtain ⟨hxl, hxb, hxlast, hxL, -⟩ := HI.path_ok _ _ _ _ Lpx
    obtain ⟨-, hlx⟩ := Hok.1 _ _ _ _ Lnx
    obtain ⟨h0, -, hord⟩ := hlx rfl
    refine ⟨h0, hxlast, fun s' P' hΛ => ?_⟩
    obtain ⟨y, cy, Lny, Lpy, Lcy, hky⟩ := Hall _ _ _ hΛ
    rw [Hrepr.path] at Lpy
    rw [Hrepr.cmds] at Lcy
    obtain ⟨hyl, hyb, -, hyL, -⟩ := HI.path_ok _ _ _ _ Lpy
    obtain ⟨-, hly⟩ := Hok.1 _ _ _ _ Lny
    obtain ⟨-, -, hordy⟩ := hly rfl
    rw [hxL rfl, hyL rfl]
    refine ⟨fun hss => ?_, fun hss => ?_⟩
    · exact keyPrefix_prefix HI _ _ x y cx cy Lcx Lcy hky.symm hxl hyl hxb hyb
        ((hord y s' Lny).mpr hss)
    · exact keyPrefix_prefix HI _ _ y x cy cx Lcy Lcx hky hyl hxl hyb hxb
        ((hordy x s Lnx).mpr hss)
  imod Hclose $$ [HC HL HS HA HP HCo HRp HN HH HD Hown HQ HK HPa Hnodes HQs Hcmds Hconns HNu] with -
  · inext
    iexists S, mC, mL, mS, mA, mP, mCo, mR, mN, sh, mD, mQ, mK, mPa
    iframe
    isplitr
    · ipureintro; exact Hrepr
    isplitr
    · iexact Hproto
    isplitr
    · ipureintro; exact Hcl
    isplitr
    · ipureintro; exact Hdom
    iunfold numInv
    iexists mNu
    iframe HNu
    iexact HNo
  imodintro
  ipureintro; exact Hres

/-! ### Helpers: maps of many new persistent elements, prefixes from `locLb` -/

/-- The map with `l[i]` at key `f i` (`f` injective). -/
def idxMap {K V : Type} (f : Nat → K) (hf : Function.Injective f) (l : List V) : GMap K V :=
  ⟨fun k => by
      classical
      exact if h : ∃ i, f i = k then l[Classical.choose h]? else none,
   ⟨(List.range l.length).map f, fun k h => by
      classical
      by_cases e : ∃ i, f i = k
      · rw [dif_pos e] at h
        have hlt : Classical.choose e < l.length := by
          rcases hh : l[Classical.choose e]? with _ | v
          · rw [hh] at h; cases h
          · exact (List.getElem?_eq_some_iff.mp hh).1
        exact List.mem_map.mpr ⟨_, List.mem_range.mpr hlt, Classical.choose_spec e⟩
      · rw [dif_neg e] at h; cases h⟩⟩

omit [GoGlobalContext] G in
theorem idxMap_lookup_f {K V : Type} (f : Nat → K) (hf : Function.Injective f) (l : List V)
    (i : Nat) : (idxMap f hf l).lookup (f i) = l[i]? := by
  classical
  show (if h : ∃ j, f j = f i then l[Classical.choose h]? else none) = _
  have e : ∃ j, f j = f i := ⟨i, rfl⟩
  rw [dif_pos e, hf (Classical.choose_spec e)]

omit [GoGlobalContext] G in
theorem idxMap_lookup_none {K V : Type} (f : Nat → K) (hf : Function.Injective f) (l : List V)
    (k : K) (h : ∀ i, f i ≠ k) : (idxMap f hf l).lookup k = none := by
  classical
  show (if h : ∃ j, f j = k then l[Classical.choose h]? else none) = _
  rw [dif_neg (fun ⟨i, hi⟩ => h i hi)]

/-- The map with `()` at each key of `ks`. -/
def keyMap {K : Type} [DecidableEq K] (ks : List K) : GMap K Unit :=
  ⟨fun k => if k ∈ ks then some () else none, ⟨ks, fun k h => by
    by_cases e : k ∈ ks
    · exact e
    · simp [e] at h⟩⟩

omit [GoGlobalContext] G in
theorem keyMap_lookup {K : Type} [DecidableEq K] (ks : List K) (k : K) :
    (keyMap ks).lookup k = if k ∈ ks then some () else none := rfl

omit [GoGlobalContext] in
theorem idxMap_big {K V : Type} [DecidableEq K] [Pos.Countable K] [Pos.Countable V] (g : GName)
    (f : Nat → K) (hf : Function.Injective f) (l : List V) :
    ([∗map] k ↦ v ∈ idxMap f hf l, k ↪[g]□ v : IProp netDistGF) ⊢ [∗list] i ↦ v ∈ l, f i ↪[g]□ v := by
  iintro #H
  iapply (BigSepL.bigSepL_intro (P := iprop(□ [∗map] k ↦ v ∈ idxMap f hf l, k ↪[g]□ v))
    (fun i x hx => intuitionistically_elim.trans (BigSepM.bigSepM_lookup
      (show Iris.Std.PartialMap.get? (idxMap f hf l) (f i) = some x by
        show (idxMap f hf l).lookup (f i) = some x
        rw [idxMap_lookup_f]; exact hx))))
  iexact H

omit [GoGlobalContext] in
theorem keyMap_big {A K : Type} [DecidableEq K] [Pos.Countable K] (g : GName) (f : A → K)
    (xs : List A) :
    ([∗map] k ↦ v ∈ keyMap (xs.map f), k ↪[g]□ v : IProp netDistGF) ⊢
      [∗list] x ∈ xs, f x ↪[g]□ () := by
  iintro #H
  iapply (BigSepL.bigSepL_intro (P := iprop(□ [∗map] k ↦ v ∈ keyMap (xs.map f), k ↪[g]□ v))
    (fun i x hx => intuitionistically_elim.trans (BigSepM.bigSepM_lookup
      (show Iris.Std.PartialMap.get? (keyMap (xs.map f)) (f x) = some () by
        show (keyMap (xs.map f)).lookup (f x) = some ()
        rw [keyMap_lookup, if_pos (List.mem_map_of_mem (List.mem_of_getElem? hx))]))))
  iexact H

omit [GoGlobalContext] G in
theorem seqOf_map_fst (S : PState) (s : Seq) (h : ∀ p ∈ s, S.cmds p.1 = some p.2) :
    S.seqOf (s.map Prod.fst) = s := by
  induction s with
  | nil => rfl
  | cons p s ih =>
    have hp := h p (by simp)
    have ih' := ih (fun q hq => h q (by simp [hq]))
    simp only [PState.seqOf] at ih' ⊢
    simp [List.filterMap_cons, hp, ih']

omit [GoGlobalContext] G in
theorem prefix_of_lookups {l : List CmdId} {s : Seq}
    (h : ∀ (i : Nat) (p : CmdId × Cmd), s[i]? = some p → l[i]? = some p.1) :
    s.map Prod.fst <+: l := by
  rw [List.prefix_iff_eq_take, List.length_map]
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_take]
  by_cases hi : i < s.length
  · rw [if_pos hi, List.getElem?_map, h i (s[i]'hi) (List.getElem?_eq_getElem hi),
      List.getElem?_eq_getElem hi]
    rfl
  · rw [if_neg hi]; simp; omega

omit [GoGlobalContext] G in
/-- What a `locLb` of `L`'s sequence of `b` gives about `S`: its ids are a prefix of the
sequence, its commands a prefix of the sequence's commands. -/
theorem locLb_prefix {S : PState} {N : Nat} {fr : Bool} (HI : S.PInv N fr)
    {mC mL mS mA mP mCo mR mPa} (Hrepr : Repr S mC mL mS mA mP mCo mR mPa) {L b : Nat} {s : Seq}
    (h : ∀ i p, s[i]? = some p → mL.lookup (L, b, i) = some p.1 ∧ mC.lookup p.1 = some p.2) :
    s.map Prod.fst <+: S.loc L b ∧ s <+: S.seqOf (S.loc L b) := by
  have h1 : s.map Prod.fst <+: S.loc L b :=
    prefix_of_lookups (fun i p hp => by rw [← Hrepr.loc]; exact (h i p hp).1)
  refine ⟨h1, ?_⟩
  obtain ⟨t, ht⟩ := h1
  rw [← ht, PState.seqOf, List.filterMap_append]
  have : (s.map Prod.fst).filterMap (fun x => (S.cmds x).map (x, ·)) = s :=
    seqOf_map_fst S s (fun p hp => by
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
      rw [← Hrepr.cmds]; exact (h i _ (by simp [hi])).2)
  rw [this]; exact List.prefix_append _ _

omit [GoGlobalContext] in
/-- A `locLb`'s facts, read against the authorities. -/
theorem locLb_lookups (L b : Nat) (s : Seq) (mL : GMap (Nat × Nat × Nat) CmdId)
    (mC : GMap CmdId Cmd) :
    ghostMapAuth γ.loc 1 mL ∗ ghostMapAuth γ.cmds 1 mC ∗ locLb γ L b s ⊢
    ⌜∀ i p, s[i]? = some p → mL.lookup (L, b, i) = some p.1 ∧ mC.lookup p.1 = some p.2⌝ := by
  refine (BI.forall_intro fun i => BI.forall_intro fun p => ?_).trans
    ((BI.forall_mono fun _ => BI.pure_forall.2).trans BI.pure_forall.2)
  by_cases hs : s[i]? = some p
  · unfold locLb
    iintro ⟨HL, HC, #Hlb⟩
    ihave ⟨#Hl, #Hc⟩ := (BigSepL.bigSepL_lookup hs) $$ Hlb
    unfold locAt cmdIs
    ihave %H1 := ghost_map_lookup $$ HL Hl
    ihave %H2 := ghost_map_lookup $$ HC Hc
    ipureintro
    exact fun _ => ⟨H1, H2⟩
  · exact BI.pure_intro (fun h => absurd h hs)

/-! ### The replica's new states -/

def RState.newBal (st : RState) (b' : Nat) : RState := { st with ballot := b', normal := false }
def RState.committed (st : RState) (b : Nat) (y : CmdId) : RState :=
  { st with comR := (b, y) :: st.comR }
def RState.accepted (st : RState) (b : Nat) (y : CmdId) : RState :=
  { st with accR := (b, y) :: st.accR }
def RState.computed (st : RState) (b' : Nat) (o : List CmdId) : RState :=
  { st with locR := (b', o) :: st.locR }
def RState.tookSync (st : RState) (b' : Nat) (o : List CmdId) : RState :=
  { st with
    ballot := b'
    cballot := b'
    normal := true
    locR := (b', o) :: st.locR
    accR := o.map (fun x => (b', x)) ++ st.accR }

/-- **A new ballot** (`handleNewLeader`): the replica moves to `b' ≥` its ballot, recovering. -/
theorem upd_newBallot (E : CoPset) (hE : ↑spN ⊆ E) (N : Nat) (fr : Bool) (l : List GoString)
    (r k : Nat) (st : RState) (b' : Nat) (hr : r < N) (hk : nodeOf l r = some k)
    (hb : st.ballot ≤ b') (W' : List w64) :
    inv γ γc γm γl ∗ cfg γc γm N fr l ∗ nodeSt γ k (1 : Qp).half st ∗
      predPre γ k (some (PEv.newBallot b', W')) ⊢
    |={E}=> nodeSt γ k (1 : Qp).half (st.newBal b') ∗ predPost γ k (some (PEv.newBallot b', W')) := by
  iintro ⟨#Hinv, #Hcfg, Hst, Hpre⟩
  imod node_step E hE N fr l r k st (some (PEv.newBallot b', W')) (fun s => iprop(⌜s = st.newBal b'⌝)) hr hk $$ [Hst Hpre]
    with ⟨%st', Hst, Hpost, %Heq⟩
  · iframe Hinv Hcfg Hst Hpre
    unfold stepUpd
    iintro %S %mC %mL %mS %mA %mP %mCo %mR %mPa %HH HC HL HS HA HP HCo HRp HPa
    obtain ⟨HI, Hsr, Hrs, Hrepr⟩ := HH
    imodintro
    iexists S.newBallot r b', mL, mS, mA, mP, mCo, mR, mPa
    iframe
    ipureintro
    refine ⟨⟨PState.PInv_newBallot HI r b' (by rw [Hrs]; exact hb),
      syncRows_mono Hsr rfl (fun r' p hp => by simp only [PState.newBallot]; exact hp),
      ⟨Hrepr.cmds, Hrepr.loc, Hrepr.sync, Hrepr.acc, Hrepr.pre, Hrepr.path, Hrepr.com, Hrepr.rep⟩,
      rfl, rfl, PState.le_newBallot _ _, fun r' h => ?_, ⟨[], ⟨by dsimp only [okE]; rw [Hrs]; exact hb, trivial⟩, rfl⟩⟩, ?_⟩
    · simp [PState.newBallot, h]
    · simp [PState.newBallot, Hrs, RState.newBal]
  subst Heq
  imodintro
  iframe Hst Hpost

/-- **A commit** (`getFastAndSlowAcksHandler`, `handleSyncEntry`; the descriptor's owner):
replica `r` commits `y` of its sequence of its ballot `b`, as the leader, or having accepted it,
or as a command of `b`'s `MSync`. -/
theorem upd_commit (E : CoPset) (hE : ↑spN ⊆ E) (N : Nat) (fr : Bool) (l : List GoString)
    (r k : Nat) (st : RState) (y : CmdId) (hr : r < N) (hk : nodeOf l r = some k)
    (hloc : y ∈ st.locAt st.ballot) (hnot : (st.ballot, y) ∉ st.comR) (W' : List w64) :
    inv γ γc γm γl ∗ cfg γc γm N fr l ∗ nodeSt γ k (1 : Qp).half st ∗ predPre γ k (some (PEv.commit st.ballot y, W')) ∗
      (⌜r = leaderOf N st.ballot ∨ (st.ballot, y) ∈ st.accR⌝ ∨
        ∃ M, syncIs γ st.ballot M ∗ ⌜y ∈ syncOrder M⌝) ⊢
    |={E}=> nodeSt γ k (1 : Qp).half (st.committed st.ballot y) ∗ predPost γ k (some (PEv.commit st.ballot y, W')) ∗ committed γ r st.ballot y := by
  iintro ⟨#Hinv, #Hcfg, Hst, Hpre, #Hw⟩
  imod node_step E hE N fr l r k st (some (PEv.commit st.ballot y, W'))
    (fun s => iprop(⌜s = st.committed st.ballot y⌝ ∗ committed γ r st.ballot y)) hr hk $$ [Hst Hpre]
    with ⟨%st', Hst, Hpost, %Heq, #Hc⟩
  · iframe Hinv Hcfg Hst Hpre
    unfold stepUpd
    iintro %S %mC %mL %mS %mA %mP %mCo %mR %mPa %HH HC HL HS HA HP HCo HRp HPa
    obtain ⟨HI, Hsr, Hrs, Hrepr⟩ := HH
    have hrows := HI.rows_ok r st.ballot
    rw [Hrs] at hrows
    ihave %Hwhy : ⌜r = leaderOf N st.ballot ∨ S.acc r st.ballot y ∨ y ∈ S.base st.ballot⌝ $$ [HS]
    · icases Hw with (%H | ⟨%M, #HM, %HyM⟩)
      · ipureintro
        rcases H with H | H
        · exact Or.inl H
        · exact Or.inr (Or.inl ((hrows.2.1 y).2 H))
      · unfold syncIs
        ihave %HlkS := ghost_map_lookup $$ HS HM
        ipureintro
        rw [Hrepr.sync] at HlkS
        refine Or.inr (Or.inr ?_)
        unfold PState.base; rw [HlkS]; exact HyM
    have hfresh : mCo.lookup (r, st.ballot, y) = none := by
      rcases e : mCo.lookup (r, st.ballot, y) with _ | v
      · rfl
      · exact absurd ((hrows.2.2.2.2.1 y).1 ((Hrepr.com r _ y).1 (by simp [e]))) hnot
    imod ghost_map_insert_persist _ () hfresh $$ HCo with ⟨HCo, #Hnew⟩
    imodintro
    iexists S.commit r st.ballot y, mL, mS, mA, mP, _, mR, mPa
    iframe
    isplitr
    · ipureintro
      refine ⟨PState.PInv_commit HI r _ y hr (by rw [Hrs]) (by rw [hrows.1]; exact hloc) Hwhy,
        syncRows_mono Hsr rfl (fun r' p hp => by simp only [PState.commit]; exact hp),
        ⟨Hrepr.cmds, Hrepr.loc, Hrepr.sync, Hrepr.acc, Hrepr.pre, Hrepr.path, fun r' b' y' => ?_,
          Hrepr.rep⟩, rfl, rfl, PState.le_commit _ _ _, fun r' h => ?_, ⟨[], ⟨⟨hr, by rw [Hrs], by rw [hrows.1]; exact hloc, Hwhy⟩, trivial⟩, rfl⟩⟩
      · rw [GMap.lookup_insert_eq_iff]
        by_cases e : (r, st.ballot, y) = (r', b', y')
        · simp only [Prod.mk.injEq] at e; obtain ⟨rfl, rfl, rfl⟩ := e
          simp [PState.commit]
        · rw [if_neg e, Hrepr.com]
          simp only [PState.commit]
          constructor
          · exact Or.inl
          · rintro (h | ⟨rfl, rfl, rfl⟩)
            · exact h
            · exact absurd rfl e
      · simp [PState.commit, h]
    isplitr
    · ipureintro; simp [PState.commit, Hrs, RState.committed]
    · unfold committed; iexact Hnew
  subst Heq
  imodintro
  iframe Hst Hpost
  iexact Hc

/-- **An acceptance** (`fastAckFromLeader`, the leader's own): replica `r` accepts `y` of its
sequence of its ballot `b`, which the leader's sequence `s` (a prefix it knows) has, with every
dependency `y` has there accepted or committed by `r` first (N2). -/
theorem upd_accept (E : CoPset) (hE : ↑spN ⊆ E) (N : Nat) (fr : Bool) (l : List GoString)
    (r k : Nat) (st : RState) (y : CmdId) (s : Seq) (hr : r < N) (hk : nodeOf l r = some k)
    (hloc : y ∈ st.locAt st.ballot) (hnot : (st.ballot, y) ∉ st.accR)
    (hys : y ∈ s.map Prod.fst)
    (hN2 : ∀ d ∈ depsIn s y, (st.ballot, d) ∈ st.accR ∨ (st.ballot, d) ∈ st.comR) (W' : List w64) :
    inv γ γc γm γl ∗ cfg γc γm N fr l ∗ nodeSt γ k (1 : Qp).half st ∗ predPre γ k (some (PEv.accept st.ballot y, W')) ∗
      locLb γ (leaderOf N st.ballot) st.ballot s ⊢
    |={E}=> nodeSt γ k (1 : Qp).half (st.accepted st.ballot y) ∗ predPost γ k (some (PEv.accept st.ballot y, W')) ∗ accepted γ r st.ballot y := by
  iintro ⟨#Hinv, #Hcfg, Hst, Hpre, #Hlb⟩
  imod node_step E hE N fr l r k st (some (PEv.accept st.ballot y, W'))
    (fun s' => iprop(⌜s' = st.accepted st.ballot y⌝ ∗ accepted γ r st.ballot y)) hr hk $$ [Hst Hpre]
    with ⟨%st', Hst, Hpost, %Heq, #Hc⟩
  · iframe Hinv Hcfg Hst Hpre
    unfold stepUpd
    iintro %S %mC %mL %mS %mA %mP %mCo %mR %mPa %HH HC HL HS HA HP HCo HRp HPa
    obtain ⟨HI, Hsr, Hrs, Hrepr⟩ := HH
    have hrows := HI.rows_ok r st.ballot
    rw [Hrs] at hrows
    ihave %Hlk := locLb_lookups (γ := γ) _ _ s mL mC $$ [HL HC Hlb]
    · iframe HL HC Hlb
    obtain ⟨hpre1, hpre2⟩ := locLb_prefix HI Hrepr Hlk
    obtain ⟨u, hu⟩ := hpre2
    have hord : y ∈ S.ord N st.ballot := (List.IsPrefix.subset hpre1) hys
    have hdeps : depsIn (S.ordSeq N st.ballot) y = depsIn s y := by
      unfold PState.ordSeq PState.ord; rw [← hu, depsIn_append_of_mem s u y hys]
    have hfresh : mA.lookup (r, st.ballot, y) = none := by
      rcases e : mA.lookup (r, st.ballot, y) with _ | v
      · rfl
      · exact absurd ((hrows.2.1 y).1 ((Hrepr.acc r _ y).1 (by simp [e]))) hnot
    imod ghost_map_insert_persist _ () hfresh $$ HA with ⟨HA, #Hnew⟩
    imodintro
    iexists S.accept r st.ballot y, mL, mS, _, mP, mCo, mR, mPa
    iframe
    isplitr
    · ipureintro
      refine ⟨PState.PInv_accept HI r _ y hr (by rw [Hrs]) (by rw [hrows.1]; exact hloc) hord
          (fun _ d hd => by
            rw [hdeps] at hd
            rcases hN2 d hd with h | h
            · exact Or.inl ((hrows.2.1 d).2 h)
            · exact Or.inr ((hrows.2.2.2.2.1 d).2 h)),
        syncRows_mono Hsr rfl (fun r' p hp => by simp only [PState.accept]; exact hp),
        ⟨Hrepr.cmds, Hrepr.loc, Hrepr.sync, fun r' b' y' => ?_, Hrepr.pre, Hrepr.path, Hrepr.com,
          Hrepr.rep⟩, rfl, rfl, PState.le_accept _ _ _, fun r' h => ?_, ⟨[], ⟨⟨hr, by rw [Hrs], by rw [hrows.1]; exact hloc, hord, fun _ d hd => (hN2 d (by rw [hdeps] at hd; exact hd)).imp ((hrows.2.1 d).2) ((hrows.2.2.2.2.1 d).2)⟩, trivial⟩, rfl⟩⟩
      · rw [GMap.lookup_insert_eq_iff]
        by_cases e : (r, st.ballot, y) = (r', b', y')
        · simp only [Prod.mk.injEq] at e; obtain ⟨rfl, rfl, rfl⟩ := e
          simp [PState.accept]
        · rw [if_neg e, Hrepr.acc]
          simp only [PState.accept]
          constructor
          · exact Or.inl
          · rintro (h | ⟨rfl, rfl, rfl⟩)
            · exact h
            · exact absurd rfl e
      · simp [PState.accept, h]
    isplitr
    · ipureintro; simp [PState.accept, Hrs, RState.accepted]
    · unfold accepted; iexact Hnew
  subst Heq
  imodintro
  iframe Hst Hpost
  iexact Hc

omit [GoGlobalContext] in
/-- Reports' facts, read against the authority. -/
theorem reported_lookups (b' : Nat) (reps : List (Nat × Report)) (mR : GMap (Nat × Nat) Report) :
    ghostMapAuth γ.rep 1 mR ∗ ([∗list] p ∈ reps, reported γ p.1 b' p.2) ⊢
    ⌜∀ p ∈ reps, mR.lookup (p.1, b') = some p.2⌝ := by
  refine (BI.forall_intro fun p => ?_).trans BI.pure_forall.2
  by_cases hs : p ∈ reps
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hs
    iintro ⟨HR, #Hl⟩
    ihave #Hp := (BigSepL.bigSepL_lookup (List.getElem?_eq_getElem hi)) $$ Hl
    unfold reported
    ihave %H := ghost_map_lookup $$ HR Hp
    ipureintro
    exact fun _ => H
  · exact BI.pure_intro (fun h => absurd h hs)

omit [GoGlobalContext] G in
theorem locAt_nil_of_rows {st : RState} {b : Nat} (h : ∀ o, (b, o) ∉ st.locR) : st.locAt b = [] := by
  unfold RState.locAt
  rw [List.find?_eq_none.mpr (fun p hp => by
    intro e; apply h p.2; have := beq_iff_eq.mp e; rw [← this]; exact hp)]
  rfl

omit [GoGlobalContext] G in
theorem locFn_inj (r b : Nat) : Function.Injective (fun i : Nat => (r, b, i)) := by
  intro i j h; simp only [Prod.mk.injEq] at h; exact h.2.2

omit [GoGlobalContext] G in
theorem locFn_ne {r b r' b'' : Nat} (e : ¬ (r' = r ∧ b'' = b)) (i i' : Nat) :
    (fun i : Nat => (r, b, i)) i' ≠ (r', b'', i) := by
  intro h; simp only [Prod.mk.injEq] at h; exact e ⟨h.1.symm, h.2.1.symm⟩

/-- The reports of their reporters' ids are themselves. -/
theorem repsOf_of {S : PState} {b' : Nat} :
    ∀ {reps : List (Nat × Report)}, (∀ p ∈ reps, S.rep p.1 b' = some p.2) →
      repsOf S b' (reps.map Prod.fst) = reps
  | [], _ => rfl
  | p :: l, h => by
    have ih := repsOf_of (S := S) (b' := b') (reps := l) (fun q hq => h q (List.mem_cons_of_mem _ hq))
    unfold repsOf at ih ⊢
    simp only [List.map_cons, List.filterMap_cons, h p (List.mem_cons_self ..), Option.map_some]
    rw [ih]

/-- **The new leader computes the `MSync`** (`handleNewLeaderAckNs` → `recoveredSync`; MR1):
the leader `L` of `b'`, recovering in `b'` with nothing of `b'` in its rows yet, from the
reports of a majority, sets `b'`'s `MSync` to `recoverSync N reps` and its sequence of `b'` to
its order. -/
theorem upd_computeSync (E : CoPset) (hE : ↑spN ⊆ E) (N : Nat) (fr : Bool) (l : List GoString)
    (k : Nat) (st : RState) (b' : Nat) (reps : List (Nat × Report))
    (hr : leaderOf N b' < N) (hk : nodeOf l (leaderOf N b') = some k) (hb : 0 < b')
    (hbal : st.ballot = b') (hnorm : st.normal = false) (hrow : ∀ o, (b', o) ∉ st.locR)
    (hmaj : isMajority N (reps.map Prod.fst)) (W' : List w64) :
    inv γ γc γm γl ∗ cfg γc γm N fr l ∗ nodeSt γ k (1 : Qp).half st ∗ predPre γ k (some (PEv.computeSync b' (reps.map Prod.fst), W')) ∗
      ([∗list] p ∈ reps, reported γ p.1 b' p.2) ⊢
    |={E}=> nodeSt γ k (1 : Qp).half (st.computed b' (syncOrder (recoverSync N reps))) ∗
      predPost γ k (some (PEv.computeSync b' (reps.map Prod.fst), W')) ∗
      syncIs γ b' (recoverSync N reps) ∗
      [∗list] i ↦ x ∈ syncOrder (recoverSync N reps), locAt γ (leaderOf N b') b' i x := by
  iintro ⟨#Hinv, #Hcfg, Hst, Hpre, #Hreps⟩
  imod node_step E hE N fr l (leaderOf N b') k st (some (PEv.computeSync b' (reps.map Prod.fst), W'))
    (fun s => iprop(⌜s = st.computed b' (syncOrder (recoverSync N reps))⌝ ∗
      syncIs γ b' (recoverSync N reps) ∗
      [∗list] i ↦ x ∈ syncOrder (recoverSync N reps), locAt γ (leaderOf N b') b' i x)) hr hk $$ [Hst Hpre]
    with ⟨%st', Hst, Hpost, %Heq, #HM, #Hl⟩
  · iframe Hinv Hcfg Hst Hpre
    unfold stepUpd
    iintro %S %mC %mL %mS %mA %mP %mCo %mR %mPa %HH HC HL HS HA HP HCo HRp HPa
    obtain ⟨HI, Hsr, Hrs, Hrepr⟩ := HH
    ihave %Hlk := reported_lookups (γ := γ) b' reps mR $$ [HRp Hreps]
    · iframe HRp Hreps
    have hrep : ∀ p ∈ reps, S.rep p.1 b' = some p.2 := fun p hp => by
      rw [← Hrepr.rep]; exact Hlk p hp
    have hnone : S.sync b' = none := by
      rcases e : S.sync b' with _ | M'
      · rfl
      · obtain ⟨o, ho⟩ := Hsr b' M' e
        rw [Hrs] at ho; exact absurd ho (hrow o)
    have hloc0 : S.loc (leaderOf N b') b' = [] := by
      rw [(HI.rows_ok _ _).1, Hrs]; exact locAt_nil_of_rows hrow
    have hSnone : mS.lookup b' = none := by rw [Hrepr.sync]; exact hnone
    imod ghost_map_insert_persist _ (recoverSync N reps) hSnone $$ HS with ⟨HS, #Hnew⟩
    let f := fun i : Nat => (leaderOf N b', b', i)
    have hdisj : GMap.Disjoint (idxMap f (locFn_inj _ _) (syncOrder (recoverSync N reps))) mL := by
      intro key h1 h2
      obtain ⟨r', b'', i⟩ := key
      by_cases e : r' = leaderOf N b' ∧ b'' = b'
      · obtain ⟨rfl, rfl⟩ := e
        rw [Hrepr.loc, hloc0] at h2; simp at h2
      · rw [idxMap_lookup_none f _ _ _ (fun i' => locFn_ne e i i')] at h1
        simp at h1
    imod ghost_map_insert_persist_big _ hdisj $$ HL with ⟨HL, #Hnewl⟩
    imodintro
    iexists S.computeSync N b' (recoverSync N reps), _, _, mA, mP, mCo, mR, mPa
    iframe
    isplitr
    · ipureintro
      refine ⟨PState.PInv_computeSync HI b' _ reps hb hnone ⟨by rw [Hrs, hbal], by rw [Hrs, hnorm]; simp⟩
          hmaj hrep rfl, ?_,
        ⟨Hrepr.cmds, fun r' b'' i => ?_, fun b'' => ?_, Hrepr.acc, Hrepr.pre, Hrepr.path,
          Hrepr.com, Hrepr.rep⟩, rfl, rfl, PState.le_computeSync' HI b' _ hb hnone, fun r' h => ?_, ⟨[], ⟨⟨rfl, hb, hnone, by rw [Hrs, hbal], by rw [Hrs, hnorm]; simp, hmaj, fun p hp => by obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp; rw [hrep q hq]; simp⟩, trivial⟩, by show _ = S.computeSync N b' (recoverSync N (repsOf S b' (reps.map Prod.fst))); rw [repsOf_of hrep]⟩⟩
      · intro b'' M'' h
        by_cases e : b'' = b'
        · subst e; exact ⟨syncOrder (recoverSync N reps), by simp [PState.computeSync]⟩
        · have h' : S.sync b'' = some M'' := by
            simpa [PState.computeSync, e] using h
          obtain ⟨o, ho⟩ := Hsr b'' M'' h'
          refine ⟨o, ?_⟩
          simp only [PState.computeSync]
          split <;> simp [ho]
      · rw [GMap.lookup_union]
        by_cases e : r' = leaderOf N b' ∧ b'' = b'
        · obtain ⟨h1, h2⟩ := e
          rw [h1, h2, show ((leaderOf N b', b', i) : Nat × Nat × Nat) = f i from rfl, idxMap_lookup_f,
            Hrepr.loc, hloc0]
          simp [PState.computeSync]
        · rw [idxMap_lookup_none f _ _ _ (fun i' => locFn_ne e i i'), Hrepr.loc]
          simp [PState.computeSync, e]
      · rw [GMap.lookup_insert_eq_iff, Hrepr.sync]
        by_cases e : b' = b''
        · subst e; simp [PState.computeSync]
        · simp [PState.computeSync, e, Ne.symm e]
      · simp [PState.computeSync, h]
    isplitr
    · ipureintro; simp [PState.computeSync, Hrs, RState.computed]
    isplitl []
    · unfold syncIs; iexact Hnew
    · unfold locAt
      iapply (idxMap_big γ.loc f (locFn_inj _ _) (syncOrder (recoverSync N reps)))
      iexact Hnewl
  subst Heq
  imodintro
  iframe Hst Hpost
  isplitl []
  · iexact HM
  · iexact Hl

omit [GoGlobalContext] in
/-- `takeSync`'s update of the sequences' map: from nothing in `b'`, the order's entries are new;
as the leader, they are there already. -/
theorem takeSync_loc (r b' : Nat) (M : SyncMsg) (l0 : List CmdId)
    (loc : Nat → Nat → Nat → Option CmdId) (mL : GMap (Nat × Nat × Nat) CmdId)
    (hL : ∀ r' b i, mL.lookup (r', b, i) = loc r' b i) (hl0 : ∀ i, loc r b' i = l0[i]?) :
    ghostMapAuth γ.loc 1 mL ∗
      (⌜l0 = []⌝ ∨ (⌜l0 = syncOrder M⌝ ∗ [∗list] i ↦ x ∈ syncOrder M, locAt γ r b' i x)) ⊢
    |==> ∃ mL', ghostMapAuth γ.loc 1 mL' ∗
      ⌜∀ r' b i, mL'.lookup (r', b, i) =
        if r' = r ∧ b = b' then (syncOrder M)[i]? else loc r' b i⌝ ∗
      [∗list] i ↦ x ∈ syncOrder M, locAt γ r b' i x := by
  iintro ⟨HL, (%H | ⟨%H, #H2⟩)⟩
  · let f := fun i : Nat => (r, b', i)
    have hdisj : GMap.Disjoint (idxMap f (locFn_inj _ _) (syncOrder M)) mL := by
      intro key h1 h2
      obtain ⟨r', b'', i⟩ := key
      by_cases e : r' = r ∧ b'' = b'
      · obtain ⟨rfl, rfl⟩ := e
        rw [hL, hl0, H] at h2; simp at h2
      · rw [idxMap_lookup_none f _ _ _ (fun i' => locFn_ne e i i')] at h1
        simp at h1
    imod ghost_map_insert_persist_big _ hdisj $$ HL with ⟨HL, #Hnew⟩
    imodintro
    iexists _
    iframe HL
    isplitr
    · ipureintro
      intro r' b i
      rw [GMap.lookup_union]
      by_cases e : r' = r ∧ b = b'
      · obtain ⟨h1, h2⟩ := e
        rw [h1, h2, show ((r, b', i) : Nat × Nat × Nat) = f i from rfl, idxMap_lookup_f, hL, hl0, H]
        simp
      · rw [idxMap_lookup_none f _ _ _ (fun i' => locFn_ne e i i'), hL, if_neg e]
        simp
    · unfold locAt
      iapply (idxMap_big γ.loc f (locFn_inj _ _) (syncOrder M))
      iexact Hnew
  · imodintro
    iexists mL
    iframe HL H2
    ipureintro
    intro r' b i
    by_cases e : r' = r ∧ b = b'
    · obtain ⟨h1, h2⟩ := e
      rw [if_pos ⟨h1, h2⟩, h1, h2, hL, hl0, H]
    · rw [if_neg e, hL]

/-- **A replica takes ballot `b'`'s `MSync` `M`** (`handleSync`; MR2): its ballot and `cballot`
become `b'`, it is normal, its sequence of `b'` is `M`'s order (it had nothing in `b'`, or, as
`b'`'s leader, exactly that order) and it accepts every command of the order (it had accepted
nothing in `b'`). The commits that follow are `upd_commit`'s (`y ∈ syncOrder M`). -/
theorem upd_takeSync (E : CoPset) (hE : ↑spN ⊆ E) (N : Nat) (fr : Bool) (l : List GoString)
    (r k : Nat) (st : RState) (b' : Nat) (M : SyncMsg) (hr : r < N) (hk : nodeOf l r = some k)
    (hbal : st.ballot ≤ b') (hacc : ∀ x, (b', x) ∉ st.accR) (W' : List w64) :
    inv γ γc γm γl ∗ cfg γc γm N fr l ∗ nodeSt γ k (1 : Qp).half st ∗ predPre γ k (some (PEv.takeSync b', W')) ∗ syncIs γ b' M ∗
      (⌜st.locAt b' = []⌝ ∨
        (⌜st.locAt b' = syncOrder M⌝ ∗ [∗list] i ↦ x ∈ syncOrder M, locAt γ r b' i x)) ⊢
    |={E}=> nodeSt γ k (1 : Qp).half (st.tookSync b' (syncOrder M)) ∗ predPost γ k (some (PEv.takeSync b', W')) ∗
      ([∗list] i ↦ x ∈ syncOrder M, locAt γ r b' i x) ∗
      [∗list] x ∈ syncOrder M, accepted γ r b' x := by
  iintro ⟨#Hinv, #Hcfg, Hst, Hpre, #HM, #Hl0⟩
  imod node_step E hE N fr l r k st (some (PEv.takeSync b', W'))
    (fun s => iprop(⌜s = st.tookSync b' (syncOrder M)⌝ ∗
      ([∗list] i ↦ x ∈ syncOrder M, locAt γ r b' i x) ∗
      [∗list] x ∈ syncOrder M, accepted γ r b' x)) hr hk $$ [Hst Hpre]
    with ⟨%st', Hst, Hpost, %Heq, #Hl, #Ha⟩
  · iframe Hinv Hcfg Hst Hpre
    unfold stepUpd
    iintro %S %mC %mL %mS %mA %mP %mCo %mR %mPa %HH HC HL HS HA HP HCo HRp HPa
    obtain ⟨HI, Hsr, Hrs, Hrepr⟩ := HH
    have hrows := HI.rows_ok r b'
    rw [Hrs] at hrows
    unfold syncIs
    ihave %HlkS := ghost_map_lookup $$ HS HM
    have hM : S.sync b' = some M := by rw [← Hrepr.sync]; exact HlkS
    have hbase : S.base b' = syncOrder M := by unfold PState.base; rw [hM]; rfl
    -- the acceptances: every command of the order, none there yet
    let g := fun x : CmdId => (r, b', x)
    have hdisjA : GMap.Disjoint (keyMap ((syncOrder M).map g)) mA := by
      intro key h1 h2
      rw [keyMap_lookup] at h1
      by_cases e : key ∈ (syncOrder M).map g
      · obtain ⟨x, -, rfl⟩ := List.mem_map.mp e
        exact hacc x ((hrows.2.1 x).1 ((Hrepr.acc r b' x).1 h2))
      · simp [e] at h1
    imod ghost_map_insert_persist_big _ hdisjA $$ HA with ⟨HA, #Hnewa⟩
    have hRA : ∀ r' b x, ((keyMap ((syncOrder M).map g) ∪ mA).lookup (r', b, x)).isSome ↔
        (S.takeSync r b').acc r' b x := by
      intro r' b x
      rw [GMap.lookup_union, keyMap_lookup]
      simp only [PState.takeSync, hbase]
      by_cases e : r' = r ∧ b = b' ∧ x ∈ syncOrder M
      · obtain ⟨rfl, rfl, hx⟩ := e
        rw [if_pos (List.mem_map_of_mem hx)]; simp [hx]
      · rw [if_neg (fun h => e (by
          obtain ⟨x', hx', hh⟩ := List.mem_map.mp h
          simp only [g, Prod.mk.injEq] at hh; obtain ⟨rfl, rfl, rfl⟩ := hh; exact ⟨rfl, rfl, hx'⟩))]
        simp only [Option.none_or, Hrepr.acc]
        constructor
        · exact Or.inl
        · rintro (h | h)
          · exact h
          · exact absurd h e
    ihave %hlocc : ⌜st.locAt b' = [] ∨ st.locAt b' = syncOrder M⌝ $$ []
    · icases Hl0 with (%H | ⟨%H, -⟩)
      · ipureintro; exact Or.inl H
      · ipureintro; exact Or.inr H
    imod takeSync_loc (γ := γ) r b' M (S.loc r b') (fun r' b i => (S.loc r' b)[i]?) mL
      (fun r' b i => Hrepr.loc r' b i) (fun i => by rw [hrows.1]) $$ [HL Hl0] with ⟨%mL', HL, %HRL, #Hlocs⟩
    · iframe HL
      icases Hl0 with (%H | ⟨%H, #H2⟩)
      · ileft; ipureintro; rw [hrows.1]; exact H
      · iright; iframe H2; ipureintro; rw [hrows.1]; exact H
    imodintro
    iexists S.takeSync r b', mL', mS, _, mP, mCo, mR, mPa
    iframe
    isplitr
    · ipureintro
      refine ⟨PState.PInv_takeSync HI r b' M hr hM (by rw [Hrs]; exact hbal)
          (by rw [hrows.1, hbase]; exact hlocc),
        syncRows_mono Hsr rfl (fun r' p hp => by
          simp only [PState.takeSync]; split <;> simp [hp]),
        ⟨Hrepr.cmds, fun r' b i => ?_, Hrepr.sync, hRA, Hrepr.pre, Hrepr.path, Hrepr.com,
          Hrepr.rep⟩, rfl, rfl, PState.le_takeSync r b' (by rw [hrows.1, hbase]; exact hlocc), fun r' h => ?_, ⟨[], ⟨⟨hr, by rw [hM]; simp, by rw [Hrs]; exact hbal, by rw [hrows.1, hbase]; exact hlocc⟩, trivial⟩, rfl⟩⟩
      · rw [HRL]; simp only [PState.takeSync, hbase]
        by_cases e : r' = r ∧ b = b' <;> simp [e]
      · simp [PState.takeSync, h]
    isplitr
    · ipureintro; simp [PState.takeSync, Hrs, RState.tookSync, hbase]
    isplitl []
    · iexact Hlocs
    · unfold accepted
      iapply (keyMap_big γ.acc g (syncOrder M))
      iexact Hnewa
  subst Heq
  imodintro
  iframe Hst Hpost
  isplitl []
  · iexact Hl
  · iexact Ha

/-- The ids of `y`'s key that the sequence `s` has after its base `B` (of length `B.length`)
before `y`, then `y` (`PState.keyPrefix` read off a replica's own sequence: what its hash log
appended). -/
def kpOf (s : Seq) (B : List CmdId) (y : CmdId) : List CmdId :=
  match cmdIn s y with
  | some c => ((((s.drop B.length).takeWhile (·.1 != y)).filter (·.2.key == c.key)).map Prod.fst)
      ++ [y]
  | none => [y]

omit [GoGlobalContext] G in
theorem cmdIn_of_reg {S : PState} {s : Seq} (h : ∀ p ∈ s, S.cmds p.1 = some p.2) {y : CmdId}
    (hy : y ∈ s.map Prod.fst) : cmdIn s y = S.cmds y := by
  unfold cmdIn
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy
  rcases e : s.find? (fun q => q.1 == p.1) with _ | q
  · exact absurd e (List.find?_isSome.mpr ⟨p, hp, by simp⟩ |> Option.isSome_iff_ne_none.mp)
  · have hq := List.mem_of_find?_eq_some e
    have hq1 := List.find?_some e
    simp only [beq_iff_eq] at hq1
    rw [e, Option.map_some, ← hq1, h q hq]

omit [GoGlobalContext] G in
theorem keyPrefix_eq {S : PState} {r b : Nat} {s : Seq} (hs : S.loc r b = s.map Prod.fst)
    (hreg : ∀ p ∈ s, S.cmds p.1 = some p.2) {y : CmdId} (hy : y ∈ s.map Prod.fst) :
    S.keyPrefix r b y = kpOf s (S.base b) y := by
  unfold PState.keyPrefix kpOf
  rw [cmdIn_of_reg hreg hy, hs, ← List.map_drop,
    seqOf_map_fst S _ (fun p hp => hreg p (List.mem_of_mem_drop hp))]
  rfl

/-- The replica's state after pre-accepting `y` in `b` with `D` and path `P`. -/
def RState.preaccepted (st : RState) (b : Nat) (y : CmdId) (D P : List CmdId) : RState :=
  { st with preR := ((b, y), D) :: st.preR, pathR := ((b, y), P) :: st.pathR }

/-- **A pre-acceptance** (`handlePropose`'s `MFastAck`, the descriptor's owner): replica `r`, a
member of `AQ N b` in its ballot `b`, pre-accepts `y` of its sequence `s` (all of it: its
`locLb`), with `y`'s dependencies in `s` and the path `P` its hash log appended (`y` last; every
command of `y`'s key it handled after the base `B` before `y`, exactly those at the leader). -/
theorem upd_preaccept (E : CoPset) (hE : ↑spN ⊆ E) (N : Nat) (fr : Bool) (l : List GoString)
    (r k : Nat) (st : RState) (y : CmdId) (s : Seq) (B D P : List CmdId) (hr : r < N)
    (hk : nodeOf l r = some k) (hAQ : r ∈ AQ N st.ballot) (hs : s.map Prod.fst = st.locAt st.ballot)
    (hy : y ∈ s.map Prod.fst) (hD : D = depsIn s y) (hB : y ∉ B) (hlast : P.getLast? = some y)
    (hLP : r = leaderOf N st.ballot → P = kpOf s B y) (hP : ∀ z ∈ kpOf s B y, z ∈ P)
    (hpre : st.preAt st.ballot y = none) (hpath : st.pathAt st.ballot y = none) (W' : List w64) :
    inv γ γc γm γl ∗ cfg γc γm N fr l ∗ nodeSt γ k (1 : Qp).half st ∗ predPre γ k (some (PEv.preaccept st.ballot y D, W')) ∗
      locLb γ r st.ballot s ∗
      (⌜st.ballot = 0 ∧ B = []⌝ ∨ ∃ M, syncIs γ st.ballot M ∗ ⌜B = syncOrder M⌝) ⊢
    |={E}=> nodeSt γ k (1 : Qp).half (st.preaccepted st.ballot y D P) ∗ predPost γ k (some (PEv.preaccept st.ballot y D, W')) ∗
      preacc γ r st.ballot y D ∗ pathIs γ r st.ballot y P := by
  iintro ⟨#Hinv, #Hcfg, Hst, Hpre, #Hlb, #HB⟩
  imod node_step E hE N fr l r k st (some (PEv.preaccept st.ballot y D, W'))
    (fun s' => iprop(⌜s' = st.preaccepted st.ballot y D P⌝ ∗ preacc γ r st.ballot y D ∗
      pathIs γ r st.ballot y P)) hr hk $$ [Hst Hpre]
    with ⟨%st', Hst, Hpost, %Heq, #Hp1, #Hp2⟩
  · iframe Hinv Hcfg Hst Hpre
    unfold stepUpd
    iintro %S %mC %mL %mS %mA %mP %mCo %mR %mPa %HH HC HL HS HA HP HCo HRp HPa
    obtain ⟨HI, Hsr, Hrs, Hrepr⟩ := HH
    have hrows := HI.rows_ok r st.ballot
    rw [Hrs] at hrows
    ihave %Hlk := locLb_lookups (γ := γ) _ _ s mL mC $$ [HL HC Hlb]
    · iframe HL HC Hlb
    have hreg : ∀ p ∈ s, S.cmds p.1 = some p.2 := fun p hp => by
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
      rw [← Hrepr.cmds]; exact (Hlk i _ (by simp [hi])).2
    have hloc : S.loc r st.ballot = s.map Prod.fst := by rw [hrows.1, hs]
    have hseq : S.seqOf (S.loc r st.ballot) = s := by rw [hloc]; exact seqOf_map_fst S s hreg
    ihave %HBase : ⌜S.base st.ballot = B⌝ $$ [HS]
    · icases HB with (%H | ⟨%M, #HM, %HBM⟩)
      · ipureintro
        unfold PState.base
        rcases e : S.sync st.ballot with _ | M
        · rw [H.2]; rfl
        · have := (HI.sync_ok _ M e).1; omega
      · unfold syncIs
        ihave %HlkS := ghost_map_lookup $$ HS HM
        ipureintro
        rw [Hrepr.sync] at HlkS
        unfold PState.base; rw [HlkS, HBM]; rfl
    have hkp : S.keyPrefix r st.ballot y = kpOf s B y := by
      rw [keyPrefix_eq hloc hreg hy, HBase]
    have hfP : mP.lookup (r, st.ballot, y) = none := by rw [Hrepr.pre, hrows.2.2.1]; exact hpre
    have hfPa : mPa.lookup (r, st.ballot, y) = none := by
      rw [Hrepr.path, hrows.2.2.2.1]; exact hpath
    imod ghost_map_insert_persist _ D hfP $$ HP with ⟨HP, #Hn1⟩
    imod ghost_map_insert_persist _ P hfPa $$ HPa with ⟨HPa, #Hn2⟩
    imodintro
    iexists S.preaccept r st.ballot y D P, mL, mS, mA, _, mCo, mR, _
    iframe
    isplitr
    · ipureintro
      refine ⟨PState.PInv_preaccept HI r _ y D P hAQ (by rw [Hrs]) (by rw [hloc]; exact hy)
          (by rw [hseq]; exact hD) (by rw [HBase]; exact hB) hlast
          (fun h => by rw [hkp]; exact hLP h) (fun z hz => by rw [hkp] at hz; exact hP z hz),
        syncRows_mono Hsr rfl (fun r' p hp => by simp only [PState.preaccept]; exact hp),
        ⟨Hrepr.cmds, Hrepr.loc, Hrepr.sync, Hrepr.acc, fun r' b' y' => ?_, fun r' b' y' => ?_,
          Hrepr.com, Hrepr.rep⟩, rfl, rfl, PState.le_preaccept _ _ _ _ _ (by rw [← Hrepr.pre]; exact hfP) (by rw [← Hrepr.path]; exact hfPa), fun r' h => ?_, ⟨P, ⟨⟨hAQ, by rw [Hrs], by rw [hloc]; exact hy, by rw [hseq]; exact hD, by rw [HBase]; exact hB, by rw [← Hrepr.pre]; exact hfP, by rw [← Hrepr.path]; exact hfPa⟩, hlast, fun h => by rw [hkp]; exact hLP h, fun z hz => by rw [hkp] at hz; exact hP z hz⟩, rfl⟩⟩
      · rw [GMap.lookup_insert_eq_iff, Hrepr.pre]
        by_cases e : (r, st.ballot, y) = (r', b', y')
        · simp only [Prod.mk.injEq] at e; obtain ⟨rfl, rfl, rfl⟩ := e
          simp [PState.preaccept]
        · rw [if_neg e]
          simp only [PState.preaccept]
          rw [if_neg (by rintro ⟨rfl, rfl, rfl⟩; exact e rfl)]
      · rw [GMap.lookup_insert_eq_iff, Hrepr.path]
        by_cases e : (r, st.ballot, y) = (r', b', y')
        · simp only [Prod.mk.injEq] at e; obtain ⟨rfl, rfl, rfl⟩ := e
          simp [PState.preaccept]
        · rw [if_neg e]
          simp only [PState.preaccept]
          rw [if_neg (by rintro ⟨rfl, rfl, rfl⟩; exact e rfl)]
      · simp [PState.preaccept, h]
    isplitr
    · ipureintro; simp [PState.preaccept, Hrs, RState.preaccepted]
    isplitl []
    · unfold preacc; iexact Hn1
    · unfold pathIs; iexact Hn2
  subst Heq
  imodintro
  iframe Hst Hpost
  isplitl []
  · iexact Hp1
  · iexact Hp2

omit [GoGlobalContext] G in
/-- `takeWhile` stops in the first part when an element of it fails. -/
theorem takeWhile_append_of_neg' {α : Type} (p : α → Bool) (a u : List α) (h : ∃ z ∈ a, p z = false) :
    (a ++ u).takeWhile p = a.takeWhile p := by
  induction a with
  | nil => obtain ⟨z, hz, -⟩ := h; simp at hz
  | cons x a ih =>
    by_cases hx : p x = true
    · have h' : ∃ z ∈ a, p z = false := by
        obtain ⟨z, hz, hpz⟩ := h
        rcases List.mem_cons.mp hz with rfl | hz
        · rw [hx] at hpz; cases hpz
        · exact ⟨z, hz, hpz⟩
      simp only [List.cons_append, List.takeWhile_cons, hx, ↓reduceIte, ih h']
    · simp only [Bool.not_eq_true] at hx
      simp [List.takeWhile_cons, hx]

omit [GoGlobalContext] G in
/-- `kpOf` depends only on a prefix of the sequence that has `y` after the base. -/
theorem kpOf_append (s u : Seq) (B : List CmdId) (y : CmdId)
    (hy : y ∈ (s.drop B.length).map Prod.fst) : kpOf (s ++ u) B y = kpOf s B y := by
  have hy' : y ∈ s.map Prod.fst := by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy
    exact List.mem_map.mpr ⟨p, List.mem_of_mem_drop hp, rfl⟩
  have hlen : B.length ≤ s.length := by
    refine Nat.le_of_not_lt (fun hc => ?_)
    rw [List.drop_eq_nil_of_le (by omega)] at hy; simp at hy
  unfold kpOf
  rw [(before_append_of_mem s u y hy').2, List.drop_append_of_le_length hlen,
    takeWhile_append_of_neg' _ _ _ (by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy
      exact ⟨p, hp, by simp⟩)]

omit [GoGlobalContext] G in
/-- The registered commands of a list, as a sequence, have the list's ids. -/
theorem seqOf_fst' (S : PState) (O : List CmdId) (hreg : ∀ y ∈ O, S.cmds y ≠ none) :
    (S.seqOf O).map Prod.fst = O := by
  induction O with
  | nil => rfl
  | cons y O ih =>
    obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp (hreg y (by simp))
    rw [PState.seqOf_cons S y O c hc]; simp [ih (fun z hz => hreg z (by simp [hz]))]

omit [GoGlobalContext] G in
theorem seqOf_reg (S : PState) (O : List CmdId) : ∀ p ∈ S.seqOf O, S.cmds p.1 = some p.2 := by
  intro p hp
  unfold PState.seqOf at hp
  obtain ⟨x, -, hx⟩ := List.mem_filterMap.mp hp
  rcases e : S.cmds x with _ | c
  · rw [e] at hx; cases hx
  · rw [e] at hx; cases hx; exact e

omit [GoGlobalContext] G in
/-- A command of a prefix `s` of a sequence `L` that is not in the base `B` (a prefix of `L`)
comes after it in `s`. -/
theorem mem_drop_of_prefix {s : Seq} {B L : List CmdId} {y : CmdId} (hs : s.map Prod.fst <+: L)
    (hB : B <+: L) (hy : y ∈ s.map Prod.fst) (hyB : y ∉ B) :
    y ∈ (s.drop B.length).map Prod.fst := by
  obtain ⟨i, hi, hiy⟩ := List.getElem_of_mem hy
  have hi' : i < s.length := by simpa using hi
  obtain ⟨t, rfl⟩ := hs
  obtain ⟨t', ht'⟩ := hB
  by_cases hib : i < B.length
  · exfalso; apply hyB
    have h1 : (B ++ t')[i]? = some B[i] := by rw [List.getElem?_append_left hib, List.getElem?_eq_getElem hib]
    have h2 : (s.map Prod.fst ++ t)[i]? = some y := by
      rw [List.getElem?_append_left hi, List.getElem?_eq_getElem hi, hiy]
    rw [ht', h2] at h1
    cases h1; exact List.getElem_mem hib
  · rw [List.mem_map]
    refine ⟨s[i]'hi', ?_, ?_⟩
    · have : s[i]'hi' = (s.drop B.length)[i - B.length]'(by simp; omega) := by
        simp only [List.getElem_drop]; congr 1; omega
      rw [this]; exact List.getElem_mem _
    · rw [← hiy]; simp

/-- **A pre-acceptance over a prefix** (`handlePropose`'s `MFastAck`, a descriptor's goroutine):
as `upd_preaccept`, with `s` any prefix of replica `r`'s sequence of its ballot that has `y` (its
`locLb`: a descriptor cannot know the whole sequence, the run loop appends to it concurrently),
`D` and the path read off that prefix. -/
theorem upd_preaccept' (E : CoPset) (hE : ↑spN ⊆ E) (N : Nat) (fr : Bool) (l : List GoString)
    (r k : Nat) (st : RState) (y : CmdId) (s : Seq) (B D P : List CmdId) (hr : r < N)
    (hk : nodeOf l r = some k) (hAQ : r ∈ AQ N st.ballot)
    (hy : y ∈ s.map Prod.fst) (hD : D = depsIn s y) (hB : y ∉ B) (hlast : P.getLast? = some y)
    (hLP : r = leaderOf N st.ballot → P = kpOf s B y) (hP : ∀ z ∈ kpOf s B y, z ∈ P)
    (hpre : st.preAt st.ballot y = none) (hpath : st.pathAt st.ballot y = none) (W' : List w64) :
    inv γ γc γm γl ∗ cfg γc γm N fr l ∗ nodeSt γ k (1 : Qp).half st ∗ predPre γ k (some (PEv.preaccept st.ballot y D, W')) ∗
      locLb γ r st.ballot s ∗
      (⌜st.ballot = 0 ∧ B = []⌝ ∨ ∃ M, syncIs γ st.ballot M ∗ ⌜B = syncOrder M⌝) ⊢
    |={E}=> nodeSt γ k (1 : Qp).half (st.preaccepted st.ballot y D P) ∗ predPost γ k (some (PEv.preaccept st.ballot y D, W')) ∗
      preacc γ r st.ballot y D ∗ pathIs γ r st.ballot y P := by
  iintro ⟨#Hinv, #Hcfg, Hst, Hpre, #Hlb, #HB⟩
  imod node_step E hE N fr l r k st (some (PEv.preaccept st.ballot y D, W'))
    (fun s' => iprop(⌜s' = st.preaccepted st.ballot y D P⌝ ∗ preacc γ r st.ballot y D ∗
      pathIs γ r st.ballot y P)) hr hk $$ [Hst Hpre]
    with ⟨%st', Hst, Hpost, %Heq, #Hp1, #Hp2⟩
  · iframe Hinv Hcfg Hst Hpre
    unfold stepUpd
    iintro %S %mC %mL %mS %mA %mP %mCo %mR %mPa %HH HC HL HS HA HP HCo HRp HPa
    obtain ⟨HI, Hsr, Hrs, Hrepr⟩ := HH
    have hrows := HI.rows_ok r st.ballot
    rw [Hrs] at hrows
    ihave %Hlk := locLb_lookups (γ := γ) _ _ s mL mC $$ [HL HC Hlb]
    · iframe HL HC Hlb
    obtain ⟨hpre1, hpre2⟩ := locLb_prefix HI Hrepr Hlk
    obtain ⟨u, hu⟩ := hpre2
    have hlocok := HI.loc_ok r st.ballot
    have hfull : (S.seqOf (S.loc r st.ballot)).map Prod.fst = S.loc r st.ballot :=
      seqOf_fst' S _ hlocok.2.1
    have hreg : ∀ p ∈ S.seqOf (S.loc r st.ballot), S.cmds p.1 = some p.2 := seqOf_reg S _
    have hyL : y ∈ S.loc r st.ballot := List.IsPrefix.subset hpre1 hy
    have hyF : y ∈ (S.seqOf (S.loc r st.ballot)).map Prod.fst := by rw [hfull]; exact hyL
    ihave %HBase : ⌜S.base st.ballot = B⌝ $$ [HS]
    · icases HB with (%H | ⟨%M, #HM, %HBM⟩)
      · ipureintro
        unfold PState.base
        rcases e : S.sync st.ballot with _ | M
        · rw [H.2]; rfl
        · have := (HI.sync_ok _ M e).1; omega
      · unfold syncIs
        ihave %HlkS := ghost_map_lookup $$ HS HM
        ipureintro
        rw [Hrepr.sync] at HlkS
        unfold PState.base; rw [HlkS, HBM]; rfl
    have hBL : B <+: S.loc r st.ballot := by
      by_cases h0 : st.ballot = 0
      · have : S.base st.ballot = [] := by
          unfold PState.base
          rcases e : S.sync st.ballot with _ | M
          · rfl
          · have := (HI.sync_ok _ M e).1; omega
        rw [← HBase, this]; exact List.nil_prefix
      · rw [← HBase]
        exact ((hlocok.2.2 (List.ne_nil_of_mem hyL)).2.2 (by omega)).2
    have hyD : y ∈ (s.drop B.length).map Prod.fst := mem_drop_of_prefix hpre1 hBL hy hB
    have hkp : S.keyPrefix r st.ballot y = kpOf s B y := by
      rw [keyPrefix_eq hfull.symm hreg hyF, HBase, ← hu, kpOf_append s u B y hyD]
    have hdeps : depsIn (S.seqOf (S.loc r st.ballot)) y = depsIn s y := by
      rw [← hu, depsIn_append_of_mem s u y hy]
    have hfP : mP.lookup (r, st.ballot, y) = none := by rw [Hrepr.pre, hrows.2.2.1]; exact hpre
    have hfPa : mPa.lookup (r, st.ballot, y) = none := by
      rw [Hrepr.path, hrows.2.2.2.1]; exact hpath
    imod ghost_map_insert_persist _ D hfP $$ HP with ⟨HP, #Hn1⟩
    imod ghost_map_insert_persist _ P hfPa $$ HPa with ⟨HPa, #Hn2⟩
    imodintro
    iexists S.preaccept r st.ballot y D P, mL, mS, mA, _, mCo, mR, _
    iframe
    isplitr
    · ipureintro
      refine ⟨PState.PInv_preaccept HI r _ y D P hAQ (by rw [Hrs]) hyL
          (by rw [hdeps]; exact hD) (by rw [HBase]; exact hB) hlast
          (fun h => by rw [hkp]; exact hLP h) (fun z hz => by rw [hkp] at hz; exact hP z hz),
        syncRows_mono Hsr rfl (fun r' p hp => by simp only [PState.preaccept]; exact hp),
        ⟨Hrepr.cmds, Hrepr.loc, Hrepr.sync, Hrepr.acc, fun r' b' y' => ?_, fun r' b' y' => ?_,
          Hrepr.com, Hrepr.rep⟩, rfl, rfl, PState.le_preaccept _ _ _ _ _ (by rw [← Hrepr.pre]; exact hfP) (by rw [← Hrepr.path]; exact hfPa), fun r' h => ?_, ⟨P, ⟨⟨hAQ, by rw [Hrs], hyL, by rw [hdeps]; exact hD, by rw [HBase]; exact hB, by rw [← Hrepr.pre]; exact hfP, by rw [← Hrepr.path]; exact hfPa⟩, hlast, fun h => by rw [hkp]; exact hLP h, fun z hz => by rw [hkp] at hz; exact hP z hz⟩, rfl⟩⟩
      · rw [GMap.lookup_insert_eq_iff, Hrepr.pre]
        by_cases e : (r, st.ballot, y) = (r', b', y')
        · simp only [Prod.mk.injEq] at e; obtain ⟨rfl, rfl, rfl⟩ := e
          simp [PState.preaccept]
        · rw [if_neg e]
          simp only [PState.preaccept]
          rw [if_neg (by rintro ⟨rfl, rfl, rfl⟩; exact e rfl)]
      · rw [GMap.lookup_insert_eq_iff, Hrepr.path]
        by_cases e : (r, st.ballot, y) = (r', b', y')
        · simp only [Prod.mk.injEq] at e; obtain ⟨rfl, rfl, rfl⟩ := e
          simp [PState.preaccept]
        · rw [if_neg e]
          simp only [PState.preaccept]
          rw [if_neg (by rintro ⟨rfl, rfl, rfl⟩; exact e rfl)]
      · simp [PState.preaccept, h]
    isplitr
    · ipureintro; simp [PState.preaccept, Hrs, RState.preaccepted]
    isplitl []
    · unfold preacc; iexact Hn1
    · unfold pathIs; iexact Hn2
  subst Heq
  imodintro
  iframe Hst Hpost
  isplitl []
  · iexact Hp1
  · iexact Hp2

omit [GoGlobalContext] in
/-- Pure facts of every element of a list of persistent facts, read against `R`. -/
theorem bigSepL_gather {A : Type} (R : IProp netDistGF) (Φ : A → IProp netDistGF) (P : A → Prop)
    (xs : List A) [∀ x, Persistent (Φ x)] (h : ∀ x, x ∈ xs → (R ∗ Φ x ⊢ ⌜P x⌝)) :
    R ∗ ([∗list] x ∈ xs, Φ x) ⊢ ⌜∀ x ∈ xs, P x⌝ := by
  refine (BI.forall_intro fun x => ?_).trans BI.pure_forall.2
  by_cases hs : x ∈ xs
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hs
    refine (BI.sep_mono_right (BigSepL.bigSepL_lookup (List.getElem?_eq_getElem hi))).trans
      ((h _ hs).trans (BI.pure_mono fun p _ => p))
  · exact BI.pure_intro (fun h => absurd h hs)

omit [GoGlobalContext] in
/-- A `locLb` of replica `r`'s own sequence that has `y`: `y` is in it (read against `S`). -/
theorem locLb_mem {S : PState} {N : Nat} {fr : Bool} (HI : S.PInv N fr)
    {mC mL mS mA mP mCo mR mPa} (Hrepr : Repr S mC mL mS mA mP mCo mR mPa) (r b : Nat) (s : Seq)
    (y : CmdId) (hy : y ∈ s.map Prod.fst) :
    ghostMapAuth γ.loc 1 mL ∗ ghostMapAuth γ.cmds 1 mC ∗ locLb γ r b s ⊢ ⌜y ∈ S.loc r b⌝ := by
  iintro H
  ihave %Hlk := locLb_lookups (γ := γ) _ _ s mL mC $$ H
  ipureintro
  exact List.IsPrefix.subset (locLb_prefix HI Hrepr Hlk).1 hy

omit [GoGlobalContext] in
/-- Acceptance or commit facts of `r` in `b`, read against the authorities. -/
theorem accCom_lookups (r b : Nat) (xs : List CmdId) (mA mCo : GMap (Nat × Nat × CmdId) Unit) :
    (ghostMapAuth γ.acc 1 mA ∗ ghostMapAuth γ.com 1 mCo) ∗
      ([∗list] d ∈ xs, iprop(accepted γ r b d ∨ committed γ r b d)) ⊢
    ⌜∀ d ∈ xs, (mA.lookup (r, b, d)).isSome ∨ (mCo.lookup (r, b, d)).isSome⌝ := by
  apply bigSepL_gather
  intro d _
  iintro ⟨⟨HA, HCo⟩, Hd⟩
  icases Hd with (Hd | Hd)
  · unfold accepted
    ihave %H := ghost_map_lookup $$ HA Hd
    ipureintro; left; simp [H]
  · unfold committed
    ihave %H := ghost_map_lookup $$ HCo Hd
    ipureintro; right; simp [H]

/-- **An acceptance, from a descriptor** (`fastAckFromLeader`): as `upd_accept`, with N2 by
the persistent facts of the dependencies' acceptances or commits (`depsAccepted`: `accepted`'s
keys, or `delivered`) instead of the replica's rows. -/
theorem upd_accept' (E : CoPset) (hE : ↑spN ⊆ E) (N : Nat) (fr : Bool) (l : List GoString)
    (r k : Nat) (st : RState) (y : CmdId) (s : Seq) (hr : r < N) (hk : nodeOf l r = some k)
    (hnot : (st.ballot, y) ∉ st.accR) (hys : y ∈ s.map Prod.fst)
    (hloc : y ∈ st.locAt st.ballot) (W' : List w64) :
    inv γ γc γm γl ∗ cfg γc γm N fr l ∗ nodeSt γ k (1 : Qp).half st ∗ predPre γ k (some (PEv.accept st.ballot y, W')) ∗
      locLb γ (leaderOf N st.ballot) st.ballot s ∗
      ([∗list] d ∈ depsIn s y, iprop(accepted γ r st.ballot d ∨ committed γ r st.ballot d)) ⊢
    |={E}=> nodeSt γ k (1 : Qp).half (st.accepted st.ballot y) ∗ predPost γ k (some (PEv.accept st.ballot y, W')) ∗ accepted γ r st.ballot y := by
  iintro ⟨#Hinv, #Hcfg, Hst, Hpre, #Hlb, #Hdeps⟩
  imod node_step E hE N fr l r k st (some (PEv.accept st.ballot y, W'))
    (fun s' => iprop(⌜s' = st.accepted st.ballot y⌝ ∗ accepted γ r st.ballot y)) hr hk $$ [Hst Hpre]
    with ⟨%st', Hst, Hpost, %Heq, #Hc⟩
  · iframe Hinv Hcfg Hst Hpre
    unfold stepUpd
    iintro %S %mC %mL %mS %mA %mP %mCo %mR %mPa %HH HC HL HS HA HP HCo HRp HPa
    obtain ⟨HI, Hsr, Hrs, Hrepr⟩ := HH
    have hrows := HI.rows_ok r st.ballot
    rw [Hrs] at hrows
    ihave %Hlk := locLb_lookups (γ := γ) _ _ s mL mC $$ [HL HC Hlb]
    · iframe HL HC Hlb
    ihave %HN2 := accCom_lookups (γ := γ) r st.ballot (depsIn s y) mA mCo $$ [HA HCo Hdeps]
    · iframe HA HCo Hdeps
    obtain ⟨hpre1, hpre2⟩ := locLb_prefix HI Hrepr Hlk
    obtain ⟨u, hu⟩ := hpre2
    have hord : y ∈ S.ord N st.ballot := (List.IsPrefix.subset hpre1) hys
    have hdeps : depsIn (S.ordSeq N st.ballot) y = depsIn s y := by
      unfold PState.ordSeq PState.ord; rw [← hu, depsIn_append_of_mem s u y hys]
    have hfresh : mA.lookup (r, st.ballot, y) = none := by
      rcases e : mA.lookup (r, st.ballot, y) with _ | v
      · rfl
      · exact absurd ((hrows.2.1 y).1 ((Hrepr.acc r _ y).1 (by simp [e]))) hnot
    imod ghost_map_insert_persist _ () hfresh $$ HA with ⟨HA, #Hnew⟩
    imodintro
    iexists S.accept r st.ballot y, mL, mS, _, mP, mCo, mR, mPa
    iframe
    isplitr
    · ipureintro
      refine ⟨PState.PInv_accept HI r _ y hr (by rw [Hrs]) (by rw [hrows.1]; exact hloc) hord
          (fun _ d hd => by
            rw [hdeps] at hd
            rcases HN2 d hd with h | h
            · exact Or.inl ((Hrepr.acc r _ d).1 h)
            · exact Or.inr ((Hrepr.com r _ d).1 h)),
        syncRows_mono Hsr rfl (fun r' p hp => by simp only [PState.accept]; exact hp),
        ⟨Hrepr.cmds, Hrepr.loc, Hrepr.sync, fun r' b' y' => ?_, Hrepr.pre, Hrepr.path, Hrepr.com,
          Hrepr.rep⟩, rfl, rfl, PState.le_accept _ _ _, fun r' h => ?_, ⟨[], ⟨⟨hr, by rw [Hrs], by rw [hrows.1]; exact hloc, hord, fun _ d hd => (HN2 d (by rw [hdeps] at hd; exact hd)).imp ((Hrepr.acc r _ d).1) ((Hrepr.com r _ d).1)⟩, trivial⟩, rfl⟩⟩
      · rw [GMap.lookup_insert_eq_iff]
        by_cases e : (r, st.ballot, y) = (r', b', y')
        · simp only [Prod.mk.injEq] at e; obtain ⟨rfl, rfl, rfl⟩ := e
          simp [PState.accept]
        · rw [if_neg e, Hrepr.acc]
          simp only [PState.accept]
          constructor
          · exact Or.inl
          · rintro (h | ⟨rfl, rfl, rfl⟩)
            · exact h
            · exact absurd rfl e
      · simp [PState.accept, h]
    isplitr
    · ipureintro; simp [PState.accept, Hrs, RState.accepted]
    · unfold accepted; iexact Hnew
  subst Heq
  imodintro
  iframe Hst Hpost
  iexact Hc

/-- **A commit, from a descriptor** (`getFastAndSlowAcksHandler`, `handleSyncEntry`): as
`upd_commit`, with the acceptance case by its persistent fact (the leader's ack in the
descriptor's message set carries it). -/
theorem upd_commit' (E : CoPset) (hE : ↑spN ⊆ E) (N : Nat) (fr : Bool) (l : List GoString)
    (r k : Nat) (st : RState) (y : CmdId) (hr : r < N) (hk : nodeOf l r = some k)
    (hloc : y ∈ st.locAt st.ballot) (hnot : (st.ballot, y) ∉ st.comR) (W' : List w64) :
    inv γ γc γm γl ∗ cfg γc γm N fr l ∗ nodeSt γ k (1 : Qp).half st ∗ predPre γ k (some (PEv.commit st.ballot y, W')) ∗
      (⌜r = leaderOf N st.ballot⌝ ∨ accepted γ r st.ballot y ∨
        ∃ M, syncIs γ st.ballot M ∗ ⌜y ∈ syncOrder M⌝) ⊢
    |={E}=> nodeSt γ k (1 : Qp).half (st.committed st.ballot y) ∗ predPost γ k (some (PEv.commit st.ballot y, W')) ∗ committed γ r st.ballot y := by
  iintro ⟨#Hinv, #Hcfg, Hst, Hpre, #Hw⟩
  imod node_step E hE N fr l r k st (some (PEv.commit st.ballot y, W'))
    (fun s => iprop(⌜s = st.committed st.ballot y⌝ ∗ committed γ r st.ballot y)) hr hk $$ [Hst Hpre]
    with ⟨%st', Hst, Hpost, %Heq, #Hc⟩
  · iframe Hinv Hcfg Hst Hpre
    unfold stepUpd
    iintro %S %mC %mL %mS %mA %mP %mCo %mR %mPa %HH HC HL HS HA HP HCo HRp HPa
    obtain ⟨HI, Hsr, Hrs, Hrepr⟩ := HH
    have hrows := HI.rows_ok r st.ballot
    rw [Hrs] at hrows
    ihave %Hwhy : ⌜r = leaderOf N st.ballot ∨ S.acc r st.ballot y ∨ y ∈ S.base st.ballot⌝ $$ [HS HA]
    · icases Hw with (%H | #Ha | ⟨%M, #HM, %HyM⟩)
      · ipureintro; exact Or.inl H
      · unfold accepted
        ihave %HlkA := ghost_map_lookup $$ HA Ha
        ipureintro
        exact Or.inr (Or.inl ((Hrepr.acc r _ y).1 (by simp [HlkA])))
      · unfold syncIs
        ihave %HlkS := ghost_map_lookup $$ HS HM
        ipureintro
        rw [Hrepr.sync] at HlkS
        refine Or.inr (Or.inr ?_)
        unfold PState.base; rw [HlkS]; exact HyM
    have hfresh : mCo.lookup (r, st.ballot, y) = none := by
      rcases e : mCo.lookup (r, st.ballot, y) with _ | v
      · rfl
      · exact absurd ((hrows.2.2.2.2.1 y).1 ((Hrepr.com r _ y).1 (by simp [e]))) hnot
    imod ghost_map_insert_persist _ () hfresh $$ HCo with ⟨HCo, #Hnew⟩
    imodintro
    iexists S.commit r st.ballot y, mL, mS, mA, mP, _, mR, mPa
    iframe
    isplitr
    · ipureintro
      refine ⟨PState.PInv_commit HI r _ y hr (by rw [Hrs]) (by rw [hrows.1]; exact hloc) Hwhy,
        syncRows_mono Hsr rfl (fun r' p hp => by simp only [PState.commit]; exact hp),
        ⟨Hrepr.cmds, Hrepr.loc, Hrepr.sync, Hrepr.acc, Hrepr.pre, Hrepr.path, fun r' b' y' => ?_,
          Hrepr.rep⟩, rfl, rfl, PState.le_commit _ _ _, fun r' h => ?_, ⟨[], ⟨⟨hr, by rw [Hrs], by rw [hrows.1]; exact hloc, Hwhy⟩, trivial⟩, rfl⟩⟩
      · rw [GMap.lookup_insert_eq_iff]
        by_cases e : (r, st.ballot, y) = (r', b', y')
        · simp only [Prod.mk.injEq] at e; obtain ⟨rfl, rfl, rfl⟩ := e
          simp [PState.commit]
        · rw [if_neg e, Hrepr.com]
          simp only [PState.commit]
          constructor
          · exact Or.inl
          · rintro (h | ⟨rfl, rfl, rfl⟩)
            · exact h
            · exact absurd rfl e
      · simp [PState.commit, h]
    isplitr
    · ipureintro; simp [PState.commit, Hrs, RState.committed]
    · unfold committed; iexact Hnew
  subst Heq
  imodintro
  iframe Hst Hpost
  iexact Hc


/-- **A repeated acceptance** (D91: `fastAckFromLeader` resolves its accept event every time it
passes `desc.phase = ACCEPT`, also when the row is already accepted): the model's accept has no
freshness premise, so `(st.ballot, y)` already accepted is the event's `okR` (`acc_ok`), and the
step is `S.accept r st.ballot y` (the same rows; the replica's `accR` gets the pair again). -/
theorem upd_reaccept (E : CoPset) (hE : ↑spN ⊆ E) (N : Nat) (fr : Bool) (l : List GoString)
    (r k : Nat) (st : RState) (y : CmdId) (hr : r < N) (hk : nodeOf l r = some k)
    (hacc : (st.ballot, y) ∈ st.accR) (W' : List w64) :
    inv γ γc γm γl ∗ cfg γc γm N fr l ∗ nodeSt γ k (1 : Qp).half st ∗
      predPre γ k (some (PEv.accept st.ballot y, W')) ⊢
    |={E}=> nodeSt γ k (1 : Qp).half (st.accepted st.ballot y) ∗
      predPost γ k (some (PEv.accept st.ballot y, W')) := by
  iintro ⟨#Hinv, #Hcfg, Hst, Hpre⟩
  imod node_step E hE N fr l r k st (some (PEv.accept st.ballot y, W'))
    (fun s' => iprop(⌜s' = st.accepted st.ballot y⌝)) hr hk $$ [Hst Hpre]
    with ⟨%st', Hst, Hpost, %Heq⟩
  · iframe Hinv Hcfg Hst Hpre
    unfold stepUpd
    iintro %S %mC %mL %mS %mA %mP %mCo %mR %mPa %HH HC HL HS HA HP HCo HRp HPa
    obtain ⟨HI, Hsr, Hrs, Hrepr⟩ := HH
    have hrows := HI.rows_ok r st.ballot
    rw [Hrs] at hrows
    have hA : S.acc r st.ballot y := (hrows.2.1 y).2 hacc
    obtain ⟨-, hloc, hord, -, hN2⟩ := HI.acc_ok r st.ballot y hA
    imodintro
    iexists S.accept r st.ballot y, mL, mS, mA, mP, mCo, mR, mPa
    iframe
    isplitr
    · ipureintro
      refine ⟨PState.PInv_accept HI r _ y hr (by rw [Hrs]) hloc hord hN2,
        syncRows_mono Hsr rfl (fun r' p hp => by simp only [PState.accept]; exact hp),
          ⟨Hrepr.cmds, Hrepr.loc, Hrepr.sync, fun r' b' y' => ?_, Hrepr.pre, Hrepr.path, Hrepr.com,
          Hrepr.rep⟩, rfl, rfl, PState.le_accept _ _ _, fun r' h => ?_,
        ⟨[], ⟨⟨hr, by rw [Hrs], hloc, hord, hN2⟩, trivial⟩, rfl⟩⟩
      · rw [Hrepr.acc]
        simp only [PState.accept]
        constructor
        · exact Or.inl
        · rintro (h | ⟨rfl, rfl, rfl⟩)
          · exact h
          · exact hA
      · simp [PState.accept, h]
    · ipureintro; simp [PState.accept, Hrs, RState.accepted]
  subst Heq
  imodintro
  iframe Hst Hpost

/-- **A repeated commit** (D91: the acks handler resolves its commit event every time it runs,
also when the row is already committed): as `upd_reaccept`, by `com_ok`. -/
theorem upd_recommit (E : CoPset) (hE : ↑spN ⊆ E) (N : Nat) (fr : Bool) (l : List GoString)
    (r k : Nat) (st : RState) (y : CmdId) (hr : r < N) (hk : nodeOf l r = some k)
    (hcom : (st.ballot, y) ∈ st.comR) (W' : List w64) :
    inv γ γc γm γl ∗ cfg γc γm N fr l ∗ nodeSt γ k (1 : Qp).half st ∗
      predPre γ k (some (PEv.commit st.ballot y, W')) ⊢
    |={E}=> nodeSt γ k (1 : Qp).half (st.committed st.ballot y) ∗
      predPost γ k (some (PEv.commit st.ballot y, W')) := by
  iintro ⟨#Hinv, #Hcfg, Hst, Hpre⟩
  imod node_step E hE N fr l r k st (some (PEv.commit st.ballot y, W'))
    (fun s' => iprop(⌜s' = st.committed st.ballot y⌝)) hr hk $$ [Hst Hpre]
    with ⟨%st', Hst, Hpost, %Heq⟩
  · iframe Hinv Hcfg Hst Hpre
    unfold stepUpd
    iintro %S %mC %mL %mS %mA %mP %mCo %mR %mPa %HH HC HL HS HA HP HCo HRp HPa
    obtain ⟨HI, Hsr, Hrs, Hrepr⟩ := HH
    have hrows := HI.rows_ok r st.ballot
    rw [Hrs] at hrows
    have hC : S.com r st.ballot y := (hrows.2.2.2.2.1 y).2 hcom
    obtain ⟨-, -, hloc, hwhy⟩ := HI.com_ok r st.ballot y hC
    imodintro
    iexists S.commit r st.ballot y, mL, mS, mA, mP, mCo, mR, mPa
    iframe
    isplitr
    · ipureintro
      refine ⟨PState.PInv_commit HI r _ y hr (by rw [Hrs]) hloc hwhy,
        syncRows_mono Hsr rfl (fun r' p hp => by simp only [PState.commit]; exact hp),
        ⟨Hrepr.cmds, Hrepr.loc, Hrepr.sync, Hrepr.acc, Hrepr.pre, Hrepr.path, fun r' b' y' => ?_,
          Hrepr.rep⟩, rfl, rfl, PState.le_commit _ _ _, fun r' h => ?_,
        ⟨[], ⟨⟨hr, by rw [Hrs], hloc, hwhy⟩, trivial⟩, rfl⟩⟩
      · rw [Hrepr.com]
        simp only [PState.commit]
        constructor
        · exact Or.inl
        · rintro (h | ⟨rfl, rfl, rfl⟩)
          · exact h
          · exact hC
      · simp [PState.commit, h]
    · ipureintro; simp [PState.commit, Hrs, RState.committed]
  subst Heq
  imodintro
  iframe Hst Hpost
/-- A report entry's witness (persistent): its command, and either its phase's facts are the
replica's own (`START`, or `PRE_ACCEPT` with its own pre-acceptance), or (accepted or committed,
or as the leader) the leader's sequence of `c` has it, with its dependencies there. -/
def entryWit (γ : Names) (N r c : Nat) (st : RState) (e : RepEntry) : IProp netDistGF :=
  iprop(cmdIs γ e.id e.cmd ∗
    (⌜e.phase.toNat = 0 ∨ (e.phase.toNat = 1 ∧ st.preAt c e.id = some e.dep)⌝ ∨
      (⌜e.phase.toNat ≥ 2 ∨ r = leaderOf N c⌝ ∗ ∃ s' : Seq, locLb γ (leaderOf N c) c s' ∗
        ⌜e.id ∈ s'.map Prod.fst ∧ e.dep.Perm (depsIn s' e.id)⌝)))

instance entryWit_persistent (N r c : Nat) (st : RState) (e : RepEntry) :
    Persistent (entryWit γ N r c st e) := by
  unfold entryWit; infer_instance

omit [GoGlobalContext] G in
/-- `repOk` from the reporter's own rows and the facts its witnesses give. -/
theorem repOk_of {S : PState} {N : Nat} {fr : Bool} (HI : S.PInv N fr) {r b' : Nat} {st : RState}
    (Hrs : S.rs r = st) {R : Report} {s : Seq} {B : List CmdId}
    (hseq : S.seqOf (S.loc r R.cbal) = s) (hbase : S.base R.cbal = B)
    (hsync : 0 < R.cbal → ∃ M, S.sync R.cbal = some M ∧ ∀ p ∈ M, ∃ e ∈ R.entries, e.id = p.1 ∧
      e.phase.toNat = 3 ∧ e.dep.Perm p.2.2)
    (hent : ∀ e ∈ R.entries, S.cmds e.id = some e.cmd ∧
      ((e.phase.toNat = 0 ∨ (e.phase.toNat = 1 ∧ st.preAt R.cbal e.id = some e.dep)) ∨
       ((e.phase.toNat ≥ 2 ∨ r = leaderOf N R.cbal) ∧ e.id ∈ S.ord N R.cbal ∧
         e.dep.Perm (depsIn (S.ordSeq N R.cbal) e.id))))
    (hbal : st.ballot ≥ b') (hc : R.cbal < b')
    (h4 : ∀ c' x, R.cbal < c' → c' < b' → (c', x) ∉ st.accR ∧ st.preAt c' x = none ∧
      (c', x) ∉ st.comR ∧ st.locAt c' = [])
    (h5 : ∀ x, (R.cbal, x) ∈ st.accR ∨ (R.cbal, x) ∈ st.comR →
      ∃ e ∈ R.entries, e.id = x ∧ (e.phase.toNat ≥ 2 ∨ (r = leaderOf N R.cbal ∧ e.phase.toNat ≥ 1)))
    (h6 : ∀ x D, st.preAt R.cbal x = some D → ∃ e ∈ R.entries, e.id = x ∧
      (e.phase.toNat ≥ 2 ∨ (e.phase.toNat = 1 ∧ e.dep = D)))
    (h7 : r = leaderOf N R.cbal → ∀ x ∈ st.locAt R.cbal, ∃ e ∈ R.entries, e.id = x)
    (h8 : ∃ B', B'.Perm B ∧ R.entries.map (·.id) = B' ++ (st.locAt R.cbal).drop B.length)
    (h9 : ∀ e ∈ R.entries, e.id ∈ st.locAt R.cbal ∧ e.phase.toNat ≤ 3 ∧
      (e.phase.toNat ≥ 2 → (R.cbal, e.id) ∈ st.accR ∨ (R.cbal, e.id) ∈ st.comR) ∧
      (e.phase.toNat = 0 → ∀ d ∈ e.dep, d ∈ depsIn s e.id)) :
    S.repOk N r b' R := by
  have hrows := fun c => HI.rows_ok r c
  simp only [Hrs] at hrows
  unfold PState.repOk
  refine ⟨by rw [Hrs]; exact hbal, hc, hsync, fun c' x h1 h2 => ?_, fun x hx => ?_,
    fun x D hx => ?_, fun hL x hx => ?_, ?_, fun e he => ?_⟩
  · obtain ⟨a1, a2, a3, a4⟩ := h4 c' x h1 h2
    exact ⟨fun h => a1 (((hrows c').2.1 x).1 h), by rw [(hrows c').2.2.1]; exact a2,
      fun h => a3 (((hrows c').2.2.2.2.1 x).1 h), by rw [(hrows c').1]; exact a4⟩
  · apply h5
    rcases hx with h | h
    · exact Or.inl (((hrows _).2.1 x).1 h)
    · exact Or.inr (((hrows _).2.2.2.2.1 x).1 h)
  · apply h6; rw [← (hrows _).2.2.1]; exact hx
  · apply h7 hL; unfold PState.ord at hx; rw [← hL, (hrows _).1] at hx; exact hx
  · obtain ⟨B', hB', he⟩ := h8
    exact ⟨B', by rw [hbase]; exact hB', by rw [he, hbase, (hrows _).1]⟩
  · obtain ⟨hc1, hc2⟩ := hent e he
    obtain ⟨i1, i2, i3, i4⟩ := h9 e he
    unfold PState.entryOk
    refine ⟨hc1, by rw [(hrows _).1]; exact i1, i2, fun h2 => ?_, fun h1 => ?_, fun h0 d hd => ?_⟩
    · refine ⟨?_, ?_⟩
      · rcases i3 h2 with h | h
        · exact Or.inl (((hrows _).2.1 _).2 h)
        · exact Or.inr (((hrows _).2.2.2.2.1 _).2 h)
      · rcases hc2 with (h | ⟨h, -⟩) | ⟨-, h⟩
        · omega
        · omega
        · exact h
    · rcases hc2 with (h | ⟨-, h⟩) | ⟨h', h⟩
      · omega
      · right; rw [(hrows _).2.2.1]; exact h
      · rcases h' with h' | h'
        · omega
        · exact Or.inl ⟨h', h⟩
    · rw [hseq]; exact i4 h0 d hd

/-- The replica's state after reporting `R` for `b'`. -/
def RState.reportedAs (st : RState) (b' : Nat) (R : Report) : RState :=
  { st with repR := (b', R) :: st.repR }

/-- **A report** (`fillNewLeaderAckN`, the run loop, its descriptors stopped): replica `r`, in
ballot `b' >` its `cballot` `c = R.cbal` and not reported for `b'` yet, reports `R`: its whole
sequence `s` of `c` (its `locLb`), `c`'s base `B` (from `c`'s `MSync`, every command of which
`R` has in `COMMIT`), each entry's witness (`entryWit`), and the facts of its own rows
(`repOk_of`'s premises). It gets `reported γ r b' R`, the `MNewLeaderAckN`'s witness. -/
theorem upd_report (E : CoPset) (hE : ↑spN ⊆ E) (N : Nat) (fr : Bool) (l : List GoString)
    (r k : Nat) (st : RState) (b' : Nat) (R : Report) (s : Seq) (B : List CmdId) (hr : r < N)
    (hk : nodeOf l r = some k) (hs : s.map Prod.fst = st.locAt R.cbal)
    (hnone : st.repAt b' = none) (hbal : st.ballot ≥ b') (hc : R.cbal < b')
    (h4 : ∀ c' x, R.cbal < c' → c' < b' → (c', x) ∉ st.accR ∧ st.preAt c' x = none ∧
      (c', x) ∉ st.comR ∧ st.locAt c' = [])
    (h5 : ∀ x, (R.cbal, x) ∈ st.accR ∨ (R.cbal, x) ∈ st.comR →
      ∃ e ∈ R.entries, e.id = x ∧ (e.phase.toNat ≥ 2 ∨ (r = leaderOf N R.cbal ∧ e.phase.toNat ≥ 1)))
    (h6 : ∀ x D, st.preAt R.cbal x = some D → ∃ e ∈ R.entries, e.id = x ∧
      (e.phase.toNat ≥ 2 ∨ (e.phase.toNat = 1 ∧ e.dep = D)))
    (h7 : r = leaderOf N R.cbal → ∀ x ∈ st.locAt R.cbal, ∃ e ∈ R.entries, e.id = x)
    (h8 : ∃ B', B'.Perm B ∧ R.entries.map (·.id) = B' ++ (st.locAt R.cbal).drop B.length)
    (h9 : ∀ e ∈ R.entries, e.id ∈ st.locAt R.cbal ∧ e.phase.toNat ≤ 3 ∧
      (e.phase.toNat ≥ 2 → (R.cbal, e.id) ∈ st.accR ∨ (R.cbal, e.id) ∈ st.comR) ∧
      (e.phase.toNat = 0 → ∀ d ∈ e.dep, d ∈ depsIn s e.id)) (W' : List w64) :
    inv γ γc γm γl ∗ cfg γc γm N fr l ∗ nodeSt γ k (1 : Qp).half st ∗ predPre γ k (some (PEv.report b' R, W')) ∗
      locLb γ r R.cbal s ∗
      (⌜R.cbal = 0 ∧ B = []⌝ ∨ ∃ M, syncIs γ R.cbal M ∗ ⌜B = syncOrder M ∧
        ∀ p ∈ M, ∃ e ∈ R.entries, e.id = p.1 ∧ e.phase.toNat = 3 ∧ e.dep.Perm p.2.2⌝) ∗
      ([∗list] e ∈ R.entries, entryWit γ N r R.cbal st e) ⊢
    |={E}=> nodeSt γ k (1 : Qp).half (st.reportedAs b' R) ∗ predPost γ k (some (PEv.report b' R, W')) ∗ reported γ r b' R := by
  iintro ⟨#Hinv, #Hcfg, Hst, Hpre, #Hlb, #HB, #Hents⟩
  imod node_step E hE N fr l r k st (some (PEv.report b' R, W'))
    (fun s' => iprop(⌜s' = st.reportedAs b' R⌝ ∗ reported γ r b' R)) hr hk $$ [Hst Hpre]
    with ⟨%st', Hst, Hpost, %Heq, #Hrp⟩
  · iframe Hinv Hcfg Hst Hpre
    unfold stepUpd
    iintro %S %mC %mL %mS %mA %mP %mCo %mR %mPa %HH HC HL HS HA HP HCo HRp HPa
    obtain ⟨HI, Hsr, Hrs, Hrepr⟩ := HH
    have hrows := fun c => HI.rows_ok r c
    simp only [Hrs] at hrows
    ihave %Hlk := locLb_lookups (γ := γ) _ _ s mL mC $$ [HL HC Hlb]
    · iframe HL HC Hlb
    have hreg : ∀ p ∈ s, S.cmds p.1 = some p.2 := fun p hp => by
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
      rw [← Hrepr.cmds]; exact (Hlk i _ (by simp [hi])).2
    have hseq : S.seqOf (S.loc r R.cbal) = s := by
      rw [(hrows _).1, ← hs]; exact seqOf_map_fst S s hreg
    ihave %HBase : ⌜S.base R.cbal = B ∧ (0 < R.cbal → ∃ M, S.sync R.cbal = some M ∧
        ∀ p ∈ M, ∃ e ∈ R.entries, e.id = p.1 ∧ e.phase.toNat = 3 ∧ e.dep.Perm p.2.2)⌝ $$ [HS]
    · icases HB with (%H | ⟨%M, #HM, %HBM⟩)
      · ipureintro
        refine ⟨?_, fun h => by omega⟩
        unfold PState.base
        rcases e : S.sync R.cbal with _ | M
        · rw [H.2]; rfl
        · have := (HI.sync_ok _ M e).1; omega
      · unfold syncIs
        ihave %HlkS := ghost_map_lookup $$ HS HM
        ipureintro
        rw [Hrepr.sync] at HlkS
        refine ⟨by unfold PState.base; rw [HlkS, HBM.1]; rfl, fun _ => ⟨M, HlkS, HBM.2⟩⟩
    ihave %Hent := bigSepL_gather (iprop(ghostMapAuth γ.loc 1 mL ∗ ghostMapAuth γ.cmds 1 mC))
      (entryWit γ N r R.cbal st)
      (fun e => S.cmds e.id = some e.cmd ∧
        ((e.phase.toNat = 0 ∨ (e.phase.toNat = 1 ∧ st.preAt R.cbal e.id = some e.dep)) ∨
         ((e.phase.toNat ≥ 2 ∨ r = leaderOf N R.cbal) ∧ e.id ∈ S.ord N R.cbal ∧
           e.dep.Perm (depsIn (S.ordSeq N R.cbal) e.id)))) R.entries (fun e _ => by
        unfold entryWit cmdIs
        iintro ⟨⟨HL, HC⟩, #Hc, #Hw⟩
        ihave %Hlc := ghost_map_lookup $$ HC Hc
        rw [Hrepr.cmds] at Hlc
        icases Hw with (%H | ⟨%H, %s', #Hlb', %H'⟩)
        · ipureintro; exact ⟨Hlc, Or.inl H⟩
        · ihave %Hlk' := locLb_lookups (γ := γ) _ _ s' mL mC $$ [HL HC Hlb']
          · iframe HL HC Hlb'
          obtain ⟨hp1, ⟨u, hu⟩⟩ := locLb_prefix HI Hrepr Hlk'
          ipureintro
          refine ⟨Hlc, Or.inr ⟨H, (List.IsPrefix.subset hp1) H'.1, ?_⟩⟩
          unfold PState.ordSeq PState.ord
          rw [← hu, depsIn_append_of_mem s' u _ H'.1]; exact H'.2) $$ [HL HC Hents]
    · iframe HL HC Hents
    have hok : S.repOk N r b' R :=
      repOk_of HI Hrs hseq HBase.1 HBase.2 Hent hbal hc h4 h5 h6 h7 h8 h9
    have hfR : mR.lookup (r, b') = none := by rw [Hrepr.rep, (hrows b').2.2.2.2.2]; exact hnone
    imod ghost_map_insert_persist _ R hfR $$ HRp with ⟨HRp, #Hn⟩
    imodintro
    iexists S.report r b' R, mL, mS, mA, mP, mCo, _, mPa
    iframe
    isplitr
    · ipureintro
      refine ⟨PState.PInv_report HI r b' R (by rw [(hrows b').2.2.2.2.2]; exact hnone) hok,
        syncRows_mono Hsr rfl (fun r' p hp => by simp only [PState.report]; exact hp),
        ⟨Hrepr.cmds, Hrepr.loc, Hrepr.sync, Hrepr.acc, Hrepr.pre, Hrepr.path, Hrepr.com,
          fun r' b'' => ?_⟩, rfl, rfl, PState.le_report _ _ _ (by rw [← Hrepr.rep]; exact hfR), fun r' h => ?_, ⟨[], ⟨⟨by rw [(hrows b').2.2.2.2.2]; exact hnone, hok⟩, trivial⟩, rfl⟩⟩
      · rw [GMap.lookup_insert_eq_iff, Hrepr.rep]
        by_cases e : (r, b') = (r', b'')
        · simp only [Prod.mk.injEq] at e; obtain ⟨rfl, rfl⟩ := e
          simp [PState.report]
        · rw [if_neg e]
          simp only [PState.report]
          rw [if_neg (by rintro ⟨rfl, rfl⟩; exact e rfl)]
      · simp [PState.report, h]
    isplitr
    · ipureintro; simp [PState.report, Hrs, RState.reportedAs]
    · unfold reported; iexact Hn
  subst Heq
  imodintro
  iframe Hst Hpost
  iexact Hrp

end ghost

end sp

end Perennial.github_com.imdea_software.swiftpaxos
