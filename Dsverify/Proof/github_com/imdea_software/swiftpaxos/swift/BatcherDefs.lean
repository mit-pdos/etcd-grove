/-
The definitions, specs and lemmas of `Batcher.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.ReplyChanDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Perennial.Golang.Theory.IfJoin

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions]

/-- `releaseFastAck(f)` (defs.go): gives `f` to the fast-ack pool when pooling is on
(`useFastAckPool`, read-only once `New` wrote it; the pool's predicate is an owned `MFastAck`,
Proof/swift/PoolFns.lean). -/
abbrev swift.releaseFastAck.specR : Prop :=
  ∀ (l : Loc) (v : Bool),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      globalAddr swift.useFastAckPool ↦□ v ∗ ∃ fa : swift.MFastAck, l ↦ fa }}
    (App (Val (@! swift.releaseFastAck)) (Val #l))
  {{ RET #(); True }}

/-- `(*MOptAcks).Marshal` (hypothesis). -/
def swift.MOptAcks.marshalH : Prop :=
  ∀ (l : Loc) (r b : w32) (asl : GoSlice) (ps : List (swift.Ack × sp.Ack)),
    sp.Msg.wf (.optAcks r b (ps.map Prod.snd)) →
    ⊢ sp.marshalOk (interface.mkOk (go.GoType.PointerType swift.MOptAcks.ty) #l)
        (.optAcks r b (ps.map Prod.snd))
        iprop(l ↦ swift.MOptAcks.mk r b asl ∗ asl ↦* ps.map Prod.fst ∗
          [∗list] p ∈ ps, swift.ackRepr p.1 p.2)

/-- `(*MAcks).Marshal` (hypothesis). -/
def swift.MAcks.marshalH : Prop :=
  ∀ (l : Loc) (fsl ssl : GoSlice) (fps : List (swift.MFastAck × sp.FastAck))
    (sps : List (swift.MLightSlowAck × sp.SlowAck)),
    sp.Msg.wf (.acks (fps.map Prod.snd) (sps.map Prod.snd)) →
    (∀ p ∈ sps, swift.slowAckRepr p.1 p.2) →
    ⊢ sp.marshalOk (interface.mkOk (go.GoType.PointerType swift.MAcks.ty) #l)
        (.acks (fps.map Prod.snd) (sps.map Prod.snd))
        iprop(typedPointsto l (swift.MAcks.mk fsl ssl) DFrac.discard ∗ fsl ↦* fps.map Prod.fst ∗
          ssl ↦* sps.map Prod.fst ∗
          [∗list] p ∈ fps, swift.fastAckRepr p.1 p.2)

/-- `(*MFastAckClient).Marshal` (hypothesis). -/
def swift.MFastAckClient.marshalH : Prop :=
  ∀ (l : Loc) (r b : w32) (x : swift.CommandId) (csl : GoSlice) (cs : List sp.Hash),
    sp.Msg.wf (.fastAckClient r b (swift.toCmdId x) cs) →
    ⊢ sp.marshalOk (interface.mkOk (go.GoType.PointerType swift.MFastAckClient.ty) #l)
        (.fastAckClient r b (swift.toCmdId x) cs)
        iprop(l ↦ swift.MFastAckClient.mk r b x csl ∗ csl ↦* cs.map swift.handler.shashOf)

/-- `(*MLightSlowAck).Marshal` (hypothesis). -/
def swift.MLightSlowAck.marshalH : Prop :=
  ∀ (l : Loc) (sa : swift.MLightSlowAck) (s : sp.SlowAck),
    swift.slowAckRepr sa s →
    ⊢ sp.marshalOk (interface.mkOk (go.GoType.PointerType swift.MLightSlowAck.ty) #l)
        (.lightSlowAck s) iprop(l ↦ sa)

end specs

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions]

set_option goose.wp.extras true

omit [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps] [swift.Assumptions] [replica.Assumptions] in
theorem swift.map_to_of (l : List sp.CmdId) : (l.map swift.ofCmdId).map swift.toCmdId = l := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, ih]; rfl

omit [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps] [swift.Assumptions] [replica.Assumptions] in
/-- The client's copy of a fast ack carries its witness. -/
theorem swift.facOk_of (γ : sp.Names) (γc γm : GName) (f : sp.FastAck) (d : sp.Hash) :
    sp.fastAckOk γ f ∗ swift.facClientOk γ γc γm f ∗ sp.depHash f.dep d ⊢
      sp.msgOk γ γc γm (.fastAckClient f.rep f.bal f.id (f.cs ++ [d])) := by
  iintro ⟨#Hok, #Hc, #Hd⟩
  iunfold sp.fastAckOk at Hok
  icases Hok with ⟨%Hw, #Hpre, %P, #Hpath, #Hph, -⟩
  iunfold swift.facClientOk at Hc
  icases Hc with ⟨%c, %N, %fr, %l, #Hcmd, #Hcfg, %Hld⟩
  simp only [sp.msgOk]
  iexists f.dep, P, c
  isplitr
  · ipureintro; exact Hw
  iframe Hpre Hpath Hcmd
  isplitr
  · unfold sp.checksum
    iexists f.cs, d
    isplitr
    · ipureintro; rfl
    iframe Hph Hd
  iexists N, fr, l
  iframe Hcfg
  ipureintro; exact Hld

/-- An entry of `fastAckClientMsgs`: its checksum slice (owned) and witness. -/
def swift.facEntry (γ : sp.Names) (γc γm : GName) (c : swift.MFastAckClient) : IProp netDistGF :=
  iprop(∃ cs : List sp.Hash, c.Checksum' ↦* cs.map swift.handler.shashOf ∗
    sp.msgOk γ γc γm (.fastAckClient c.Replica' c.Ballot' (swift.toCmdId c.CmdId') cs) ∗
    ⌜sp.hashesWf cs⌝)

/-- An entry of `slowAckClientMsgs`: its witness. -/
def swift.slowEntry (γ : sp.Names) (γc γm : GName) (sa : swift.MLightSlowAck) : IProp netDistGF :=
  iprop(∃ s : sp.SlowAck, ⌜swift.slowAckRepr sa s⌝ ∗ sp.msgOk γ γc γm (.lightSlowAck s))

instance swift.slowEntry_persistent (γ : sp.Names) (γc γm : GName) (sa : swift.MLightSlowAck) :
    Persistent (swift.slowEntry γ γc γm sa) := by
  unfold swift.slowEntry; infer_instance

omit [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps] [swift.Assumptions] [replica.Assumptions] in
/-- Inserting (or overwriting) an entry with its resource. -/
theorem swift.bigSepM_overwrite {V : Type} (M : GMap swift.CommandId V)
    (E : V → IProp netDistGF) (k : swift.CommandId) (v : V) :
    ([∗map] _k ↦ v ∈ M, E v) ∗ E v ⊢ [∗map] _k ↦ v ∈ (<[k := v]> M), E v := by
  iintro ⟨HM, Hv⟩
  cases h : Iris.Std.PartialMap.get? M k with
  | none =>
    iapply (BigSepM.bigSepM_insert (Φ := fun _ v => E v) h).2
    iframe
  | some y =>
    icases (BigSepM.bigSepM_delete (Φ := fun _ v => E v) h).1 $$ HM with ⟨-, HM⟩
    iapply (BigSepM.bigSepM_insert_delete (Φ := fun _ v => E v)).2
    iframe

omit [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps] [swift.Assumptions] [replica.Assumptions] in
theorem swift.slots_set {A : Type} (l : List A) (m : Nat) (z v : A) (hm : 0 < m) :
    (l ++ List.replicate m z).set l.length v = (l ++ [v]) ++ List.replicate (m - 1) z := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  simp [List.set_append_right, List.replicate_succ]

/-- The `MAcks.FastAcks` slots filled so far (`fps`, of `n`). -/
def swift.fastSlots (γ : sp.Names) (fsl : GoSlice) (n : Nat)
    (fps : List (swift.MFastAck × sp.FastAck)) : IProp netDistGF :=
  iprop(fsl ↦* (fps.map Prod.fst ++ List.replicate (n - fps.length) (zero_val swift.MFastAck)) ∗
    ([∗list] p ∈ fps, swift.fastAckRepr p.1 p.2 ∗ sp.fastAckOk γ p.2) ∗
    ⌜∀ p ∈ fps, p.2.wf⌝)

/-- The `MAcks.LightSlowAcks` slots filled so far (`sps`, of `n`). -/
def swift.slowSlots (γ : sp.Names) (γc γm : GName) (ssl : GoSlice) (n : Nat)
    (sps : List (swift.MLightSlowAck × sp.SlowAck)) : IProp netDistGF :=
  iprop(ssl ↦* (sps.map Prod.fst ++
      List.replicate (n - sps.length) (zero_val swift.MLightSlowAck)) ∗
    ([∗list] p ∈ sps, ⌜sp.wireOk p.2.rep p.2.bal⌝ ∗ sp.accepted γ (sp.rid p.2.rep) (sp.bal p.2.bal) p.2.id ∗
      ∃ N fr l, sp.cfg γc γm N fr l ∗ ⌜sp.rid p.2.rep ≠ sp.leaderOf N (sp.bal p.2.bal)⌝) ∗
    ⌜∀ p ∈ sps, swift.slowAckRepr p.1 p.2⌝)

/-- C16: the `MOptAcks` entries are all fast-shaped (`Dep ≠ [id]`), or `me` is not the ballot's
leader (an entry from a slow ack). -/
def swift.optNL (γc γm : GName) (me b0 : w32) (aps : List (swift.Ack × sp.Ack)) :
    IProp netDistGF :=
  iprop(⌜∀ p ∈ aps, p.2.dep ≠ [p.2.id]⌝ ∨
    ∃ N fr l, sp.cfg γc γm N fr l ∗ ⌜sp.rid me ≠ sp.leaderOf N (sp.bal b0)⌝)

instance swift.optNL_persistent (γc γm : GName) (me b0 : w32) (aps : List (swift.Ack × sp.Ack)) :
    Persistent (swift.optNL γc γm me b0 aps) := by
  unfold swift.optNL; infer_instance

omit [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps] [swift.Assumptions] [replica.Assumptions] in
theorem swift.optNL_nil (γc γm : GName) (me b0 : w32) : ⊢ swift.optNL γc γm me b0 [] := by
  iunfold swift.optNL; ileft; ipureintro; intro p hp; simp at hp

omit [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps] [swift.Assumptions] [replica.Assumptions] in
/-- Appending a fast-shaped entry. -/
theorem swift.optNL_snoc (γc γm : GName) (me b0 : w32) (aps : List (swift.Ack × sp.Ack))
    (q : swift.Ack × sp.Ack) (h : q.2.dep ≠ [q.2.id]) :
    swift.optNL γc γm me b0 aps ⊢ swift.optNL γc γm me b0 (aps ++ [q]) := by
  iunfold swift.optNL
  iintro (%H | H)
  · ileft; ipureintro; intro p hp; simp at hp; rcases hp with hp | hp
    · exact H p hp
    · subst hp; exact h
  · iright; iexact H

omit [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps] [swift.Assumptions] [replica.Assumptions] in
/-- Any entries, `me` not the leader (a slow ack's entry). -/
theorem swift.optNL_slow (γc γm : GName) (me b0 : w32) (aps : List (swift.Ack × sp.Ack))
    (N : Nat) (fr : Bool) (l : List GoString) :
    sp.cfg γc γm N fr l ∗ ⌜sp.rid me ≠ sp.leaderOf N (sp.bal b0)⌝ ⊢
      swift.optNL γc γm me b0 aps := by
  iintro ⟨#Hc, %Hne⟩
  iunfold swift.optNL
  iright; iexists N, fr, l; iframe Hc; ipureintro; exact Hne

omit [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps] [swift.Assumptions] [replica.Assumptions] in
/-- Any entries, from a slow ack of `me` in `b0` (its C16 witness). -/
theorem swift.optNL_of_slow (γc γm : GName) (me b0 : w32) (aps : List (swift.Ack × sp.Ack))
    (s : sp.SlowAck) (hr : s.rep = me) (hb : sp.bal s.bal = sp.bal b0) :
    (∃ N fr l, sp.cfg γc γm N fr l ∗ ⌜sp.rid s.rep ≠ sp.leaderOf N (sp.bal s.bal)⌝) ⊢
      swift.optNL γc γm me b0 aps := by
  iintro ⟨%N, %fr, %l, #Hc, %Hne⟩
  iapply swift.optNL_slow γc γm me b0 aps N fr l
  iframe Hc; ipureintro; rw [← hr, ← hb]; exact Hne

omit [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps] [swift.Assumptions] [replica.Assumptions] in
/-- The message's disjunct (`sp.msgOk (.optAcks ..)`). -/
theorem swift.optNL_msg (γc γm : GName) (me b0 : w32) (aps : List (swift.Ack × sp.Ack)) :
    swift.optNL γc γm me b0 aps ⊢
      (⌜∀ a ∈ aps.map Prod.snd, a.dep ≠ [a.id]⌝ ∨
        ∃ N fr l, sp.cfg γc γm N fr l ∗ ⌜sp.rid me ≠ sp.leaderOf N (sp.bal b0)⌝) := by
  iunfold swift.optNL
  iintro (%H | H)
  · ileft; ipureintro; intro a ha; simp at ha; obtain ⟨x, hx⟩ := ha; exact H _ hx
  · iright; iexact H

/-- The `MOptAcks` being built (replica `me`, ballot `b0`) and the index map `is`. -/
def swift.optSt (γ : sp.Names) (γc γm : GName) (me b0 : w32) (o : Loc) (ism : Loc) (n : Nat) : IProp netDistGF :=
  iprop(∃ (asl : GoSlice) (aps : List (swift.Ack × sp.Ack)) (IM : GMap swift.CommandId w64),
    o ↦ swift.MOptAcks.mk me b0 asl ∗ asl ↦* aps.map Prod.fst ∗
    ownSliceCap swift.Ack asl (DFrac.own 1) ∗
    ([∗list] p ∈ aps, swift.ackRepr p.1 p.2 ∗ sp.ackOk γ (sp.rid me) (sp.bal b0) p.2) ∗
    ism ↦$ IM ∗
    ⌜(∀ p ∈ aps, p.2.wf) ∧ aps.length ≤ n ∧
      ∀ k j, IM !! k = some j → 0 ≤ sint.Z j ∧ ∃ p, aps[sint.nat j]? = some p ∧ p.1.CmdId' = k⌝ ∗
    swift.optNL γc γm me b0 aps)

omit [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps] [swift.Assumptions] [replica.Assumptions] in
theorem swift.optSt_mono (γ : sp.Names) (γc γm : GName) (me b0 : w32) (o ism : Loc) (n m : Nat)
    (h : n ≤ m) :
    swift.optSt γ γc γm me b0 o ism n ⊢ swift.optSt γ γc γm me b0 o ism m := by
  iintro H
  iunfold swift.optSt at H
  iunfold swift.optSt
  icases H with ⟨%asl, %aps, %IM, Ho, Ha, Hc, Hr, Hm, %Hp, #Hnl⟩
  iexists asl, aps, IM
  iframe
  isplitr
  · ipureintro
    exact ⟨Hp.1, by omega, Hp.2.2⟩
  iexact Hnl

/-- A client-copy map with its entries' resources. -/
def swift.facMap (γ : sp.Names) (γc γm : GName) (fcm : Loc) : IProp netDistGF :=
  iprop(∃ FM : GMap swift.CommandId swift.MFastAckClient, fcm ↦$ FM ∗
    [∗map] _k ↦ c ∈ FM, swift.facEntry γ γc γm c)

def swift.slowMap (γ : sp.Names) (γc γm : GName) (scm : Loc) : IProp netDistGF :=
  iprop(∃ SM : GMap swift.CommandId swift.MLightSlowAck, scm ↦$ SM ∗
    [∗map] _k ↦ c ∈ SM, swift.slowEntry γ γc γm c)

/-- A fast ack's `MOptAcks` entry. -/
def swift.ackOfFast (f : sp.FastAck) : sp.Ack := ⟨f.id, f.dep, f.cs, f.seqnum⟩

omit [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps] [swift.Assumptions] [replica.Assumptions] in
theorem swift.ackOk_of_fast (γ : sp.Names) (f : sp.FastAck) (h : f.dep ≠ [f.id]) :
    sp.fastAckOk γ f ⊢ sp.ackOk γ (sp.rid f.rep) (sp.bal f.bal) (swift.ackOfFast f) := by
  iintro #Hok
  iunfold sp.fastAckOk at Hok
  icases Hok with ⟨-, #Hpre, %P, #Hpath, #Hph⟩
  unfold sp.ackOk swift.ackOfFast
  simp only [h, ↓reduceIte]
  iframe Hpre
  iexists P
  iframe Hpath Hph

omit [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps] [replica.Assumptions] in
theorem swift.ackRepr_of_fast (fa : swift.MFastAck) (f : sp.FastAck) :
    swift.fastAckRepr fa f ⊢
      swift.ackRepr (swift.Ack.mk fa.CmdId' fa.Dep' fa.Checksum' fa.Seqnum') (swift.ackOfFast f) := by
  iintro #H
  iunfold swift.fastAckRepr at H
  icases H with ⟨%Hr, #Hd, #Hc⟩
  unfold swift.ackRepr swift.ackOfFast
  iframe Hd Hc
  ipureintro; exact ⟨Hr.2.2.1, Hr.2.2.2⟩

omit [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps] [swift.Assumptions] [replica.Assumptions] in
/-- A map's entries' resources, the keys visited so far (`keys.take i`) taken out. -/
theorem swift.mapIter_start {V : Type} (M : GMap swift.CommandId V) (E : V → IProp netDistGF)
    (keys : List swift.CommandId) :
    ([∗map] _k ↦ v ∈ M, E v) ⊢ [∗map] k ↦ v ∈ M, iprop(⌜k ∉ keys.take 0⌝ -∗ E v) := by
  apply BigSepM.bigSepM_mono_of_forall
  iintro %k %v H -
  iexact H

omit [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps] [swift.Assumptions] [replica.Assumptions] in
theorem swift.mapIter_step {V : Type} (M : GMap swift.CommandId V) (E : V → IProp netDistGF)
    (keys : List swift.CommandId) (i : Nat) (k : swift.CommandId) (v : V)
    (hk : keys[i]? = some k) (hM : M !! k = some v) (hnd : keys.Nodup) :
    ([∗map] k' ↦ v' ∈ M, iprop(⌜k' ∉ keys.take i⌝ -∗ E v')) ⊢
      E v ∗ [∗map] k' ↦ v' ∈ M, iprop(⌜k' ∉ keys.take (i + 1)⌝ -∗ E v') := by
  iintro HM
  have hlt : i < keys.length := (List.getElem?_eq_some_iff.mp hk).1
  have hnot : k ∉ keys.take i := by
    intro hm
    obtain ⟨j, hj, hjk⟩ := List.getElem_of_mem hm
    simp only [List.length_take] at hj
    rw [List.getElem_take] at hjk
    have hki : keys[i] = k := (List.getElem?_eq_some_iff.mp hk).2
    have := hnd.eq_of_getElem_eq _ _ (hjk.trans hki.symm)
    omega
  have hin : k ∈ keys.take (i + 1) := by
    rw [List.take_add_one, hk]; simp
  icases (BigSepM.bigSepM_delete (Φ := fun k' v' => iprop(⌜k' ∉ keys.take i⌝ -∗ E v')) hM).1 $$ HM
    with ⟨Hv, HM⟩
  ihave Hv := Hv $$ %hnot
  iframe Hv
  iapply (BigSepM.bigSepM_delete (Φ := fun k' v' => iprop(⌜k' ∉ keys.take (i + 1)⌝ -∗ E v')) hM).2
  isplitr
  · iintro %h; exact absurd hin h
  iapply BigSepM.bigSepM_mono_of_forall $$ HM
  iintro %k' %v' H %h
  iapply H
  ipureintro
  intro h'; apply h; exact List.take_subset_take_left _ (by omega) h'

/-- The sending context at the goroutine's own `Replica` pointer. -/
def swift.sendCtxAt (γ : sp.Names) (γc γm : GName) (rp rr : Loc) (N : Nat) (me : w32) :
    IProp netDistGF :=
  iprop(∃ (s : Loc) (γw : GName) (γs : ChanNames) (csv : swift.CommunicationSupply),
    replica.fld rr go!"Id" ↦□ me ∗ replica.fld rr go!"N" ↦□ (W64 N) ∗
    replica.isReplica rr γ γc γm γw N me ∗
    swift.fld rp go!"sender" ↦□ s ∗ isChanBag γs s (replica.sendArgP rr γ γc γm N) ∗
    swift.fld rp go!"cs" ↦□ csv ∗ ⌜swift.csCodes csv ∧ 0 ≤ me.toInt ∧ me.toInt < N ∧ N ≤ 7⌝)

instance swift.sendCtxAt_persistent (γ : sp.Names) (γc γm : GName) (rp rr : Loc) (N : Nat)
    (me : w32) : Persistent (swift.sendCtxAt γ γc γm rp rr N me) := by
  unfold swift.sendCtxAt; infer_instance

omit [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps] [replica.Assumptions] in
theorem swift.sendCtxN_at (γ : sp.Names) (γc γm : GName) (rp rr : Loc) (N : Nat) (me : w32) :
    swift.fld rp go!"Replica" ↦□ rr ∗ swift.sendCtxN γ γc γm rp N me ⊢
      swift.sendCtxAt γ γc γm rp rr N me := by
  iintro ⟨#HR, #Hc⟩
  iunfold swift.sendCtxN at Hc
  icases Hc with ⟨%rr', %s, %γw, %γs, %csv, #HR', #HisR, #Hs, #Hsb, #Hcs, %Hcodes⟩
  icombine HR HR' gives %Hrr
  subst Hrr
  ihave #R2 := HisR
  iunfold replica.isReplica at R2
  icases R2 with ⟨%lg, %cfgp, %tbl, %pc, %fr, %nid, %ents, %γpc, %pwsl, %alsl, %latsl, %pws,
    %cwm, -, -, #HN, #HId, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, %HNp, -⟩
  iunfold swift.sendCtxAt
  iexists s, γw, γs, csv
  iframe HId HN HisR Hs Hsb Hcs
  ipureintro
  exact ⟨Hcodes, HNp.2.1, HNp.2.2.1, HNp.2.2.2⟩

omit [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps] [replica.Assumptions] in
theorem swift.sendCtxAt_agree (γ : sp.Names) (γc γm : GName) (rp rr : Loc) (N N' : Nat)
    (me me' : w32) :
    swift.sendCtxAt γ γc γm rp rr N me ∗ swift.sendCtxAt γ γc γm rp rr N' me' ⊢
      ⌜N = N' ∧ me = me'⌝ := by
  iintro ⟨#H1, #H2⟩
  iunfold swift.sendCtxAt at H1 H2
  icases H1 with ⟨%s, %γw, %γs, %csv, #HId, #HN, -, -, -, -, %Hp⟩
  icases H2 with ⟨%s', %γw', %γs', %csv', #HId', #HN', -, -, -, -, %Hp'⟩
  icombine HId HId' gives %Hme
  icombine HN HN' gives %HN2
  ipureintro
  refine ⟨?_, Hme⟩
  have h1 := Hp.2.2.2
  have h2 := Hp'.2.2.2
  have h3 := congrArg BitVec.toNat HN2
  simp only [BitVec.toNat_ofInt] at h3
  omega

theorem swift.NilDepOfCmdId.wp (x : swift.CommandId) :
    {{ (True : IProp netDistGF) }}
      (App (Val (@! swift.NilDepOfCmdId)) (Val #x))
    {{ (sl : GoSlice), RET #sl; sl ↦* [x] }} := by
  wp_start
  wp_auto
  wp_apply wp_slice_literal (V := swift.CommandId) _
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  try wp_auto
  iapply HΦ
  iexact Hsl

end proof

end Perennial.github_com.imdea_software.swiftpaxos
