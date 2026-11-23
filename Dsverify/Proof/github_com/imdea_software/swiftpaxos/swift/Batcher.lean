/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/Batcher.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The batcher (swift/batcher.go): `NewBatcher`'s goroutine (notes/prove-swift.md §12).

Each round takes one operation (a fast ack or a light slow ack), then as many more of each
channel as `len` reported, builds an `MAcks` (all of them) and an `MOptAcks` (the entries of the
first ack's ballot, a slow ack replacing its command's fast entry), sends the clients' copies
(`MFastAckClient`, `MLightSlowAck`) and then the `MOptAcks` if every ack had the first's ballot,
else the `MAcks`, to all peers.

Hypotheses (open): the four messages' `Marshal` (`marshalOk`), `clientChecksum`'s spec
(ReplyChan.lean), `releaseFastAck`'s (the fast-ack pool).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.ReplyChan
public import Perennial.Golang.Theory.IfJoin

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
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
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [swift.Assumptions] [replica.Assumptions]

set_option goose.wp.extras true

omit [SwiftNetPkgState netDistGF] [swift.Assumptions] [replica.Assumptions] in
theorem swift.map_to_of (l : List sp.CmdId) : (l.map swift.ofCmdId).map swift.toCmdId = l := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, ih]; rfl

omit [SwiftNetPkgState netDistGF] [swift.Assumptions] [replica.Assumptions] in
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

omit [SwiftNetPkgState netDistGF] [swift.Assumptions] [replica.Assumptions] in
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

omit [SwiftNetPkgState netDistGF] [swift.Assumptions] [replica.Assumptions] in
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

omit [SwiftNetPkgState netDistGF] [swift.Assumptions] [replica.Assumptions] in
theorem swift.optNL_nil (γc γm : GName) (me b0 : w32) : ⊢ swift.optNL γc γm me b0 [] := by
  iunfold swift.optNL; ileft; ipureintro; intro p hp; simp at hp

omit [SwiftNetPkgState netDistGF] [swift.Assumptions] [replica.Assumptions] in
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

omit [SwiftNetPkgState netDistGF] [swift.Assumptions] [replica.Assumptions] in
/-- Any entries, `me` not the leader (a slow ack's entry). -/
theorem swift.optNL_slow (γc γm : GName) (me b0 : w32) (aps : List (swift.Ack × sp.Ack))
    (N : Nat) (fr : Bool) (l : List GoString) :
    sp.cfg γc γm N fr l ∗ ⌜sp.rid me ≠ sp.leaderOf N (sp.bal b0)⌝ ⊢
      swift.optNL γc γm me b0 aps := by
  iintro ⟨#Hc, %Hne⟩
  iunfold swift.optNL
  iright; iexists N, fr, l; iframe Hc; ipureintro; exact Hne

omit [SwiftNetPkgState netDistGF] [swift.Assumptions] [replica.Assumptions] in
/-- Any entries, from a slow ack of `me` in `b0` (its C16 witness). -/
theorem swift.optNL_of_slow (γc γm : GName) (me b0 : w32) (aps : List (swift.Ack × sp.Ack))
    (s : sp.SlowAck) (hr : s.rep = me) (hb : sp.bal s.bal = sp.bal b0) :
    (∃ N fr l, sp.cfg γc γm N fr l ∗ ⌜sp.rid s.rep ≠ sp.leaderOf N (sp.bal s.bal)⌝) ⊢
      swift.optNL γc γm me b0 aps := by
  iintro ⟨%N, %fr, %l, #Hc, %Hne⟩
  iapply swift.optNL_slow γc γm me b0 aps N fr l
  iframe Hc; ipureintro; rw [← hr, ← hb]; exact Hne

omit [SwiftNetPkgState netDistGF] [swift.Assumptions] [replica.Assumptions] in
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

omit [SwiftNetPkgState netDistGF] [swift.Assumptions] [replica.Assumptions] in
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

omit [SwiftNetPkgState netDistGF] [swift.Assumptions] [replica.Assumptions] in
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

omit [SwiftNetPkgState netDistGF] [replica.Assumptions] in
theorem swift.ackRepr_of_fast (fa : swift.MFastAck) (f : sp.FastAck) :
    swift.fastAckRepr fa f ⊢
      swift.ackRepr (swift.Ack.mk fa.CmdId' fa.Dep' fa.Checksum' fa.Seqnum') (swift.ackOfFast f) := by
  iintro #H
  iunfold swift.fastAckRepr at H
  icases H with ⟨%Hr, #Hd, #Hc⟩
  unfold swift.ackRepr swift.ackOfFast
  iframe Hd Hc
  ipureintro; exact ⟨Hr.2.2.1, Hr.2.2.2⟩

omit [SwiftNetPkgState netDistGF] [swift.Assumptions] [replica.Assumptions] in
/-- A map's entries' resources, the keys visited so far (`keys.take i`) taken out. -/
theorem swift.mapIter_start {V : Type} (M : GMap swift.CommandId V) (E : V → IProp netDistGF)
    (keys : List swift.CommandId) :
    ([∗map] _k ↦ v ∈ M, E v) ⊢ [∗map] k ↦ v ∈ M, iprop(⌜k ∉ keys.take 0⌝ -∗ E v) := by
  apply BigSepM.bigSepM_mono_of_forall
  iintro %k %v H -
  iexact H

omit [SwiftNetPkgState netDistGF] [swift.Assumptions] [replica.Assumptions] in
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

omit [SwiftNetPkgState netDistGF] [replica.Assumptions] in
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

omit [SwiftNetPkgState netDistGF] [replica.Assumptions] in
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

set_option maxHeartbeats 8000000 in
theorem swift.NewBatcher.wp_proof (wp_cc : swift.clientChecksum.specR (hG := hG))
    (wp_rel : swift.releaseFastAck.specR (hG := hG))
    (hmo : swift.MOptAcks.marshalH (hG := hG)) (hma : swift.MAcks.marshalH (hG := hG))
    (hmf : swift.MFastAckClient.marshalH (hG := hG))
    (hms : swift.MLightSlowAck.marshalH (hG := hG))
    (wp_sendc : replica.Sender.SendToClient.spec (hG := hG))
    (wp_senda : replica.Sender.SendToAll.spec (hG := hG)) :
    swift.NewBatcher.specI (hG := hG) := by
  intro rp rr γ γc γm fs upv
  wp_start as ⟨#HReplica, #HShutdown, #HfreeS, #Hupv⟩
  haveI := swift.hlog.cmdId_intoValInj (sem := sem)
  wp_auto
  wp_apply chan.wp_make2 (V := swift.BatcherOp) (W64 16) as %fa %γ1 ⟨#Hfa, %Hfacap, Hfaown⟩
  · ipureintro; decide
  wp_apply chan.wp_make2 (V := swift.BatcherOp) (W64 16) as %ls %γ2 ⟨#Hls, %Hlscap, Hlsown⟩
  · ipureintro; decide
  try wp_auto
  ipersist b
  ipersist r
  ipersist freeFastAck
  ipersist freeSlowAck
  ipersist «$r0»
  iapply fupd_wp
  imod start_bag (swift.batchFastP γ γc γm rp) (ChanState.Buffered []) fa γ1
    (by trivial) $$ [$Hfa] [Hfaown] with #Hbf
  · iexact Hfaown
  imod start_bag (swift.batchSlowP γ γc γm rp) (ChanState.Buffered []) ls γ2
    (by trivial) $$ [$Hls] [Hlsown] with #Hbs
  · iexact Hlsown
  imodintro
  wp_apply wp_fork
  · ihave #R2 := «$r0»
    iStructNamedPrefix R2 "B"
    wp_auto_lc 2
    ihave HL : ("Hlc1" ∷ £ 1 ∗ "Hlc2" ∷ £ 1 : IProp netDistGF) $$ [Hlc1 Hlc2]
    · iframe
    wp_for HL
    wp_apply_core chan.wp_select_blocking
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- a fast ack first
      iapply swift.bag_clauseT $$ Hlc1 Hlc2 Hbf
      inext
      iintro %op Hop
      wp_auto_lc 2
      iunfold swift.batchFastP at Hop
      icases Hop with ⟨%N, %me, %l, %fa0, %f0, #Hctx, %Hmsg, Hl, #Hrep, #Hok, %Hf, Hcl⟩
      ihave #Hat := swift.sendCtxN_at γ γc γm rp rr N me $$ [$HReplica $Hctx]
      ihave #Hat2 := Hat
      iunfold swift.sendCtxAt at Hat2
      icases Hat2 with ⟨%s, %γw, %γs, %csv, #HId, #HN, #HisR, #Hsnd, #Hsbag, #Hcs, %Hpc⟩
      ihave #Hcs2 := Hcs
      iStructNamedPrefix Hcs2 "CS"
      ihave #Hrep2 := Hrep
      iunfold swift.fastAckRepr at Hrep2
      icases Hrep2 with ⟨%Hfr, #Hdep0, #Hcs0⟩
      rw [Hmsg]
      wp_auto
      wp_func_call
      wp_call
      wp_apply (wp_Len (V := swift.BatcherOp) (t := swift.BatcherOp.ty) fa γ1) $$ [$Hfa] as %fl0 %Hfl0
      wp_func_call
      wp_call
      wp_apply (wp_Len (V := swift.BatcherOp) (t := swift.BatcherOp.ty) ls γ2) $$ [$Hls] as %sl0 %Hsl0
      rw [Hfacap] at Hfl0
      rw [Hlscap] at Hsl0
      wp_apply (wp_slice_make2 (V := swift.MFastAck) (fl0 + W64 1)) as %fsl ⟨Hfsl, Hfslc⟩
      · ipureintro; word
      wp_apply (wp_slice_make2 (V := swift.MLightSlowAck) sl0) as %ssl ⟨Hssl, Hsslc⟩
      · ipureintro; word
      try wp_auto
      irename «$r0» => Hacks
      generalize hacksl : «$r0_ptr» = acksl at *
      wp_apply wp_slice_literal (V := swift.Ack) _
      isplitr
      · ipureintro; rfl
      iintro %asl ⟨Hasl, Haslc⟩
      try wp_auto
      irename «$r0» => Hopt
      wp_apply (wp_map_make1 (K := swift.CommandId) (V := w64)) as %ism Hism
      wp_apply (wp_mapInsert (K := swift.CommandId) (V := w64)) $$ [$Hism] as Hism
      wp_apply (wp_map_make1 (K := swift.CommandId) (V := swift.MFastAckClient)) as %fcm Hfcm
      wp_apply (wp_map_make1 (K := swift.CommandId) (V := swift.MLightSlowAck)) as %scm Hscm
      try wp_auto
      ihave Hfcm : (∃ FM : GMap swift.CommandId swift.MFastAckClient, fcm ↦$ FM ∗
          [∗map] _k ↦ c ∈ FM, swift.facEntry γ γc γm c) $$ [Hfcm]
      · iexists ∅; iframe; iapply BigSepM.bigSepM_empty.2; itrivial
      generalize hst : op.sendToClient' = st at *
      wp_if_join (fun v => iprop(⌜v = executeVal⌝ ∗ (∃ FM : GMap swift.CommandId swift.MFastAckClient, fcm ↦$ FM ∗
          [∗map] _k ↦ c ∈ FM, swift.facEntry γ γc γm c) ∗ fastAck_ptr ↦ l ∗ l ↦ fa0 ∗
          fastAckClientMsgs_ptr ↦ fcm)) with [Hfcm Hcl fastAck Hl fastAckClientMsgs]
      · iframe
      · try wp_auto
        ihave #Hcl2 : swift.facClientOk γ γc γm f0 $$ [Hcl]
        · iexact Hcl
        wp_apply wp_cc fa0.Checksum' fa0.Dep' f0.cs (f0.dep.map swift.ofCmdId) DFrac.discard
          DFrac.discard $$ [$Hcs0 $Hdep0] as %csl ⟨-, -, %d, Hcsl, #Hdh, %Hd⟩
        · ipureintro; exact ⟨Hf.2.1.2, Hf.2.2.2, by simp; exact Hf.2.1.1⟩
        try wp_auto
        icases Hfcm with ⟨%FM, Hm, HM⟩
        wp_apply (wp_mapInsert (K := swift.CommandId) (V := swift.MFastAckClient)) $$ [$Hm] as Hm
        iframe
        isplitr
        · ipureintro; rfl
        iapply swift.bigSepM_overwrite
        iframe HM
        isimp only [swift.map_to_of] at Hdh
        unfold swift.facEntry
        iexists (f0.cs ++ [d])
        iframe Hcsl
        obtain ⟨hr, hb, hx, -⟩ := Hfr
        simp only [hr, hb, hx]
        isplitr
        · iapply swift.facOk_of
          iframe Hok Hdh Hcl2
        ipureintro
        refine ⟨by simp; have := Hf.2.1.2.1; omega, ?_⟩
        intro h hh; simp at hh; rcases hh with hh | hh
        · exact Hf.2.1.2.2 h hh
        · subst hh; exact Hd
      iintro %v0 ⟨%Hv0, Hfcm, fastAck, Hl, fastAckClientMsgs⟩
      subst Hv0
      try wp_auto
      ihave %Hfl := ownSlice_len _ _ _ $$ Hfsl
      simp only [List.length_replicate] at Hfl
      have hb0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z fsl.len := by
        constructor
        · decide
        · have := Hfl.1; word
      isimp only [hb0, ↓reduceIte]
      wp_apply (wp_store_slice_index (V := swift.MFastAck) fsl (sint.Z (W64 0)) _ fa0) $$ [$Hfsl] as Hfsl
      · ipureintro
        refine ⟨by decide, ?_⟩
        rw [List.length_replicate, Hfl.1]
        have h := hb0.2
        have e : (sint.nat fsl.len : Int) = sint.Z fsl.len := by
          show ((sint.Z fsl.len).toNat : Int) = _; omega
        rw [e]; exact h
      try wp_auto
      wp_apply wp_rel $$ [Hl]
      · iframe Hupv; iexists fa0; iexact Hl
      try wp_auto
      ipersist acks
      ipersist optAcks
      ipersist is
      ipersist fastAckClientMsgs
      ipersist slowAckClientMsgs
      ipersist fLen
      ipersist sLen
      ipersist Hacks
      ihave #Hacks2 := Hacks
      iStructNamedPrefix Hacks2 "MA"
      have hfl1 : sint.Z (fl0 + W64 1) = sint.Z fl0 + 1 := by have := Hfl0.2; word
      ihave Hopt' : swift.optSt γ γc γm me fa0.Ballot' «$r0_ptr» ism 1 $$ [Hopt Hasl Haslc Hism]
      · iunfold swift.optSt
        iexists _, [(swift.Ack.mk fa0.CmdId' fa0.Dep' fa0.Checksum' fa0.Seqnum',
          swift.ackOfFast f0)], _
        isimp only [List.map_cons, List.map_nil]
        iframe Hopt Hasl Haslc Hism
        isplitl
        · iapply BigSepL.bigSepL_singleton.2
          isplitl
          · iapply swift.ackRepr_of_fast; iexact Hrep
          obtain ⟨hr, hb, -⟩ := Hfr
          rw [hb, ← Hf.1]
          iapply swift.ackOk_of_fast γ f0 Hf.2.2.1; iexact Hok
        isplitr
        rotate_left
        · iunfold swift.optNL; ileft; ipureintro; intro p hp; simp at hp; subst hp; exact Hf.2.2.1
        ipureintro
        refine ⟨?_, by simp, ?_⟩
        · intro p hp; simp at hp; subst hp; exact Hf.2.1
        · intro k j hk
          by_cases e : k = fa0.CmdId'
          · subst e; simp at hk; subst hk; exact ⟨by decide, _, rfl, rfl⟩
          · simp at hk; exact absurd hk.1.symm e
      have hn1 : sint.nat (fl0 + W64 1) = sint.nat fl0 + 1 := by
        have := Hfl0.1; show (sint.Z _).toNat = (sint.Z _).toNat + 1; rw [hfl1]; omega
      ihave Hfs : swift.fastSlots γ fsl (sint.nat fl0 + 1) [(fa0, f0)] $$ [Hfsl]
      · iunfold swift.fastSlots
        have e := swift.slots_set ([] : List swift.MFastAck) (sint.nat fl0 + 1)
          (zero_val swift.MFastAck) fa0 (by omega)
        simp only [List.length_nil, List.nil_append] at e
        rw [hn1, e]
        isimp only [List.map_cons, List.map_nil, List.length_cons, List.length_nil]
        isplitl [Hfsl]
        · iExactEq Hfsl; congr 2
        isplitl
        · iapply BigSepL.bigSepL_singleton.2
          iframe Hrep Hok
        ipureintro
        intro p hp; simp at hp; subst hp; exact Hf.2.1
      ihave HL : (∃ (iv : w64) (bv : w32) (fps : List (swift.MFastAck × sp.FastAck)),
          "i" ∷ i_ptr ↦ iv ∗ "ballot" ∷ ballot_ptr ↦ bv ∗
          "Hfs" ∷ swift.fastSlots γ fsl (sint.nat fl0 + 1) fps ∗
          "Hopt" ∷ swift.optSt γ γc γm me fa0.Ballot' «$r0_ptr» ism fps.length ∗
          "Hfcm" ∷ swift.facMap γ γc γm fcm ∗
          "%Hi" ∷ ⌜1 ≤ sint.Z iv ∧ sint.Z iv ≤ sint.Z fl0 + 1 ∧ fps.length = sint.nat iv ∧
            (bv = fa0.Ballot' ∨ bv = W32 (-1))⌝ : IProp netDistGF) $$ [i ballot Hfs Hopt' Hfcm]
      · iexists (W64 1), fa0.Ballot', [(fa0, f0)]
        iunfold swift.facMap
        iframe
        ipureintro
        refine ⟨by decide, by have := Hfl0.1; simp; omega, by rfl, Or.inl rfl⟩
      wp_for HL
      by_cases hlt : sint.Z iv < sint.Z (fl0 + W64 1)
      · simp only [hlt, _root_.decide_true]
        cleanup_bool_decide
        wp_auto
        wp_apply (wp_bag_receive (t := swift.BatcherOp.ty) γ1 fa (swift.batchFastP γ γc γm rp))
          $$ [$Hbf] as %op1 Hop1
        iunfold swift.batchFastP at Hop1
        icases Hop1 with ⟨%N1, %me1, %l1, %fa1, %f1, #Hctx1, %Hmsg1, Hl1, #Hrep1, #Hok1, %Hf1, Hcl1⟩
        ihave #Hat1 := swift.sendCtxN_at γ γc γm rp rr N1 me1 $$ [$HReplica $Hctx1]
        ihave %Hag := swift.sendCtxAt_agree γ γc γm rp rr N N1 me me1 $$ [$Hat $Hat1]
        obtain ⟨rfl, rfl⟩ := Hag
        ihave #Hrep12 := Hrep1
        iunfold swift.fastAckRepr at Hrep12
        icases Hrep12 with ⟨%Hfr1, #Hdep1, #Hcs1⟩
        try wp_auto
        rw [Hmsg1]
        try wp_auto
        iunfold swift.fastSlots at Hfs
        icases Hfs with ⟨Hfsl, Hfsr, %Hfsw⟩
        ihave %Hfl' := ownSlice_len _ _ _ $$ Hfsl
        rw [List.length_append, List.length_map, List.length_replicate] at Hfl'
        have hlen : sint.Z fsl.len = sint.Z fl0 + 1 := by
          have h1 := Hfl'.1; have h2 := Hi.2.2.1
          have e1 := swift.snat_eq fsl.len Hfl'.2
          have e2 := swift.snat_eq iv (by omega)
          have e3 := swift.snat_eq fl0 Hfl0.1
          have h3 : (fps.length : Int) ≤ sint.nat fl0 + 1 := by omega
          omega
        have hi0 : 0 ≤ sint.Z iv ∧ sint.Z iv < sint.Z fsl.len := by
          rw [hfl1] at hlt; omega
        try isimp only [hi0, _root_.and_self, ↓reduceIte]
        wp_apply (wp_store_slice_index (V := swift.MFastAck) fsl (sint.Z iv) _ fa1) $$ [$Hfsl] as Hfsl
        · ipureintro; refine ⟨hi0.1, ?_⟩
          rw [List.length_append, List.length_map, List.length_replicate]
          have h2 := Hi.2.2.1
          have e2 := swift.snat_eq iv (by omega)
          have e3 := swift.snat_eq fl0 Hfl0.1
          rw [hfl1] at hlt
          omega
        try wp_auto
        ihave #Hok12 := Hok1
        iunfold sp.fastAckOk at Hok12
        icases Hok12 with ⟨%Hw1, -⟩
        have hwire1 : 0 ≤ sint.Z fa1.Ballot' := by
          rw [Hfr1.2.1]; exact Hw1.2
        wp_if_join (fun v => iprop(⌜v = executeVal⌝ ∗ ∃ bv' : w32, ballot_ptr ↦ bv' ∗
            swift.optSt γ γc γm me fa0.Ballot' «$r0_ptr» ism (fps.length + 1) ∗
            ⌜bv' = fa0.Ballot' ∨ bv' = W32 (-1)⌝ ∗ f_ptr ↦ l1 ∗ l1 ↦ fa1))
          with [ballot Hopt f Hl1]
        · -- the first ack's ballot: a new `MOptAcks` entry
          iunfold swift.optSt at Hopt
          icases Hopt with ⟨%asl1, %aps, %IM, Ho, Ha, Hac, Hr, Hm, %Hp, #Hnl⟩
          try wp_auto
          wp_apply (wp_mapInsert (K := swift.CommandId) (V := w64)) $$ [$Hm] as Hm
          try wp_auto
          wp_apply wp_slice_literal (V := swift.Ack) _
          isplitr
          · ipureintro; rfl
          iintro %sl1 ⟨Hsl1, -⟩
          try wp_auto
          ihave %Hal := ownSlice_len _ _ _ $$ Ha
          wp_apply (wp_slice_append (V := swift.Ack)) $$ [$Ha $Hac $Hsl1] as %asl2 ⟨Ha, Hac, -⟩
          try wp_auto
          have hb01 : fa1.Ballot' = fa0.Ballot' := by
            rcases Hi.2.2.2 with h | h
            · exact h
            · exfalso; rw [h] at hwire1; exact absurd hwire1 (by decide)
          iframe
          isplitr
          · ipureintro; rfl
          isplitl [Ho Ha Hac Hm Hr]
          · iunfold swift.optSt
            iexists asl2, aps ++ [(swift.Ack.mk fa1.CmdId' fa1.Dep' fa1.Checksum' fa1.Seqnum',
              swift.ackOfFast f1)], _
            isimp only [List.map_append, List.map_cons, List.map_nil]
            iframe Ho Ha Hac Hm
            isplitl [Hr]
            · iapply BigSepL.bigSepL_snoc.2
              iframe Hr
              isplitl
              · iapply swift.ackRepr_of_fast; iexact Hrep1
              have e1 : sp.bal fa0.Ballot' = sp.bal f1.bal := by rw [← hb01, Hfr1.2.1]
              rw [e1, ← Hf1.1]
              iapply swift.ackOk_of_fast γ f1 Hf1.2.2.1; iexact Hok1
            isplitr
            rotate_left
            · iapply swift.optNL_snoc _ _ _ _ _ _ Hf1.2.2.1; iexact Hnl
            ipureintro
            refine ⟨?_, ?_, ?_⟩
            · intro p hp; simp at hp; rcases hp with hp | hp
              · exact Hp.1 p hp
              · subst hp; exact Hf1.2.1
            · have := Hp.2.1; simp; omega
            · intro k j hk
              have hlen : sint.nat asl1.len = aps.length := by simpa using Hal.1.symm
              by_cases e : k = fa1.CmdId'
              · subst e; simp at hk; subst hk
                refine ⟨Hal.2, (swift.Ack.mk fa1.CmdId' fa1.Dep' fa1.Checksum' fa1.Seqnum',
                  swift.ackOfFast f1), ?_, rfl⟩
                rw [hlen]; simp
              · have hk' : IM !! k = some j := by
                  have e' : ¬ fa1.CmdId' = k := fun h => e h.symm
                  simpa [e'] using hk
                obtain ⟨hj0, p, hp1, hp2⟩ := Hp.2.2 k j hk'
                refine ⟨hj0, p, ?_, hp2⟩
                rw [List.getElem?_append_left]; exact hp1
                exact (List.getElem?_eq_some_iff.mp hp1).1
          ipureintro; left; exact hb01
        · -- another ballot: no `MOptAcks`
          ihave Hopt := swift.optSt_mono γ γc γm me fa0.Ballot' «$r0_ptr» ism fps.length (fps.length + 1)
              (by omega) $$ Hopt
          try wp_auto
          iframe
          ipureintro; right; rfl
        iintro %v1 ⟨%Hv1, %bv', ballot, Hopt, %Hbv', f, Hl1⟩
        subst Hv1
        try wp_auto
        generalize hst1 : op1.sendToClient' = st1 at *
        wp_if_join (fun v => iprop(⌜v = executeVal⌝ ∗ swift.facMap γ γc γm fcm ∗
            f_ptr ↦ l1 ∗ l1 ↦ fa1)) with [Hfcm Hcl1 f Hl1]
        · iframe
        · try wp_auto
          ihave #Hcl2 : swift.facClientOk γ γc γm f1 $$ [Hcl1]
          · iexact Hcl1
          wp_apply wp_cc fa1.Checksum' fa1.Dep' f1.cs (f1.dep.map swift.ofCmdId) DFrac.discard
            DFrac.discard $$ [$Hcs1 $Hdep1] as %csl ⟨-, -, %d, Hcsl, #Hdh, %Hd⟩
          · ipureintro; exact ⟨Hf1.2.1.2, Hf1.2.2.2, by simp; exact Hf1.2.1.1⟩
          try wp_auto
          iunfold swift.facMap at Hfcm
          icases Hfcm with ⟨%FM, Hm, HM⟩
          wp_apply (wp_mapInsert (K := swift.CommandId) (V := swift.MFastAckClient)) $$ [$Hm] as Hm
          iframe
          isplitr
          · ipureintro; rfl
          iunfold swift.facMap
          iexists _
          iframe Hm
          iapply swift.bigSepM_overwrite
          iframe HM
          isimp only [swift.map_to_of] at Hdh
          unfold swift.facEntry
          iexists (f1.cs ++ [d])
          iframe Hcsl
          obtain ⟨hr, hb, hx, -⟩ := Hfr1
          simp only [hr, hb, hx]
          isplitr
          · iapply swift.facOk_of
            iframe Hok1 Hdh Hcl2
          ipureintro
          refine ⟨by simp; have := Hf1.2.1.2.1; omega, ?_⟩
          intro h hh; simp at hh; rcases hh with hh | hh
          · exact Hf1.2.1.2.2 h hh
          · subst hh; exact Hd
        iintro %v2 ⟨%Hv2, Hfcm, f, Hl1⟩
        subst Hv2
        try wp_auto
        wp_apply wp_rel $$ [Hl1]
        · iframe Hupv; iexists fa1; iexact Hl1
        wp_for_post
        have hlt' : sint.Z iv < sint.Z fl0 + 1 := by rw [hfl1] at hlt; exact hlt
        have e2 := swift.snat_eq iv (by omega)
        have e3 := swift.snat_eq fl0 Hfl0.1
        have hiv1 : sint.Z (iv + W64 1) = sint.Z iv + 1 := by
          have := Hfl0.2; word
        iframe
        iexists (iv + W64 1), bv', fps ++ [(fa1, f1)]
        iframe
        isplitl [Hfsl Hfsr]
        · iunfold swift.fastSlots
          have hset : (sint.Z iv).toNat = (fps.map Prod.fst).length := by
            simp; omega
          rw [hset, swift.slots_set _ _ _ _ (by omega)]
          isimp only [List.map_append, List.map_cons, List.map_nil, List.length_append,
            List.length_cons, List.length_nil]
          isplitl [Hfsl]
          · iExactEq Hfsl; congr 2
          isplitl [Hfsr]
          · iapply BigSepL.bigSepL_snoc.2
            iframe Hfsr Hrep1 Hok1
          ipureintro
          intro p hp; simp at hp; rcases hp with hp | hp
          · exact Hfsw p hp
          · subst hp; exact Hf1.2.1
        isplitl [Hopt]
        · iapply swift.optSt_mono _ _ _ _ _ _ _ _ _ (by simp) $$ Hopt
        ipureintro
        rw [hiv1]
        have e4 := swift.snat_eq (iv + W64 1) (by omega)
        refine ⟨by omega, by omega, ?_, Hbv'⟩
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      · simp only [hlt, decide_false]
        cleanup_bool_decide
        try simp only [Bool.false_eq_true, ↓reduceIte]
        try wp_auto
        have hfpsl : fps.length = sint.nat fl0 + 1 := by
          have e2 := swift.snat_eq iv (by omega)
          have e3 := swift.snat_eq fl0 Hfl0.1
          rw [hfl1] at hlt; omega
        ihave HL2 : (∃ (iv : w64) (bv : w32) (sps : List (swift.MLightSlowAck × sp.SlowAck)),
            "i" ∷ i_ptr ↦ iv ∗ "ballot" ∷ ballot_ptr ↦ bv ∗
            "Hss" ∷ swift.slowSlots γ γc γm ssl (sint.nat sl0) sps ∗
            "Hopt" ∷ swift.optSt γ γc γm me fa0.Ballot' «$r0_ptr» ism (fps.length + sps.length) ∗
            "Hscm" ∷ swift.slowMap γ γc γm scm ∗
            "%Hi2" ∷ ⌜0 ≤ sint.Z iv ∧ sint.Z iv ≤ sint.Z sl0 ∧ sps.length = sint.nat iv ∧
              (bv = fa0.Ballot' ∨ bv = W32 (-1))⌝ : IProp netDistGF)
            $$ [i ballot Hssl Hopt Hscm]
        · iexists (W64 0), bv, []
          iframe
          isplitl [Hssl]
          · iunfold swift.slowSlots
            isimp only [List.map_nil, List.nil_append, List.length_nil, Nat.sub_zero]
            isplitl [Hssl]
            · iexact Hssl
            isplitl
            · iapply BigSepL.bigSepL_nil.2; itrivial
            ipureintro; intro p hp; simp at hp
          isplitl [Hscm]
          · iunfold swift.slowMap; iexists ∅; iframe; iapply BigSepM.bigSepM_empty.2; itrivial
          ipureintro
          refine ⟨by decide, by have := Hsl0.1; simpa using this, by simp; rfl, Hi.2.2.2⟩
        wp_for HL2
        by_cases hlt2 : sint.Z iv < sint.Z sl0
        · simp only [hlt2, _root_.decide_true]
          cleanup_bool_decide
          try simp only [↓reduceIte, ite_true]
          wp_auto
          wp_apply (wp_bag_receive (t := swift.BatcherOp.ty) γ2 ls (swift.batchSlowP γ γc γm rp))
            $$ [$Hbs] as %op2 Hop2
          iunfold swift.batchSlowP at Hop2
          icases Hop2 with ⟨%N2, %me2, %l2, %sa2, %s2, #Hctx2, %Hmsg2, #Hl2, %Hs2, #Hsok⟩
          ihave #Hl2c := Hl2
          iStructNamedPrefix Hl2c "SB"
          ihave #Hat2 := swift.sendCtxN_at γ γc γm rp rr N2 me2 $$ [$HReplica $Hctx2]
          ihave %Hag2 := swift.sendCtxAt_agree γ γc γm rp rr N N2 me me2 $$ [$Hat $Hat2]
          obtain ⟨rfl, rfl⟩ := Hag2
          ihave #Hsok2 := Hsok
          isimp only [sp.msgOk] at Hsok2
          icases Hsok2 with ⟨%Hw2, #Hacc2, #Hnl2⟩
          try wp_auto
          rw [Hmsg2]
          try wp_auto
          iunfold swift.slowSlots at Hss
          icases Hss with ⟨Hssl, Hssr, %Hssw⟩
          ihave %Hsl' := ownSlice_len _ _ _ $$ Hssl
          rw [List.length_append, List.length_map, List.length_replicate] at Hsl'
          have e2 := swift.snat_eq iv (by omega)
          have e3 := swift.snat_eq sl0 Hsl0.1
          have hsps : (sps.length : Int) ≤ sint.nat sl0 := by omega
          have hlen2 : sint.Z ssl.len = sint.Z sl0 := by
            have e1 := swift.snat_eq ssl.len Hsl'.2
            have h1 := Hsl'.1
            omega
          have hi2 : 0 ≤ sint.Z iv ∧ sint.Z iv < sint.Z ssl.len := by omega
          try isimp only [hi2, _root_.and_self, ↓reduceIte]
          wp_apply (wp_store_slice_index (V := swift.MLightSlowAck) ssl (sint.Z iv) _ sa2)
            $$ [$Hssl] as Hssl
          · ipureintro; refine ⟨hi2.1, ?_⟩
            rw [List.length_append, List.length_map, List.length_replicate]
            omega
          try wp_auto
          have hwire2 : 0 ≤ sint.Z sa2.Ballot' := by rw [Hs2.1.2.1]; exact Hw2.2
          wp_if_join (fun v => iprop(⌜v = executeVal⌝ ∗ ∃ bv' : w32, ballot_ptr ↦ bv' ∗
              swift.optSt γ γc γm me fa0.Ballot' «$r0_ptr» ism (fps.length + sps.length + 1) ∗
              ⌜bv' = fa0.Ballot' ∨ bv' = W32 (-1)⌝ ∗ s_ptr ↦ l2))
            with [ballot Hopt s]
          · -- the first ack's ballot
            have hb02 : sa2.Ballot' = fa0.Ballot' := by
              rcases Hi2.2.2.2 with h | h
              · exact h
              · exfalso; rw [h] at hwire2; exact absurd hwire2 (by decide)
            iunfold swift.optSt at Hopt
            icases Hopt with ⟨%asl1, %aps, %IM, Ho, Ha, Hac, Hr, Hm, %Hp, #Hnl⟩
            try wp_auto
            wp_apply (wp_map_lookup2 (K := swift.CommandId) (V := w64)) $$ [$Hm] as Hm
            try wp_auto
            cases hk : IM !! sa2.CmdId' with
            | some j =>
              simp only [Option.isSome_some, _root_.decide_true, Option.getD_some]
              wp_auto
              obtain ⟨hj0, p0, hp0, hp0k⟩ := Hp.2.2 _ _ hk
              have hj : sint.nat j < aps.length := (List.getElem?_eq_some_iff.mp hp0).1
              wp_apply swift.NilDepOfCmdId.wp sa2.CmdId' as %dsl Hdsl
              ipersist Hdsl
              ihave %Hal := ownSlice_len _ _ _ $$ Ha
              have ej := swift.snat_eq j hj0
              have hjb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z asl1.len := by
                have ea := swift.snat_eq asl1.len Hal.2
                have h1 := Hal.1; simp only [List.length_map] at h1
                omega
              isimp only [hjb, _root_.and_self, ↓reduceIte]
              have hlk : (aps.map Prod.fst)[(sint.Z j).toNat]? = some p0.1 := by
                rw [show (sint.Z j).toNat = sint.nat j from rfl]; simp [hp0]
              icases ownSlice_elem_acc (sint.Z j) p0.1 asl1 (DFrac.own 1) _ hjb.1 hlk $$ Ha
                with ⟨Hel, Ha⟩
              try wp_auto
              wp_apply wp_slice_literal (V := swift.SHash) []
              isplitr
              · ipureintro; rfl
              iintro %csl ⟨Hcsl, -⟩
              ipersist Hcsl
              try wp_auto
              isimp only [hjb, _root_.and_self, ↓reduceIte]
              try wp_auto
              ihave Ha := Ha $$ Hel
              iframe
              isplitr
              · ipureintro; rfl
              isplitl [Ho Ha Hac Hr Hm]
              · iunfold swift.optSt
                iexists asl1, aps.set (sint.nat j)
                  (swift.Ack.mk p0.1.CmdId' dsl (slice.mk csl (W64 (go.arrayLiteralSize []))
                    (W64 (go.arrayLiteralSize []))) p0.1.Seqnum',
                   (⟨p0.2.id, [p0.2.id], [], p0.2.seqnum⟩ : sp.Ack)), IM
                iframe Ho Hac Hm
                isplitl [Ha]
                · iExactEq Ha; rw [List.map_set]
                isplitl [Hr]
                · icases (BigSepL.bigSepL_insert_acc hp0) $$ Hr with ⟨⟨#Hrep0, -⟩, Hr⟩
                  iapply Hr
                  iunfold swift.ackRepr at Hrep0
                  icases Hrep0 with ⟨%Hr0, -, -⟩
                  isplitl
                  · unfold swift.ackRepr
                    isplitr
                    · ipureintro; exact ⟨Hr0.1, Hr0.2⟩
                    isplitr
                    · iExactEq Hdsl
                      rw [← Hr0.1, hp0k]; rfl
                    iExactEq Hcsl; rfl
                  unfold sp.ackOk
                  simp only [↓reduceIte]
                  have e1 : sp.bal fa0.Ballot' = sp.bal s2.bal := by rw [← hb02, Hs2.1.2.1]
                  have e2 : p0.2.id = s2.id := by rw [← Hr0.1, hp0k, Hs2.1.2.2]
                  rw [e1, e2, ← Hs2.2]
                  iexact Hacc2
                isplitr
                rotate_left
                · iapply swift.optNL_of_slow γc γm me fa0.Ballot' _ s2 Hs2.2 (by rw [← Hs2.1.2.1, hb02]); iexact Hnl2
                ipureintro
                refine ⟨?_, by simp; have := Hp.2.1; omega, ?_⟩
                · intro q hq
                  rcases List.mem_or_eq_of_mem_set hq with hq | hq
                  · exact Hp.1 q hq
                  · subst hq
                    have hw := Hp.1 p0 (List.mem_of_getElem? hp0)
                    exact ⟨by unfold sp.depWf; simp, by unfold sp.hashesWf; simp⟩
                · intro k j' hk'
                  obtain ⟨hj0', q, hq1, hq2⟩ := Hp.2.2 k j' hk'
                  refine ⟨hj0', ?_⟩
                  by_cases e : sint.nat j' = sint.nat j
                  · rw [e, List.getElem?_set_self hj]
                    refine ⟨_, rfl, ?_⟩
                    rw [e, hp0] at hq1; cases hq1; exact hq2
                  · rw [List.getElem?_set_ne (Ne.symm e)]
                    exact ⟨q, hq1, hq2⟩
              ipureintro; left; exact hb02
            | none =>
              simp only [Option.isSome_none, decide_false, Option.getD_none]
              wp_auto
              ihave %Hal := ownSlice_len _ _ _ $$ Ha
              wp_apply (wp_mapInsert (K := swift.CommandId) (V := w64)) $$ [$Hm] as Hm
              try wp_auto
              wp_apply swift.NilDepOfCmdId.wp sa2.CmdId' as %dsl Hdsl
              ipersist Hdsl
              try wp_auto
              wp_apply wp_slice_literal (V := swift.SHash) []
              isplitr
              · ipureintro; rfl
              iintro %csl ⟨Hcsl, -⟩
              ipersist Hcsl
              try wp_auto
              wp_apply wp_slice_literal (V := swift.Ack) _
              isplitr
              · ipureintro; rfl
              iintro %sl1 ⟨Hsl1, -⟩
              try wp_auto
              wp_apply (wp_slice_append (V := swift.Ack)) $$ [$Ha $Hac $Hsl1] as %asl2 ⟨Ha, Hac, -⟩
              try wp_auto
              iframe
              isplitr
              · ipureintro; rfl
              isplitl [Ho Ha Hac Hr Hm]
              · iunfold swift.optSt
                iexists asl2, aps ++ [(swift.Ack.mk sa2.CmdId' dsl (slice.mk csl
                    (W64 (go.arrayLiteralSize [])) (W64 (go.arrayLiteralSize []))) 0,
                   (⟨s2.id, [s2.id], [], 0⟩ : sp.Ack))], _
                isimp only [List.map_append, List.map_cons, List.map_nil]
                iframe Ho Ha Hac Hm
                isplitl [Hr]
                · iapply BigSepL.bigSepL_snoc.2
                  iframe Hr
                  isplitl
                  · unfold swift.ackRepr
                    isplitr
                    · ipureintro; exact ⟨Hs2.1.2.2, rfl⟩
                    isplitr
                    · iExactEq Hdsl
                      rw [← Hs2.1.2.2]; rfl
                    iExactEq Hcsl; rfl
                  unfold sp.ackOk
                  simp only [↓reduceIte]
                  have e1 : sp.bal fa0.Ballot' = sp.bal s2.bal := by rw [← hb02, Hs2.1.2.1]
                  rw [e1, ← Hs2.2]
                  iexact Hacc2
                isplitr
                rotate_left
                · iapply swift.optNL_of_slow γc γm me fa0.Ballot' _ s2 Hs2.2 (by rw [← Hs2.1.2.1, hb02]); iexact Hnl2
                ipureintro
                refine ⟨?_, ?_, ?_⟩
                · intro q hq; simp at hq; rcases hq with hq | hq
                  · exact Hp.1 q hq
                  · subst hq; exact ⟨by unfold sp.depWf; simp, by unfold sp.hashesWf; simp⟩
                · have := Hp.2.1; simp; omega
                · intro k j hk
                  have hlen : sint.nat asl1.len = aps.length := by simpa using Hal.1.symm
                  by_cases e : k = sa2.CmdId'
                  · subst e; simp at hk; subst hk
                    refine ⟨Hal.2, (swift.Ack.mk sa2.CmdId' dsl (slice.mk csl
                      (W64 (go.arrayLiteralSize [])) (W64 (go.arrayLiteralSize []))) 0,
                      (⟨s2.id, [s2.id], [], 0⟩ : sp.Ack)), ?_, rfl⟩
                    rw [hlen]; simp
                  · have hk' : IM !! k = some j := by
                      have e' : ¬ sa2.CmdId' = k := fun h => e h.symm
                      simpa [e'] using hk
                    obtain ⟨hj0, q, hq1, hq2⟩ := Hp.2.2 k j hk'
                    refine ⟨hj0, q, ?_, hq2⟩
                    rw [List.getElem?_append_left]; exact hq1
                    exact (List.getElem?_eq_some_iff.mp hq1).1
              ipureintro; left; exact hb02
          · ihave Hopt := swift.optSt_mono γ γc γm me fa0.Ballot' «$r0_ptr» ism (fps.length + sps.length)
                (fps.length + sps.length + 1) (by omega) $$ Hopt
            try wp_auto
            iframe
            ipureintro; right; rfl
          iintro %v1 ⟨%Hv1, %bv', ballot, Hopt, %Hbv', s⟩
          subst Hv1
          try wp_auto
          generalize hst2 : op2.sendToClient' = st2 at *
          wp_if_join (fun v => iprop(⌜v = executeVal⌝ ∗ swift.facMap γ γc γm fcm ∗
              swift.slowMap γ γc γm scm ∗ s_ptr ↦ l2)) with [Hfcm Hscm s]
          · iframe
          · try wp_auto
            iunfold swift.facMap at Hfcm
            icases Hfcm with ⟨%FM, Hm, HM⟩
            wp_apply (wp_map_lookup2 (K := swift.CommandId) (V := swift.MFastAckClient)) $$ [$Hm] as Hm
            try wp_auto
            wp_if_join (fun v => iprop(⌜v = executeVal⌝ ∗ swift.facMap γ γc γm fcm ∗
                s_ptr ↦ l2)) with [Hm HM s]
            · try wp_auto
              cases hk : FM !! sa2.CmdId' with
              | none => simp [hk] at Hif
              | some c =>
                wp_apply (wp_mapDelete (K := swift.CommandId) (V := swift.MFastAckClient)) $$ [$Hm] as Hm
                iframe
                isplitr
                · ipureintro; rfl
                iunfold swift.facMap
                iexists _
                iframe Hm
                icases (BigSepM.bigSepM_delete (Φ := fun _ v => swift.facEntry γ γc γm v) hk).1 $$ HM
                  with ⟨-, HM⟩
                iexact HM
            · try wp_auto
              iframe
              iunfold swift.facMap
              iexists FM
              iframe
            iintro %v3 ⟨%Hv3, Hfcm, s⟩
            subst Hv3
            try wp_auto
            iunfold swift.slowMap at Hscm
            icases Hscm with ⟨%SM, Hsm, HSM⟩
            wp_apply (wp_mapInsert (K := swift.CommandId) (V := swift.MLightSlowAck)) $$ [$Hsm] as Hsm
            iframe
            isplitr
            · ipureintro; rfl
            iunfold swift.slowMap
            iexists _
            iframe Hsm
            iapply swift.bigSepM_overwrite
            iframe HSM
            unfold swift.slowEntry
            iexists s2
            iframe Hsok
            ipureintro; exact Hs2.1
          iintro %v2 ⟨%Hv2, Hfcm, Hscm, s⟩
          subst Hv2
          try wp_auto
          wp_bind (App (Val #fs) (Val #l2))
          iapply HfreeS
          inext
          try wp_auto
          wp_for_post
          have hiv1 : sint.Z (iv + W64 1) = sint.Z iv + 1 := by
            have := Hsl0.2; word
          iframe
          iexists (iv + W64 1), bv', sps ++ [(sa2, s2)]
          iframe
          isplitl [Hssl Hssr]
          · iunfold swift.slowSlots
            have hset : (sint.Z iv).toNat = (sps.map Prod.fst).length := by
              simp; omega
            rw [hset, swift.slots_set _ _ _ _ (by omega)]
            isimp only [List.map_append, List.map_cons, List.map_nil, List.length_append,
              List.length_cons, List.length_nil]
            isplitl [Hssl]
            · iExactEq Hssl; congr 2
            isplitl [Hssr]
            · iapply BigSepL.bigSepL_snoc.2
              iframe Hssr
              isplitr
              · ipureintro; exact Hw2
              isplitr
              · iexact Hacc2
              iexact Hnl2
            ipureintro
            intro p hp; simp at hp; rcases hp with hp | hp
            · exact Hssw p hp
            · subst hp; exact Hs2.1
          isplitl [Hopt]
          · iapply swift.optSt_mono _ _ _ _ _ _ _ _ _ (by simp; omega) $$ Hopt
          ipureintro
          rw [hiv1]
          have e4 := swift.snat_eq (iv + W64 1) (by omega)
          refine ⟨by omega, by omega, ?_, Hbv'⟩
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        · simp only [hlt2, decide_false]
          cleanup_bool_decide
          try simp only [Bool.false_eq_true, ↓reduceIte]
          try wp_auto
          -- the clients' fast-ack copies
          iunfold swift.facMap at Hfcm
          icases Hfcm with ⟨%FM, Hm, HM⟩
          ihave HM := swift.mapIter_start FM (swift.facEntry γ γc γm) [] $$ HM
          wp_func_lits
          wp_bind (App (App (Val (map.forRange _ _)) _) _)
          iapply (wp_map_for_range (fun keys i => iprop(
              (∃ c : swift.MFastAckClient, f_ptr ↦ c) ∗ ⌜0 ≤ i⌝ ∗
              [∗map] k ↦ v ∈ FM, iprop(⌜k ∉ keys.take i.toNat⌝ -∗ swift.facEntry γ γc γm v)))) $$ Hm
          iintro %keys %Hkeys
          isplitl [f HM]
          · isplitl [f]
            · iexists _; iexact f
            isplitr
            · ipureintro; omega
            iapply BigSepM.bigSepM_mono_of_forall $$ HM
            iintro %k %v H %h; iapply H; ipureintro; simp
          isplitl []
          · imodintro
            iintro %i %key %v %Hiv ⟨⟨%c0, f⟩, %Hi0, HM⟩
            ihave ⟨Hv, HM⟩ := swift.mapIter_step FM (swift.facEntry γ γc γm) keys i.toNat key v
              Hiv.1 Hiv.2 Hkeys.2.2 $$ HM
            wp_auto
            wp_method_call
            wp_call
            wp_auto
            iunfold swift.facEntry at Hv
            icases Hv with ⟨%cs, Hcsl, #Hvok, %Hvwf⟩
            wp_apply wp_sendc rr γ γc γm γw N me γs s v.CmdId'.ClientId'
              (interface.mkOk (go.GoType.PointerType swift.MFastAckClient.ty) #cf_ptr)
              (.fastAckClient v.Replica' v.Ballot' (swift.toCmdId v.CmdId') cs) csv.fastAckClientRPC'
              iprop(cf_ptr ↦ swift.MFastAckClient.mk v.Replica' v.Ballot' v.CmdId' v.Checksum' ∗
                v.Checksum' ↦* cs.map swift.handler.shashOf)
              $$ [$HisR $Hsbag cf Hcsl]
            · unfold replica.toSend
              isplitl
              · isplitr
                · iapply (hmf cf_ptr v.Replica' v.Ballot' v.CmdId' v.Checksum' cs Hvwf)
                isplitl [cf Hcsl]
                · iframe
                isplitr
                · iexact Hvok
                isplitr
                · unfold replica.freeOk; ileft; ipureintro; rfl
                ipureintro
                refine ⟨Hvwf, ?_⟩
                rw [Hpc.1.2.1]; rfl
              ipureintro
              simp [sp.Msg.isToClient, swift.toCmdId]
            unfold forMapPostcondition
            iright; ileft
            isplitr; · ipureintro; rfl
            isplitl [f]
            · iexists _; iexact f
            isplitr
            · ipureintro; omega
            have e : (i + 1).toNat = i.toNat + 1 := by omega
            rw [e]; iexact HM
          iintro ⟨⟨%c0, f⟩, -, -⟩ Hm
          try wp_auto
          -- the clients' slow-ack copies
          iunfold swift.slowMap at Hscm
          icases Hscm with ⟨%SM, Hsm, HSM⟩
          ihave HSM := swift.mapIter_start SM (swift.slowEntry γ γc γm) [] $$ HSM
          wp_func_lits
          wp_bind (App (App (Val (map.forRange _ _)) _) _)
          iapply (wp_map_for_range (fun keys i => iprop(
              (∃ c : swift.MLightSlowAck, s_ptr ↦ c) ∗ ⌜0 ≤ i⌝ ∗
              [∗map] k ↦ v ∈ SM, iprop(⌜k ∉ keys.take i.toNat⌝ -∗ swift.slowEntry γ γc γm v))))
            $$ Hsm
          iintro %keys2 %Hkeys2
          isplitl [s HSM]
          · isplitl [s]
            · iexists _; iexact s
            isplitr
            · ipureintro; omega
            iapply BigSepM.bigSepM_mono_of_forall $$ HSM
            iintro %k %v H %h; iapply H; ipureintro; simp
          isplitl []
          · imodintro
            iintro %i %key %v %Hiv ⟨⟨%c0, s⟩, %Hi0, HSM⟩
            ihave ⟨Hv, HSM⟩ := swift.mapIter_step SM (swift.slowEntry γ γc γm) keys2 i.toNat key v
              Hiv.1 Hiv.2 Hkeys2.2.2 $$ HSM
            wp_auto
            wp_method_call
            wp_call
            wp_auto
            iunfold swift.slowEntry at Hv
            icases Hv with ⟨%sv, %Hsv, #Hvok⟩
            wp_apply wp_sendc rr γ γc γm γw N me γs s v.CmdId'.ClientId'
              (interface.mkOk (go.GoType.PointerType swift.MLightSlowAck.ty) #cs_ptr)
              (.lightSlowAck sv) csv.lightSlowAckRPC' iprop(cs_ptr ↦ v)
              $$ [$HisR $Hsbag cs]
            · unfold replica.toSend
              isplitl
              · isplitr
                · iapply (hms cs_ptr v sv Hsv)
                isplitl [cs]
                · iframe
                isplitr
                · iexact Hvok
                isplitr
                · unfold replica.freeOk; ileft; ipureintro; rfl
                ipureintro
                refine ⟨trivial, ?_⟩
                rw [Hpc.1.2.2.2.1]; rfl
              ipureintro
              simp only [sp.Msg.isToClient]
              rw [← Hsv.2.2]; rfl
            unfold forMapPostcondition
            iright; ileft
            isplitr; · ipureintro; rfl
            isplitl [s]
            · iexists _; iexact s
            isplitr
            · ipureintro; omega
            have e : (i + 1).toNat = i.toNat + 1 := by omega
            rw [e]; iexact HSM
          iintro ⟨⟨%c0, s⟩, -, -⟩ Hsm
          try wp_auto
          wp_if_destruct
          · -- another ballot was seen: the `MAcks`
            try wp_auto
            wp_method_call
            wp_call
            wp_auto
            have hsps : sps.length = sint.nat sl0 := by
              have e2 := swift.snat_eq iv Hi2.1
              have e3 := swift.snat_eq sl0 Hsl0.1
              omega
            iunfold swift.fastSlots at Hfs
            icases Hfs with ⟨Hfsl, #Hfsr, %Hfsw⟩
            iunfold swift.slowSlots at Hss
            icases Hss with ⟨Hssl, #Hssr, %Hssw⟩
            isimp only [hfpsl, Nat.sub_self, List.replicate_zero, List.append_nil] at Hfsl
            isimp only [hsps, Nat.sub_self, List.replicate_zero, List.append_nil] at Hssl
            icases BigSepL.bigSepL_sep_eqv.1 $$ Hfsr with ⟨#Hfr1, #Hfr2⟩
            wp_apply wp_senda rr γ γc γm γw N me γs s
              (interface.mkOk (go.GoType.PointerType swift.MAcks.ty) #acksl)
              (.acks (fps.map Prod.snd) (sps.map Prod.snd)) csv.acksRPC'
              iprop(typedPointsto acksl (swift.MAcks.mk fsl ssl) DFrac.discard ∗
                fsl ↦* fps.map Prod.fst ∗ ssl ↦* sps.map Prod.fst ∗
                [∗list] p ∈ fps, swift.fastAckRepr p.1 p.2)
              $$ [$HisR $Hsbag Hfsl Hssl]
            · have h16 : sint.Z fl0 ≤ 16 := Int.le_trans Hfl0.2 (by decide)
              have h16' : sint.Z sl0 ≤ 16 := Int.le_trans Hsl0.2 (by decide)
              have e3 := swift.snat_eq fl0 Hfl0.1
              have e4 := swift.snat_eq sl0 Hsl0.1
              have hwf : sp.Msg.wf (.acks (fps.map Prod.snd) (sps.map Prod.snd)) := by
                refine ⟨⟨?_, ?_⟩, ?_⟩
                · simp; omega
                · intro f hf; simp at hf; obtain ⟨a, ha⟩ := hf; exact Hfsw _ ha
                · simp; omega
              unfold replica.toSend
              isplitl
              · isplitr
                · iapply (hma acksl fsl ssl fps sps hwf Hssw)
                isplitl [Hfsl Hssl]
                · iframe Hacks Hfsl Hssl Hfr1
                isplitr
                · simp only [sp.msgOk]
                  isplitl
                  · rw [BigSepL.bigSepL_map]; iexact Hfr2
                  rw [BigSepL.bigSepL_map]; iexact Hssr
                isplitr
                · unfold replica.freeOk; ileft; ipureintro; rfl
                ipureintro
                refine ⟨hwf, ?_⟩
                rw [Hpc.1.2.2.2.2.1]; rfl
              ipureintro; trivial
            wp_for_post
            unfold named
            isplitl [Hlc1]
            · iexact Hlc1
            iexact Hlc2
          · -- every ack had the first's ballot: the `MOptAcks`
            have hbv : bv = fa0.Ballot' := by
              rcases Hi2.2.2.2 with h | h
              · exact h
              · exact absurd h Hif
            try wp_auto
            wp_method_call
            wp_call
            wp_auto
            iunfold swift.optSt at Hopt
            icases Hopt with ⟨%asl1, %aps, %IM, Ho, Ha, Hac, #Hr, Hm', %Hp, #Hnl⟩
            icases BigSepL.bigSepL_sep_eqv.1 $$ Hr with ⟨#Hr1, #Hr2⟩
            ihave #Hok0 := Hok
            iunfold sp.fastAckOk at Hok0
            icases Hok0 with ⟨%Hw0, -⟩
            have hwf : sp.Msg.wf (.optAcks me fa0.Ballot' (aps.map Prod.snd)) := by
              refine ⟨?_, ?_⟩
              · have h16 : sint.Z fl0 ≤ 16 := Int.le_trans Hfl0.2 (by decide)
                have h16' : sint.Z sl0 ≤ 16 := Int.le_trans Hsl0.2 (by decide)
                have e3 := swift.snat_eq fl0 Hfl0.1
                have e4 := swift.snat_eq sl0 Hsl0.1
                have e2 := swift.snat_eq iv Hi2.1
                have := Hp.2.1
                simp; omega
              · intro a ha; simp at ha; obtain ⟨x, hx⟩ := ha; exact Hp.1 _ hx
            wp_apply wp_senda rr γ γc γm γw N me γs s
              (interface.mkOk (go.GoType.PointerType swift.MOptAcks.ty) #«$r0_ptr»)
              (.optAcks me fa0.Ballot' (aps.map Prod.snd)) csv.optAcksRPC'
              iprop(«$r0_ptr» ↦ swift.MOptAcks.mk me fa0.Ballot' asl1 ∗
                asl1 ↦* aps.map Prod.fst ∗ [∗list] p ∈ aps, swift.ackRepr p.1 p.2)
              $$ [$HisR $Hsbag Ho Ha]
            · unfold replica.toSend
              isplitl
              · isplitr
                · iapply (hmo «$r0_ptr» me fa0.Ballot' asl1 aps hwf)
                isplitl [Ho Ha]
                · iframe Ho Ha Hr1
                isplitr
                · simp only [sp.msgOk]
                  isplitr
                  · ipureintro
                    refine ⟨Hpc.2.1, ?_⟩
                    rw [Hfr.2.1]; exact Hw0.2
                  isplitr
                  · rw [BigSepL.bigSepL_map]; iexact Hr2
                  iapply swift.optNL_msg; iexact Hnl
                isplitr
                · unfold replica.freeOk; ileft; ipureintro; rfl
                ipureintro
                refine ⟨hwf, ?_⟩
                rw [Hpc.1.2.2.2.2.2.1]; rfl
              ipureintro; trivial
            wp_for_post
            unfold named
            isplitl [Hlc1]
            · iexact Hlc1
            iexact Hlc2
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- a slow ack first
      iapply swift.bag_clauseT $$ Hlc1 Hlc2 Hbs
      inext
      iintro %op Hop
      wp_auto_lc 2
      iunfold swift.batchSlowP at Hop
      icases Hop with ⟨%N, %me, %l, %sa0, %s0, #Hctx, %Hmsg, #Hl, %Hs0, #Hsok0⟩
      ihave #Hlc := Hl
      iStructNamedPrefix Hlc "SA"
      ihave #Hat := swift.sendCtxN_at γ γc γm rp rr N me $$ [$HReplica $Hctx]
      ihave #Hat2 := Hat
      iunfold swift.sendCtxAt at Hat2
      icases Hat2 with ⟨%s, %γw, %γs, %csv, #HId, #HN, #HisR, #Hsnd, #Hsbag, #Hcs, %Hpc⟩
      ihave #Hcs2 := Hcs
      iStructNamedPrefix Hcs2 "CS"
      ihave #Hsok02 := Hsok0
      isimp only [sp.msgOk] at Hsok02
      icases Hsok02 with ⟨%Hw0, #Hacc0, #Hnl0⟩
      rw [Hmsg]
      wp_auto
      wp_func_call
      wp_call
      wp_apply (wp_Len (V := swift.BatcherOp) (t := swift.BatcherOp.ty) fa γ1) $$ [$Hfa] as %fl0 %Hfl0
      wp_func_call
      wp_call
      wp_apply (wp_Len (V := swift.BatcherOp) (t := swift.BatcherOp.ty) ls γ2) $$ [$Hls] as %sl0 %Hsl0
      rw [Hfacap] at Hfl0
      rw [Hlscap] at Hsl0
      wp_apply (wp_slice_make2 (V := swift.MFastAck) fl0) as %fsl ⟨Hfsl, Hfslc⟩
      · ipureintro; word
      wp_apply (wp_slice_make2 (V := swift.MLightSlowAck) (sl0 + W64 1)) as %ssl ⟨Hssl, Hsslc⟩
      · ipureintro; word
      try wp_auto
      irename «$r0» => Hacks
      generalize hacksl : «$r0_ptr» = acksl at *
      wp_apply swift.NilDepOfCmdId.wp sa0.CmdId' as %dsl0 Hdsl0
      ipersist Hdsl0
      try wp_auto
      wp_apply wp_slice_literal (V := swift.SHash) []
      isplitr
      · ipureintro; rfl
      iintro %csl0 ⟨Hcsl0, -⟩
      ipersist Hcsl0
      try wp_auto
      wp_apply wp_slice_literal (V := swift.Ack) _
      isplitr
      · ipureintro; rfl
      iintro %asl ⟨Hasl, Haslc⟩
      try wp_auto
      irename «$r0» => Hopt
      wp_apply (wp_map_make1 (K := swift.CommandId) (V := w64)) as %ism Hism
      wp_apply (wp_mapInsert (K := swift.CommandId) (V := w64)) $$ [$Hism] as Hism
      wp_apply (wp_map_make1 (K := swift.CommandId) (V := swift.MFastAckClient)) as %fcm Hfcm
      wp_apply (wp_map_make1 (K := swift.CommandId) (V := swift.MLightSlowAck)) as %scm Hscm
      try wp_auto
      ihave Hscm : swift.slowMap γ γc γm scm $$ [Hscm]
      · iunfold swift.slowMap; iexists ∅; iframe; iapply BigSepM.bigSepM_empty.2; itrivial
      generalize hst : op.sendToClient' = st at *
      wp_if_join (fun v => iprop(⌜v = executeVal⌝ ∗ swift.slowMap γ γc γm scm ∗
          slowAck_ptr ↦ l ∗ slowAckClientMsgs_ptr ↦ scm))
        with [Hscm slowAck slowAckClientMsgs]
      · iframe
      · try wp_auto
        iunfold swift.slowMap at Hscm
        icases Hscm with ⟨%SM, Hsm, HSM⟩
        wp_apply (wp_mapInsert (K := swift.CommandId) (V := swift.MLightSlowAck)) $$ [$Hsm] as Hsm
        iframe
        isplitr
        · ipureintro; rfl
        iunfold swift.slowMap
        iexists _
        iframe Hsm
        iapply swift.bigSepM_overwrite
        iframe HSM
        unfold swift.slowEntry
        iexists s0
        iframe Hsok0
        ipureintro; exact Hs0.1
      iintro %v0 ⟨%Hv0, Hscm, slowAck, slowAckClientMsgs⟩
      subst Hv0
      try wp_auto
      have hsl1 : sint.Z (sl0 + W64 1) = sint.Z sl0 + 1 := by have := Hsl0.2; word
      ihave %Hsll := ownSlice_len _ _ _ $$ Hssl
      simp only [List.length_replicate] at Hsll
      have hb0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z ssl.len := by
        constructor
        · decide
        · have := Hsll.1; have := Hsl0.1; word
      isimp only [hb0, ↓reduceIte]
      wp_apply (wp_store_slice_index (V := swift.MLightSlowAck) ssl (sint.Z (W64 0)) _ sa0)
        $$ [$Hssl] as Hssl
      · ipureintro
        refine ⟨by decide, ?_⟩
        rw [List.length_replicate, Hsll.1]
        have h := hb0.2
        have e : (sint.nat ssl.len : Int) = sint.Z ssl.len := swift.snat_eq _ (by omega)
        rw [e]; exact h
      try wp_auto
      wp_bind (App (Val #fs) (Val #l))
      iapply HfreeS
      inext
      try wp_auto
      ipersist acks
      ipersist optAcks
      ipersist is
      ipersist fastAckClientMsgs
      ipersist slowAckClientMsgs
      ipersist fLen
      ipersist sLen
      ipersist Hacks
      ihave #Hacks2 := Hacks
      iStructNamedPrefix Hacks2 "MA"
      ihave Hopt' : swift.optSt γ γc γm me sa0.Ballot' «$r0_ptr» ism 1 $$ [Hopt Hasl Haslc Hism]
      · iunfold swift.optSt
        iexists _, [(swift.Ack.mk sa0.CmdId' dsl0 (slice.mk csl0
            (W64 (go.arrayLiteralSize [])) (W64 (go.arrayLiteralSize []))) 0,
          (⟨s0.id, [s0.id], [], 0⟩ : sp.Ack))], _
        isimp only [List.map_cons, List.map_nil]
        iframe Hopt Hasl Haslc Hism
        isplitl
        · iapply BigSepL.bigSepL_singleton.2
          isplitl
          · unfold swift.ackRepr
            isplitr
            · ipureintro; exact ⟨Hs0.1.2.2, rfl⟩
            isplitr
            · iExactEq Hdsl0
              rw [← Hs0.1.2.2]; rfl
            iExactEq Hcsl0; rfl
          unfold sp.ackOk
          simp only [↓reduceIte]
          have e1 : sp.bal sa0.Ballot' = sp.bal s0.bal := by rw [Hs0.1.2.1]
          rw [e1, ← Hs0.2]
          iexact Hacc0
        isplitr
        rotate_left
        · iapply swift.optNL_of_slow γc γm me sa0.Ballot' _ s0 Hs0.2 (by rw [← Hs0.1.2.1]); iexact Hnl0
        ipureintro
        refine ⟨?_, by simp, ?_⟩
        · intro p hp; simp at hp; subst hp
          exact ⟨by unfold sp.depWf; simp, by unfold sp.hashesWf; simp⟩
        · intro k j hk
          by_cases e : k = sa0.CmdId'
          · subst e; simp at hk; subst hk; exact ⟨by decide, _, rfl, rfl⟩
          · simp at hk; exact absurd hk.1.symm e
      have hn1 : sint.nat (sl0 + W64 1) = sint.nat sl0 + 1 := by
        have := Hsl0.1; show (sint.Z _).toNat = (sint.Z _).toNat + 1; rw [hsl1]; omega
      ihave Hss : swift.slowSlots γ γc γm ssl (sint.nat sl0 + 1) [(sa0, s0)] $$ [Hssl]
      · iunfold swift.slowSlots
        have e := swift.slots_set ([] : List swift.MLightSlowAck) (sint.nat sl0 + 1)
          (zero_val swift.MLightSlowAck) sa0 (by omega)
        simp only [List.length_nil, List.nil_append] at e
        rw [hn1, e]
        isimp only [List.map_cons, List.map_nil, List.length_cons, List.length_nil]
        isplitl [Hssl]
        · iExactEq Hssl; congr 2
        isplitl
        · iapply BigSepL.bigSepL_singleton.2
          isplitr
          · ipureintro; exact Hw0
          isplitr
          · iexact Hacc0
          iexact Hnl0
        ipureintro
        intro p hp; simp at hp; subst hp; exact Hs0.1
      ihave HL : (∃ (iv : w64) (bv : w32) (sps : List (swift.MLightSlowAck × sp.SlowAck)),
          "i" ∷ i_ptr ↦ iv ∗ "ballot" ∷ ballot_ptr ↦ bv ∗
          "Hss" ∷ swift.slowSlots γ γc γm ssl (sint.nat sl0 + 1) sps ∗
          "Hopt" ∷ swift.optSt γ γc γm me sa0.Ballot' «$r0_ptr» ism sps.length ∗
          "Hscm" ∷ swift.slowMap γ γc γm scm ∗
          "%Hi" ∷ ⌜1 ≤ sint.Z iv ∧ sint.Z iv ≤ sint.Z sl0 + 1 ∧ sps.length = sint.nat iv ∧
            (bv = sa0.Ballot' ∨ bv = W32 (-1))⌝ : IProp netDistGF) $$ [i ballot Hss Hopt' Hscm]
      · iexists (W64 1), sa0.Ballot', [(sa0, s0)]
        iframe
        ipureintro
        refine ⟨by decide, by have := Hsl0.1; simp; omega, by rfl, Or.inl rfl⟩
      wp_for HL
      by_cases hlt : sint.Z iv < sint.Z (sl0 + W64 1)
      · simp only [hlt, _root_.decide_true]
        cleanup_bool_decide
        wp_auto
        wp_apply (wp_bag_receive (t := swift.BatcherOp.ty) γ2 ls (swift.batchSlowP γ γc γm rp))
          $$ [$Hbs] as %op2 Hop2
        iunfold swift.batchSlowP at Hop2
        icases Hop2 with ⟨%N2, %me2, %l2, %sa2, %s2, #Hctx2, %Hmsg2, #Hl2, %Hs2, #Hsok⟩
        ihave #Hl2c := Hl2
        iStructNamedPrefix Hl2c "SB"
        ihave #Hat2 := swift.sendCtxN_at γ γc γm rp rr N2 me2 $$ [$HReplica $Hctx2]
        ihave %Hag2 := swift.sendCtxAt_agree γ γc γm rp rr N N2 me me2 $$ [$Hat $Hat2]
        obtain ⟨rfl, rfl⟩ := Hag2
        ihave #Hsok2 := Hsok
        isimp only [sp.msgOk] at Hsok2
        icases Hsok2 with ⟨%Hw2, #Hacc2, #Hnl2⟩
        try wp_auto
        rw [Hmsg2]
        try wp_auto
        iunfold swift.slowSlots at Hss
        icases Hss with ⟨Hssl, Hssr, %Hssw⟩
        ihave %Hsl' := ownSlice_len _ _ _ $$ Hssl
        rw [List.length_append, List.length_map, List.length_replicate] at Hsl'
        have e2 := swift.snat_eq iv (by omega)
        have e3 := swift.snat_eq sl0 Hsl0.1
        rw [hsl1] at hlt
        have hsps : (sps.length : Int) ≤ sint.nat sl0 + 1 := by omega
        have hlen2 : sint.Z ssl.len = sint.Z sl0 + 1 := by
          have e1 := swift.snat_eq ssl.len Hsl'.2
          have h1 := Hsl'.1
          omega
        have hi2 : 0 ≤ sint.Z iv ∧ sint.Z iv < sint.Z ssl.len := by omega
        try isimp only [hi2, _root_.and_self, ↓reduceIte]
        wp_apply (wp_store_slice_index (V := swift.MLightSlowAck) ssl (sint.Z iv) _ sa2)
          $$ [$Hssl] as Hssl
        · ipureintro; refine ⟨hi2.1, ?_⟩
          rw [List.length_append, List.length_map, List.length_replicate]
          omega
        try wp_auto
        have hwire2 : 0 ≤ sint.Z sa2.Ballot' := by rw [Hs2.1.2.1]; exact Hw2.2
        wp_if_join (fun v => iprop(⌜v = executeVal⌝ ∗ ∃ bv' : w32, ballot_ptr ↦ bv' ∗
            swift.optSt γ γc γm me sa0.Ballot' «$r0_ptr» ism (sps.length + 1) ∗
            ⌜bv' = sa0.Ballot' ∨ bv' = W32 (-1)⌝ ∗ s_ptr ↦ l2))
          with [ballot Hopt s]
        · -- the first ack's ballot: a new entry
          have hb02 : sa2.Ballot' = sa0.Ballot' := by
            rcases Hi.2.2.2 with h | h
            · exact h
            · exfalso; rw [h] at hwire2; exact absurd hwire2 (by decide)
          iunfold swift.optSt at Hopt
          icases Hopt with ⟨%asl1, %aps, %IM, Ho, Ha, Hac, Hr, Hm, %Hp, #Hnl⟩
          try wp_auto
          ihave %Hal := ownSlice_len _ _ _ $$ Ha
          wp_apply (wp_mapInsert (K := swift.CommandId) (V := w64)) $$ [$Hm] as Hm
          try wp_auto
          wp_apply swift.NilDepOfCmdId.wp sa2.CmdId' as %dsl Hdsl
          ipersist Hdsl
          try wp_auto
          wp_apply wp_slice_literal (V := swift.SHash) []
          isplitr
          · ipureintro; rfl
          iintro %csl ⟨Hcsl, -⟩
          ipersist Hcsl
          try wp_auto
          wp_apply wp_slice_literal (V := swift.Ack) _
          isplitr
          · ipureintro; rfl
          iintro %sl1 ⟨Hsl1, -⟩
          try wp_auto
          wp_apply (wp_slice_append (V := swift.Ack)) $$ [$Ha $Hac $Hsl1] as %asl2 ⟨Ha, Hac, -⟩
          try wp_auto
          iframe
          isplitr
          · ipureintro; rfl
          isplitl [Ho Ha Hac Hr Hm]
          · iunfold swift.optSt
            iexists asl2, aps ++ [(swift.Ack.mk sa2.CmdId' dsl (slice.mk csl
                (W64 (go.arrayLiteralSize [])) (W64 (go.arrayLiteralSize []))) 0,
               (⟨s2.id, [s2.id], [], 0⟩ : sp.Ack))], _
            isimp only [List.map_append, List.map_cons, List.map_nil]
            iframe Ho Ha Hac Hm
            isplitl [Hr]
            · iapply BigSepL.bigSepL_snoc.2
              iframe Hr
              isplitl
              · unfold swift.ackRepr
                isplitr
                · ipureintro; exact ⟨Hs2.1.2.2, rfl⟩
                isplitr
                · iExactEq Hdsl
                  rw [← Hs2.1.2.2]; rfl
                iExactEq Hcsl; rfl
              unfold sp.ackOk
              simp only [↓reduceIte]
              have e1 : sp.bal sa0.Ballot' = sp.bal s2.bal := by rw [← hb02, Hs2.1.2.1]
              rw [e1, ← Hs2.2]
              iexact Hacc2
            isplitr
            rotate_left
            · iapply swift.optNL_of_slow γc γm me sa0.Ballot' _ s2 Hs2.2 (by rw [← Hs2.1.2.1, hb02]); iexact Hnl2
            ipureintro
            refine ⟨?_, ?_, ?_⟩
            · intro q hq; simp at hq; rcases hq with hq | hq
              · exact Hp.1 q hq
              · subst hq; exact ⟨by unfold sp.depWf; simp, by unfold sp.hashesWf; simp⟩
            · have := Hp.2.1; simp; omega
            · intro k j hk
              have hlen : sint.nat asl1.len = aps.length := by simpa using Hal.1.symm
              by_cases e : k = sa2.CmdId'
              · subst e; simp at hk; subst hk
                refine ⟨Hal.2, (swift.Ack.mk sa2.CmdId' dsl (slice.mk csl
                  (W64 (go.arrayLiteralSize [])) (W64 (go.arrayLiteralSize []))) 0,
                  (⟨s2.id, [s2.id], [], 0⟩ : sp.Ack)), ?_, rfl⟩
                rw [hlen]; simp
              · have hk' : IM !! k = some j := by
                  have e' : ¬ sa2.CmdId' = k := fun h => e h.symm
                  simpa [e'] using hk
                obtain ⟨hj0, q, hq1, hq2⟩ := Hp.2.2 k j hk'
                refine ⟨hj0, q, ?_, hq2⟩
                rw [List.getElem?_append_left]; exact hq1
                exact (List.getElem?_eq_some_iff.mp hq1).1
          ipureintro; left; exact hb02
        · ihave Hopt := swift.optSt_mono γ γc γm me sa0.Ballot' «$r0_ptr» ism sps.length
              (sps.length + 1) (by omega) $$ Hopt
          try wp_auto
          iframe
          ipureintro; right; rfl
        iintro %v1 ⟨%Hv1, %bv', ballot, Hopt, %Hbv', s⟩
        subst Hv1
        try wp_auto
        generalize hst2 : op2.sendToClient' = st2 at *
        wp_if_join (fun v => iprop(⌜v = executeVal⌝ ∗ swift.slowMap γ γc γm scm ∗
            s_ptr ↦ l2)) with [Hscm s]
        · iframe
        · try wp_auto
          iunfold swift.slowMap at Hscm
          icases Hscm with ⟨%SM, Hsm, HSM⟩
          wp_apply (wp_mapInsert (K := swift.CommandId) (V := swift.MLightSlowAck)) $$ [$Hsm] as Hsm
          iframe
          isplitr
          · ipureintro; rfl
          iunfold swift.slowMap
          iexists _
          iframe Hsm
          iapply swift.bigSepM_overwrite
          iframe HSM
          unfold swift.slowEntry
          iexists s2
          iframe Hsok
          ipureintro; exact Hs2.1
        iintro %v2 ⟨%Hv2, Hscm, s⟩
        subst Hv2
        try wp_auto
        wp_bind (App (Val #fs) (Val #l2))
        iapply HfreeS
        inext
        try wp_auto
        wp_for_post
        have hiv1 : sint.Z (iv + W64 1) = sint.Z iv + 1 := by
          have := Hsl0.2; word
        iframe
        iexists (iv + W64 1), bv', sps ++ [(sa2, s2)]
        iframe
        isplitl [Hssl Hssr]
        · iunfold swift.slowSlots
          have hset : (sint.Z iv).toNat = (sps.map Prod.fst).length := by
            simp; omega
          rw [hset, swift.slots_set _ _ _ _ (by omega)]
          isimp only [List.map_append, List.map_cons, List.map_nil, List.length_append,
            List.length_cons, List.length_nil]
          isplitl [Hssl]
          · iExactEq Hssl; congr 2
          isplitl [Hssr]
          · iapply BigSepL.bigSepL_snoc.2
            iframe Hssr
            isplitr
            · ipureintro; exact Hw2
            isplitr
            · iexact Hacc2
            iexact Hnl2
          ipureintro
          intro p hp; simp at hp; rcases hp with hp | hp
          · exact Hssw p hp
          · subst hp; exact Hs2.1
        isplitl [Hopt]
        · iapply swift.optSt_mono _ _ _ _ _ _ _ _ _ (by simp) $$ Hopt
        ipureintro
        rw [hiv1]
        have e4 := swift.snat_eq (iv + W64 1) (by omega)
        refine ⟨by omega, by omega, ?_, Hbv'⟩
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      · simp only [hlt, decide_false]
        cleanup_bool_decide
        try simp only [Bool.false_eq_true, ↓reduceIte]
        try wp_auto
        have hspsl : sps.length = sint.nat sl0 + 1 := by
          have e2 := swift.snat_eq iv (by omega)
          have e3 := swift.snat_eq sl0 Hsl0.1
          rw [hsl1] at hlt; omega
        ihave HL2 : (∃ (iv : w64) (bv : w32) (fps : List (swift.MFastAck × sp.FastAck)),
            "i" ∷ i_ptr ↦ iv ∗ "ballot" ∷ ballot_ptr ↦ bv ∗
            "Hfs" ∷ swift.fastSlots γ fsl (sint.nat fl0) fps ∗
            "Hopt" ∷ swift.optSt γ γc γm me sa0.Ballot' «$r0_ptr» ism (sps.length + fps.length) ∗
            "Hfcm" ∷ swift.facMap γ γc γm fcm ∗
            "%Hi2" ∷ ⌜0 ≤ sint.Z iv ∧ sint.Z iv ≤ sint.Z fl0 ∧ fps.length = sint.nat iv ∧
              (bv = sa0.Ballot' ∨ bv = W32 (-1))⌝ : IProp netDistGF)
            $$ [i ballot Hfsl Hopt Hfcm]
        · iexists (W64 0), bv, []
          iframe
          isplitl [Hfsl]
          · iunfold swift.fastSlots
            isimp only [List.map_nil, List.nil_append, List.length_nil, Nat.sub_zero]
            isplitl [Hfsl]
            · iexact Hfsl
            isplitl
            · iapply BigSepL.bigSepL_nil.2; itrivial
            ipureintro; intro p hp; simp at hp
          isplitl [Hfcm]
          · iunfold swift.facMap; iexists ∅; iframe; iapply BigSepM.bigSepM_empty.2; itrivial
          ipureintro
          refine ⟨by decide, by have := Hfl0.1; simpa using this, by simp; rfl, Hi.2.2.2⟩
        wp_for HL2
        by_cases hlt2 : sint.Z iv < sint.Z fl0
        · simp only [hlt2, _root_.decide_true]
          cleanup_bool_decide
          try simp only [↓reduceIte, ite_true]
          wp_auto
          wp_apply (wp_bag_receive (t := swift.BatcherOp.ty) γ1 fa (swift.batchFastP γ γc γm rp))
            $$ [$Hbf] as %op1 Hop1
          iunfold swift.batchFastP at Hop1
          icases Hop1 with ⟨%N1, %me1, %l1, %fa1, %f1, #Hctx1, %Hmsg1, Hl1, #Hrep1, #Hok1, %Hf1, Hcl1⟩
          ihave #Hat1 := swift.sendCtxN_at γ γc γm rp rr N1 me1 $$ [$HReplica $Hctx1]
          ihave %Hag := swift.sendCtxAt_agree γ γc γm rp rr N N1 me me1 $$ [$Hat $Hat1]
          obtain ⟨rfl, rfl⟩ := Hag
          ihave #Hrep12 := Hrep1
          iunfold swift.fastAckRepr at Hrep12
          icases Hrep12 with ⟨%Hfr1, #Hdep1, #Hcs1⟩
          try wp_auto
          rw [Hmsg1]
          try wp_auto
          iunfold swift.fastSlots at Hfs
          icases Hfs with ⟨Hfsl, Hfsr, %Hfsw⟩
          ihave %Hfl' := ownSlice_len _ _ _ $$ Hfsl
          rw [List.length_append, List.length_map, List.length_replicate] at Hfl'
          have e2 := swift.snat_eq iv Hi2.1
          have e3 := swift.snat_eq fl0 Hfl0.1
          have hfps : (fps.length : Int) ≤ sint.nat fl0 := by omega
          have hlen : sint.Z fsl.len = sint.Z fl0 := by
            have e1 := swift.snat_eq fsl.len Hfl'.2
            have h1 := Hfl'.1
            omega
          have hi0 : 0 ≤ sint.Z iv ∧ sint.Z iv < sint.Z fsl.len := by omega
          try isimp only [hi0, _root_.and_self, ↓reduceIte]
          wp_apply (wp_store_slice_index (V := swift.MFastAck) fsl (sint.Z iv) _ fa1) $$ [$Hfsl] as Hfsl
          · ipureintro; refine ⟨hi0.1, ?_⟩
            rw [List.length_append, List.length_map, List.length_replicate]
            omega
          try wp_auto
          ihave #Hok12 := Hok1
          iunfold sp.fastAckOk at Hok12
          icases Hok12 with ⟨%Hw1, -⟩
          have hwire1 : 0 ≤ sint.Z fa1.Ballot' := by
            rw [Hfr1.2.1]; exact Hw1.2
          wp_if_join (fun v => iprop(⌜v = executeVal⌝ ∗ ∃ bv' : w32, ballot_ptr ↦ bv' ∗
              swift.optSt γ γc γm me sa0.Ballot' «$r0_ptr» ism (sps.length + fps.length + 1) ∗
              ⌜bv' = sa0.Ballot' ∨ bv' = W32 (-1)⌝ ∗ f_ptr ↦ l1 ∗ l1 ↦ fa1))
            with [ballot Hopt f Hl1]
          · -- the first ack's ballot: a new entry unless the command has one
            have hb01 : fa1.Ballot' = sa0.Ballot' := by
              rcases Hi2.2.2.2 with h | h
              · exact h
              · exfalso; rw [h] at hwire1; exact absurd hwire1 (by decide)
            iunfold swift.optSt at Hopt
            icases Hopt with ⟨%asl1, %aps, %IM, Ho, Ha, Hac, Hr, Hm, %Hp, #Hnl⟩
            try wp_auto
            wp_apply (wp_map_lookup2 (K := swift.CommandId) (V := w64)) $$ [$Hm] as Hm
            try wp_auto
            cases hk : IM !! fa1.CmdId' with
            | some j =>
              simp only [Option.isSome_some, _root_.decide_true]
              try wp_auto
              iframe
              isplitr
              · ipureintro; rfl
              isplitl [Ho Ha Hac Hr Hm]
              · iunfold swift.optSt
                iexists asl1, aps, IM
                iframe
                isplitr
                · ipureintro
                  exact ⟨Hp.1, by have := Hp.2.1; omega, Hp.2.2⟩
                iexact Hnl
              ipureintro; left; exact hb01
            | none =>
              simp only [Option.isSome_none, decide_false]
              try wp_auto
              ihave %Hal := ownSlice_len _ _ _ $$ Ha
              wp_apply (wp_mapInsert (K := swift.CommandId) (V := w64)) $$ [$Hm] as Hm
              try wp_auto
              wp_apply wp_slice_literal (V := swift.Ack) _
              isplitr
              · ipureintro; rfl
              iintro %sl1 ⟨Hsl1, -⟩
              try wp_auto
              wp_apply (wp_slice_append (V := swift.Ack)) $$ [$Ha $Hac $Hsl1] as %asl2 ⟨Ha, Hac, -⟩
              try wp_auto
              iframe
              isplitr
              · ipureintro; rfl
              isplitl [Ho Ha Hac Hr Hm]
              · iunfold swift.optSt
                iexists asl2, aps ++ [(swift.Ack.mk fa1.CmdId' fa1.Dep' fa1.Checksum' fa1.Seqnum',
                  swift.ackOfFast f1)], _
                isimp only [List.map_append, List.map_cons, List.map_nil]
                iframe Ho Ha Hac Hm
                isplitl [Hr]
                · iapply BigSepL.bigSepL_snoc.2
                  iframe Hr
                  isplitl
                  · iapply swift.ackRepr_of_fast; iexact Hrep1
                  have e1 : sp.bal sa0.Ballot' = sp.bal f1.bal := by rw [← hb01, Hfr1.2.1]
                  rw [e1, ← Hf1.1]
                  iapply swift.ackOk_of_fast γ f1 Hf1.2.2.1; iexact Hok1
                isplitr
                rotate_left
                · iapply swift.optNL_snoc _ _ _ _ _ _ Hf1.2.2.1; iexact Hnl
                ipureintro
                refine ⟨?_, ?_, ?_⟩
                · intro p hp; simp at hp; rcases hp with hp | hp
                  · exact Hp.1 p hp
                  · subst hp; exact Hf1.2.1
                · have := Hp.2.1; simp; omega
                · intro k j hk'
                  have hlen : sint.nat asl1.len = aps.length := by simpa using Hal.1.symm
                  by_cases e : k = fa1.CmdId'
                  · subst e; simp at hk'; subst hk'
                    refine ⟨Hal.2, (swift.Ack.mk fa1.CmdId' fa1.Dep' fa1.Checksum' fa1.Seqnum',
                      swift.ackOfFast f1), ?_, rfl⟩
                    rw [hlen]; simp
                  · have hk'' : IM !! k = some j := by
                      have e' : ¬ fa1.CmdId' = k := fun h => e h.symm
                      simpa [e'] using hk'
                    obtain ⟨hj0, p, hp1, hp2⟩ := Hp.2.2 k j hk''
                    refine ⟨hj0, p, ?_, hp2⟩
                    rw [List.getElem?_append_left]; exact hp1
                    exact (List.getElem?_eq_some_iff.mp hp1).1
              ipureintro; left; exact hb01
          · ihave Hopt := swift.optSt_mono γ γc γm me sa0.Ballot' «$r0_ptr» ism (sps.length + fps.length)
                (sps.length + fps.length + 1) (by omega) $$ Hopt
            try wp_auto
            iframe
            ipureintro; right; rfl
          iintro %v1 ⟨%Hv1, %bv', ballot, Hopt, %Hbv', f, Hl1⟩
          subst Hv1
          try wp_auto
          generalize hst1 : op1.sendToClient' = st1 at *
          wp_if_join (fun v => iprop(⌜v = executeVal⌝ ∗ swift.facMap γ γc γm fcm ∗
              swift.slowMap γ γc γm scm ∗ f_ptr ↦ l1 ∗ l1 ↦ fa1)) with [Hfcm Hscm Hcl1 f Hl1]
          · iframe
          · try wp_auto
            ihave #Hcl2 : swift.facClientOk γ γc γm f1 $$ [Hcl1]
            · iexact Hcl1
            iunfold swift.slowMap at Hscm
            icases Hscm with ⟨%SM, Hsm, HSM⟩
            wp_apply (wp_map_lookup2 (K := swift.CommandId) (V := swift.MLightSlowAck)) $$ [$Hsm] as Hsm
            try wp_auto
            cases hk : SM !! fa1.CmdId' with
            | some c =>
              simp only [Option.isSome_some, _root_.decide_true]
              try wp_auto
              iframe
              isplitr
              · ipureintro; rfl
              iunfold swift.slowMap
              iexists SM
              iframe
            | none =>
              simp only [Option.isSome_none, decide_false]
              try wp_auto
              wp_apply wp_cc fa1.Checksum' fa1.Dep' f1.cs (f1.dep.map swift.ofCmdId) DFrac.discard
                DFrac.discard $$ [$Hcs1 $Hdep1] as %csl ⟨-, -, %d, Hcsl, #Hdh, %Hd⟩
              · ipureintro; exact ⟨Hf1.2.1.2, Hf1.2.2.2, by simp; exact Hf1.2.1.1⟩
              try wp_auto
              iunfold swift.facMap at Hfcm
              icases Hfcm with ⟨%FM, Hm, HM⟩
              wp_apply (wp_mapInsert (K := swift.CommandId) (V := swift.MFastAckClient)) $$ [$Hm] as Hm
              iframe
              isplitr
              · ipureintro; rfl
              isplitl [Hm HM Hcsl]
              · iunfold swift.facMap
                iexists _
                iframe Hm
                iapply swift.bigSepM_overwrite
                iframe HM
                isimp only [swift.map_to_of] at Hdh
                unfold swift.facEntry
                iexists (f1.cs ++ [d])
                iframe Hcsl
                obtain ⟨hr, hb, hx, -⟩ := Hfr1
                simp only [hr, hb, hx]
                isplitr
                · iapply swift.facOk_of
                  iframe Hok1 Hdh Hcl2
                ipureintro
                refine ⟨by simp; have := Hf1.2.1.2.1; omega, ?_⟩
                intro h hh; simp at hh; rcases hh with hh | hh
                · exact Hf1.2.1.2.2 h hh
                · subst hh; exact Hd
              iunfold swift.slowMap
              iexists SM
              iframe
          iintro %v2 ⟨%Hv2, Hfcm, Hscm, f, Hl1⟩
          subst Hv2
          try wp_auto
          wp_apply wp_rel $$ [Hl1]
          · iframe Hupv; iexists fa1; iexact Hl1
          wp_for_post
          have hiv1 : sint.Z (iv + W64 1) = sint.Z iv + 1 := by
            have := Hfl0.2; word
          iframe
          iexists (iv + W64 1), bv', fps ++ [(fa1, f1)]
          iframe
          isplitl [Hfsl Hfsr]
          · iunfold swift.fastSlots
            have hset : (sint.Z iv).toNat = (fps.map Prod.fst).length := by
              simp; omega
            rw [hset, swift.slots_set _ _ _ _ (by omega)]
            isimp only [List.map_append, List.map_cons, List.map_nil, List.length_append,
              List.length_cons, List.length_nil]
            isplitl [Hfsl]
            · iExactEq Hfsl; congr 2
            isplitl [Hfsr]
            · iapply BigSepL.bigSepL_snoc.2
              iframe Hfsr Hrep1 Hok1
            ipureintro
            intro p hp; simp at hp; rcases hp with hp | hp
            · exact Hfsw p hp
            · subst hp; exact Hf1.2.1
          isplitl [Hopt]
          · iapply swift.optSt_mono _ _ _ _ _ _ _ _ _ (by simp; omega) $$ Hopt
          ipureintro
          rw [hiv1]
          have e4 := swift.snat_eq (iv + W64 1) (by omega)
          refine ⟨by omega, by omega, ?_, Hbv'⟩
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        · simp only [hlt2, decide_false]
          cleanup_bool_decide
          try simp only [Bool.false_eq_true, ↓reduceIte]
          try wp_auto
          -- the clients' fast-ack copies
          iunfold swift.facMap at Hfcm
          icases Hfcm with ⟨%FM, Hm, HM⟩
          ihave HM := swift.mapIter_start FM (swift.facEntry γ γc γm) [] $$ HM
          wp_func_lits
          wp_bind (App (App (Val (map.forRange _ _)) _) _)
          iapply (wp_map_for_range (fun keys i => iprop(
              (∃ c : swift.MFastAckClient, f_ptr ↦ c) ∗ ⌜0 ≤ i⌝ ∗
              [∗map] k ↦ v ∈ FM, iprop(⌜k ∉ keys.take i.toNat⌝ -∗ swift.facEntry γ γc γm v)))) $$ Hm
          iintro %keys %Hkeys
          isplitl [f HM]
          · isplitl [f]
            · iexists _; iexact f
            isplitr
            · ipureintro; omega
            iapply BigSepM.bigSepM_mono_of_forall $$ HM
            iintro %k %v H %h; iapply H; ipureintro; simp
          isplitl []
          · imodintro
            iintro %i %key %v %Hiv ⟨⟨%c0, f⟩, %Hi0, HM⟩
            ihave ⟨Hv, HM⟩ := swift.mapIter_step FM (swift.facEntry γ γc γm) keys i.toNat key v
              Hiv.1 Hiv.2 Hkeys.2.2 $$ HM
            wp_auto
            wp_method_call
            wp_call
            wp_auto
            iunfold swift.facEntry at Hv
            icases Hv with ⟨%cs, Hcsl, #Hvok, %Hvwf⟩
            wp_apply wp_sendc rr γ γc γm γw N me γs s v.CmdId'.ClientId'
              (interface.mkOk (go.GoType.PointerType swift.MFastAckClient.ty) #cf_ptr)
              (.fastAckClient v.Replica' v.Ballot' (swift.toCmdId v.CmdId') cs) csv.fastAckClientRPC'
              iprop(cf_ptr ↦ swift.MFastAckClient.mk v.Replica' v.Ballot' v.CmdId' v.Checksum' ∗
                v.Checksum' ↦* cs.map swift.handler.shashOf)
              $$ [$HisR $Hsbag cf Hcsl]
            · unfold replica.toSend
              isplitl
              · isplitr
                · iapply (hmf cf_ptr v.Replica' v.Ballot' v.CmdId' v.Checksum' cs Hvwf)
                isplitl [cf Hcsl]
                · iframe
                isplitr
                · iexact Hvok
                isplitr
                · unfold replica.freeOk; ileft; ipureintro; rfl
                ipureintro
                refine ⟨Hvwf, ?_⟩
                rw [Hpc.1.2.1]; rfl
              ipureintro
              simp [sp.Msg.isToClient, swift.toCmdId]
            unfold forMapPostcondition
            iright; ileft
            isplitr; · ipureintro; rfl
            isplitl [f]
            · iexists _; iexact f
            isplitr
            · ipureintro; omega
            have e : (i + 1).toNat = i.toNat + 1 := by omega
            rw [e]; iexact HM
          iintro ⟨⟨%c0, f⟩, -, -⟩ Hm
          try wp_auto
          -- the clients' slow-ack copies
          iunfold swift.slowMap at Hscm
          icases Hscm with ⟨%SM, Hsm, HSM⟩
          ihave HSM := swift.mapIter_start SM (swift.slowEntry γ γc γm) [] $$ HSM
          wp_func_lits
          wp_bind (App (App (Val (map.forRange _ _)) _) _)
          iapply (wp_map_for_range (fun keys i => iprop(
              (∃ c : swift.MLightSlowAck, s_ptr ↦ c) ∗ ⌜0 ≤ i⌝ ∗
              [∗map] k ↦ v ∈ SM, iprop(⌜k ∉ keys.take i.toNat⌝ -∗ swift.slowEntry γ γc γm v))))
            $$ Hsm
          iintro %keys2 %Hkeys2
          isplitl [s HSM]
          · isplitl [s]
            · iexists _; iexact s
            isplitr
            · ipureintro; omega
            iapply BigSepM.bigSepM_mono_of_forall $$ HSM
            iintro %k %v H %h; iapply H; ipureintro; simp
          isplitl []
          · imodintro
            iintro %i %key %v %Hiv ⟨⟨%c0, s⟩, %Hi0, HSM⟩
            ihave ⟨Hv, HSM⟩ := swift.mapIter_step SM (swift.slowEntry γ γc γm) keys2 i.toNat key v
              Hiv.1 Hiv.2 Hkeys2.2.2 $$ HSM
            wp_auto
            wp_method_call
            wp_call
            wp_auto
            iunfold swift.slowEntry at Hv
            icases Hv with ⟨%sv, %Hsv, #Hvok⟩
            wp_apply wp_sendc rr γ γc γm γw N me γs s v.CmdId'.ClientId'
              (interface.mkOk (go.GoType.PointerType swift.MLightSlowAck.ty) #cs_ptr)
              (.lightSlowAck sv) csv.lightSlowAckRPC' iprop(cs_ptr ↦ v)
              $$ [$HisR $Hsbag cs]
            · unfold replica.toSend
              isplitl
              · isplitr
                · iapply (hms cs_ptr v sv Hsv)
                isplitl [cs]
                · iframe
                isplitr
                · iexact Hvok
                isplitr
                · unfold replica.freeOk; ileft; ipureintro; rfl
                ipureintro
                refine ⟨trivial, ?_⟩
                rw [Hpc.1.2.2.2.1]; rfl
              ipureintro
              simp only [sp.Msg.isToClient]
              rw [← Hsv.2.2]; rfl
            unfold forMapPostcondition
            iright; ileft
            isplitr; · ipureintro; rfl
            isplitl [s]
            · iexists _; iexact s
            isplitr
            · ipureintro; omega
            have e : (i + 1).toNat = i.toNat + 1 := by omega
            rw [e]; iexact HSM
          iintro ⟨⟨%c0, s⟩, -, -⟩ Hsm
          try wp_auto
          wp_if_destruct
          · -- another ballot was seen: the `MAcks`
            try wp_auto
            wp_method_call
            wp_call
            wp_auto
            have hfpsl : fps.length = sint.nat fl0 := by
              have e2 := swift.snat_eq iv Hi2.1
              have e3 := swift.snat_eq fl0 Hfl0.1
              omega
            iunfold swift.fastSlots at Hfs
            icases Hfs with ⟨Hfsl, #Hfsr, %Hfsw⟩
            iunfold swift.slowSlots at Hss
            icases Hss with ⟨Hssl, #Hssr, %Hssw⟩
            isimp only [hfpsl, Nat.sub_self, List.replicate_zero, List.append_nil] at Hfsl
            isimp only [hspsl, Nat.sub_self, List.replicate_zero, List.append_nil] at Hssl
            icases BigSepL.bigSepL_sep_eqv.1 $$ Hfsr with ⟨#Hfr1, #Hfr2⟩
            wp_apply wp_senda rr γ γc γm γw N me γs s
              (interface.mkOk (go.GoType.PointerType swift.MAcks.ty) #acksl)
              (.acks (fps.map Prod.snd) (sps.map Prod.snd)) csv.acksRPC'
              iprop(typedPointsto acksl (swift.MAcks.mk fsl ssl) DFrac.discard ∗
                fsl ↦* fps.map Prod.fst ∗ ssl ↦* sps.map Prod.fst ∗
                [∗list] p ∈ fps, swift.fastAckRepr p.1 p.2)
              $$ [$HisR $Hsbag Hfsl Hssl]
            · have h16 : sint.Z fl0 ≤ 16 := Int.le_trans Hfl0.2 (by decide)
              have h16' : sint.Z sl0 ≤ 16 := Int.le_trans Hsl0.2 (by decide)
              have e3 := swift.snat_eq fl0 Hfl0.1
              have e4 := swift.snat_eq sl0 Hsl0.1
              have hwf : sp.Msg.wf (.acks (fps.map Prod.snd) (sps.map Prod.snd)) := by
                refine ⟨⟨?_, ?_⟩, ?_⟩
                · simp; omega
                · intro f hf; simp at hf; obtain ⟨a, ha⟩ := hf; exact Hfsw _ ha
                · simp; omega
              unfold replica.toSend
              isplitl
              · isplitr
                · iapply (hma acksl fsl ssl fps sps hwf Hssw)
                isplitl [Hfsl Hssl]
                · iframe Hacks Hfsl Hssl Hfr1
                isplitr
                · simp only [sp.msgOk]
                  isplitl
                  · rw [BigSepL.bigSepL_map]; iexact Hfr2
                  rw [BigSepL.bigSepL_map]; iexact Hssr
                isplitr
                · unfold replica.freeOk; ileft; ipureintro; rfl
                ipureintro
                refine ⟨hwf, ?_⟩
                rw [Hpc.1.2.2.2.2.1]; rfl
              ipureintro; trivial
            wp_for_post
            unfold named
            isplitl [Hlc1]
            · iexact Hlc1
            iexact Hlc2
          · -- every ack had the first's ballot: the `MOptAcks`
            have hbv : bv = sa0.Ballot' := by
              rcases Hi2.2.2.2 with h | h
              · exact h
              · exact absurd h Hif
            try wp_auto
            wp_method_call
            wp_call
            wp_auto
            iunfold swift.optSt at Hopt
            icases Hopt with ⟨%asl1, %aps, %IM, Ho, Ha, Hac, #Hr, Hm', %Hp, #Hnl⟩
            icases BigSepL.bigSepL_sep_eqv.1 $$ Hr with ⟨#Hr1, #Hr2⟩
            have hwf : sp.Msg.wf (.optAcks me sa0.Ballot' (aps.map Prod.snd)) := by
              refine ⟨?_, ?_⟩
              · have h16 : sint.Z fl0 ≤ 16 := Int.le_trans Hfl0.2 (by decide)
                have h16' : sint.Z sl0 ≤ 16 := Int.le_trans Hsl0.2 (by decide)
                have e3 := swift.snat_eq fl0 Hfl0.1
                have e4 := swift.snat_eq sl0 Hsl0.1
                have e2 := swift.snat_eq iv Hi2.1
                have := Hp.2.1
                simp; omega
              · intro a ha; simp at ha; obtain ⟨x, hx⟩ := ha; exact Hp.1 _ hx
            wp_apply wp_senda rr γ γc γm γw N me γs s
              (interface.mkOk (go.GoType.PointerType swift.MOptAcks.ty) #«$r0_ptr»)
              (.optAcks me sa0.Ballot' (aps.map Prod.snd)) csv.optAcksRPC'
              iprop(«$r0_ptr» ↦ swift.MOptAcks.mk me sa0.Ballot' asl1 ∗
                asl1 ↦* aps.map Prod.fst ∗ [∗list] p ∈ aps, swift.ackRepr p.1 p.2)
              $$ [$HisR $Hsbag Ho Ha]
            · unfold replica.toSend
              isplitl
              · isplitr
                · iapply (hmo «$r0_ptr» me sa0.Ballot' asl1 aps hwf)
                isplitl [Ho Ha]
                · iframe Ho Ha Hr1
                isplitr
                · simp only [sp.msgOk]
                  isplitr
                  · ipureintro
                    refine ⟨Hpc.2.1, ?_⟩
                    rw [Hs0.1.2.1]; exact Hw0.2
                  isplitr
                  · rw [BigSepL.bigSepL_map]; iexact Hr2
                  iapply swift.optNL_msg; iexact Hnl
                isplitr
                · unfold replica.freeOk; ileft; ipureintro; rfl
                ipureintro
                refine ⟨hwf, ?_⟩
                rw [Hpc.1.2.2.2.2.2.1]; rfl
              ipureintro; trivial
            wp_for_post
            unfold named
            isplitl [Hlc1]
            · iexact Hlc1
            iexact Hlc2
    iapply BigAndL.bigAndL_nil.2
    itrivial
  try wp_auto
  iapply HΦ
  unfold swift.batcherH
  iexists fa, ls, γ1, γ2
  isplitr
  · iexact «$r0»
  isplitr
  · iexact Hbf
  iexact Hbs

end proof

end Perennial.github_com.imdea_software.swiftpaxos
