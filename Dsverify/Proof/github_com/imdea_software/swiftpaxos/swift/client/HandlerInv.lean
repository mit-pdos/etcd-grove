/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/client/HandlerInv.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The client handler's invariant (notes/prove-clientpkg.md, "The handler's design"), its ghost
and per-message core: what the two message sets of a command `x` hold, as predicates of
`replica.MsgSet`'s internal spec (`Proof/replica/MsgSet.lean`), and the step from a reached
quorum (`handlerPre`) to `Decide.lean`'s certificates (the premises of `sp.accept_fast` /
`sp.accept_slow`).

An ack in a message set is an `*MFastAck` the handler built and never changes (`ackObj`,
persistent): its replica `k` (the set's key), ballot, command `x`, nil dependencies, and
checksum `hs`.
* fast path (`fastPathH[x]`), non-leader entries: an `MFastAckClient` of `k` (witness
  `msgOk (.fastAckClient k b x hs)`) or a light slow ack (`hs = []`, witness
  `msgOk (.lightSlowAck ⟨k, b, x⟩)`), never from ballot `b`'s leader (N4);
* slow path (`slowPathH[x]`), non-leader entries: light slow acks only;
* the leader entry (both paths): a copy of an `MReply` of ballot `b` (witness `msgOk (.reply
  r b x csL v)`; the fast path's copy keeps the checksum `csL`, the slow path's has none), and
  the record that `reps[x][b]` was set (`repRec`);
* accepted relative to the leader entry (`accA`): the same ballot, checksums `SHashesEq`.
With a leader entry, a fast-path entry has `SHashesEq csL hs`, and `csL` is not empty (a
checksum ends with the dependency hash), so it is an `MFastAckClient`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.Defs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.client.Decide
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.MsgSet

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace swift.handler

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]

/-- A command id as the protocol's. -/
def cmdOf (c : swift.CommandId) : sp.CmdId := ⟨c.ClientId', c.SeqNum'⟩

/-- A hash as a Go `SHash`. -/
def shashOf (h : sp.Hash) : swift.SHash := ⟨⟨h⟩⟩

theorem shashOf_inj : Function.Injective shashOf := by
  intro a b h; simp only [shashOf, swift.SHash.mk.injEq, GoArray.mk.injEq] at h; exact h

/-- The ack object `m`: an `*MFastAck` with contents `fa` (for good) and checksum `hs`. -/
def ackObj (m : GoInterface) (fa : swift.MFastAck) (hs : List sp.Hash) : IProp netDistGF :=
  iprop(∃ l : Loc, ⌜m = interface.mkOk (go.GoType.PointerType swift.MFastAck.ty) #l ∧
      ∀ h ∈ hs, h.length = 32⌝ ∗ l ↦□ fa ∗ fa.Checksum' ↦*□ (hs.map shashOf))

instance ackObj_persistent (m : GoInterface) (fa : swift.MFastAck) (hs : List sp.Hash) :
    Persistent (ackObj m fa hs) := by unfold ackObj; infer_instance

theorem ackObj_agree (m : GoInterface) (fa1 fa2 : swift.MFastAck) (hs1 hs2 : List sp.Hash) :
    ackObj m fa1 hs1 ∗ ackObj m fa2 hs2 ⊢ ⌜fa1 = fa2 ∧ hs1 = hs2⌝ := by
  unfold ackObj
  iintro ⟨⟨%l1, ⟨%Hm1, -⟩, Hl1, Hs1⟩, ⟨%l2, ⟨%Hm2, -⟩, Hl2, Hs2⟩⟩
  rw [Hm1] at Hm2
  have hl : l1 = l2 := by
    simp only [interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq, true_and] at Hm2
    exact go.intoVal_inj Hm2
  subst hl
  icombine Hl1 Hl2 gives %hfa
  subst hfa
  ihave %hhs := ownSlice_agree _ _ _ _ _ $$ Hs1 Hs2
  ipureintro
  exact ⟨rfl, (List.map_inj_right (fun a b h => shashOf_inj h)).mp hhs⟩

/-- `reps[x][b]` was set (the handler's record; persistent). -/
def repRec (γr : GName) (x : sp.CmdId) (b : w32) : IProp netDistGF :=
  iprop(∃ L : List (sp.CmdId × w32), monoListLbOwn γr L ∗ ⌜(x, b) ∈ L⌝)

/-- A non-leader entry of `x`'s fast (`fast = true`) or slow message set, keyed by its replica
`k`. -/
def entryP (γ : sp.Names) (γc γm : GName) (N : Nat) (cid : w32) (fast : Bool) (x : sp.CmdId)
    (k : w32) (m : GoInterface) : IProp netDistGF :=
  iprop(∃ (fa : swift.MFastAck) (hs : List sp.Hash), ackObj m fa hs ∗
    ⌜fa.Replica' = k ∧ cmdOf fa.CmdId' = x ∧ x.cl = cid ∧ fa.Dep' = slice.nil ∧
      sp.rid k ≠ sp.leaderOf N (sp.bal fa.Ballot')⌝ ∗
    ((⌜fast = true⌝ ∗ sp.msgOk γ γc γm (.fastAckClient k fa.Ballot' x hs)) ∨
      (⌜hs = []⌝ ∗ sp.msgOk γ γc γm (.lightSlowAck ⟨k, fa.Ballot', x⟩))))

/-- The leader entry of `x`'s fast or slow message set: a copy of an `MReply` of `x`. -/
def leaderP (γ : sp.Names) (γc γm γr : GName) (cid : w32) (fast : Bool) (x : sp.CmdId)
    (m : GoInterface) : IProp netDistGF :=
  iprop(∃ (fa : swift.MFastAck) (hs csL : List sp.Hash) (v : List w8), ackObj m fa hs ∗
    ⌜cmdOf fa.CmdId' = x ∧ x.cl = cid ∧ fa.Dep' = slice.nil ∧
      hs = (if fast then csL else [])⌝ ∗
    sp.msgOk γ γc γm (.reply fa.Replica' fa.Ballot' x csL v) ∗ repRec γr x fa.Ballot')

/-- Accepted relative to the leader entry: the same ballot, the checksums `SHashesEq`. -/
def accA (lm m : GoInterface) : IProp netDistGF :=
  iprop(∃ (fa1 fa2 : swift.MFastAck) (hs1 hs2 : List sp.Hash), ackObj lm fa1 hs1 ∗
    ackObj m fa2 hs2 ∗ ⌜fa1.Ballot' = fa2.Ballot' ∧ sp.shashesEq hs1 hs2⌝)

instance entryP_persistent γ γc γm N cid fast x k m :
    Persistent (entryP γ γc γm N cid fast x k m) := by
  unfold entryP; haveI := sp.msgOk_persistent (γ := γ) (γc := γc) (γm := γm); infer_instance
instance leaderP_persistent γ γc γm γr cid fast x m :
    Persistent (leaderP γ γc γm γr cid fast x m) := by
  unfold leaderP repRec; haveI := sp.msgOk_persistent (γ := γ) (γc := γc) (γm := γm)
  infer_instance
instance accA_persistent lm m : Persistent (accA lm m) := by unfold accA; infer_instance

theorem ackObj_iface (m : GoInterface) (fa : swift.MFastAck) (hs : List sp.Hash) :
    ackObj m fa hs ⊢ ∃ l : Loc, ⌜m = interface.mkOk (go.GoType.PointerType swift.MFastAck.ty) #l⌝ := by
  unfold ackObj
  iintro ⟨%l, ⟨%Hm, -⟩, -⟩
  iexists l; ipureintro; exact Hm

theorem entryP_iface γ γc γm N cid fast x k m :
    entryP γ γc γm N cid fast x k m ⊢
      ∃ l : Loc, ⌜m = interface.mkOk (go.GoType.PointerType swift.MFastAck.ty) #l⌝ := by
  unfold entryP
  iintro ⟨%fa, %hs, Ho, -⟩
  iapply ackObj_iface $$ Ho

theorem leaderP_iface γ γc γm γr cid fast x m :
    leaderP γ γc γm γr cid fast x m ⊢
      ∃ l : Loc, ⌜m = interface.mkOk (go.GoType.PointerType swift.MFastAck.ty) #l⌝ := by
  unfold leaderP
  iintro ⟨%fa, %hs, %csL, %v, Ho, -⟩
  iapply ackObj_iface $$ Ho

end defs

section cert
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]

/-- A leader reply's checksum is not empty (it ends with the dependency hash). Unfolds
`sp.msgOk`, `sp.checksum` (notes: a missing law `msgOk_reply_cs`). -/
theorem reply_cs_ne (γ : sp.Names) (γc γm : GName) (r b : w32) (x : sp.CmdId)
    (cs : List sp.Hash) (v : List w8) :
    sp.msgOk γ γc γm (.reply r b x cs v) ⊢ ⌜cs ≠ []⌝ := by
  simp only [sp.msgOk, sp.checksum]
  iintro ⟨%N, %fr, %l, %s, %Ps, %c, -, -, ⟨%hs, %d, %Hcs, -⟩, -⟩
  ipureintro; subst Hcs; simp

/-- One fast-path entry, accepted relative to a leader entry of ballot `fa.Ballot'` with a
non-empty checksum `csL`: an `MFastAckClient` of that ballot, checksums `SHashesEq`, not from
the ballot's leader. -/
theorem entry_fast (γ : sp.Names) (γc γm : GName) (N : Nat) (cid : w32) (x : sp.CmdId)
    (lm : GoInterface) (fa : swift.MFastAck) (csL : List sp.Hash) (hcs : csL ≠ [])
    (hlm : lm ≠ interface.nil) (k : w32) (m : GoInterface) :
    ackObj lm fa csL ∗ entryP γ γc γm N cid true x k m ∗ replica.mset.accOk accA lm m ⊢
    ∃ hs, ⌜sp.shashesEq csL hs ∧ sp.rid k ≠ sp.leaderOf N (sp.bal fa.Ballot')⌝ ∗
      sp.msgOk γ γc γm (.fastAckClient k fa.Ballot' x hs) := by
  haveI := sp.msgOk_persistent (γ := γ) (γc := γc) (γm := γm)
  unfold entryP replica.mset.accOk accA
  iintro ⟨#HL, ⟨%fa2, %hs2, #H2, ⟨%Hk, %Hx, %Hcl, %Hdep, %Hnl⟩, #Hw⟩, Hacc⟩
  icases Hacc with (%Hn | ⟨%fa1', %fa2', %hs1', %hs2', #HL', #H2', ⟨%Hbal, %Heq⟩⟩)
  · exact absurd Hn hlm
  ihave %HaL := ackObj_agree lm fa fa1' csL hs1' $$ [HL HL']
  · iframe #
  ihave %Ha2 := ackObj_agree m fa2 fa2' hs2 hs2' $$ [H2 H2']
  · iframe #
  obtain ⟨rfl, rfl⟩ := HaL
  obtain ⟨rfl, rfl⟩ := Ha2
  icases Hw with (⟨-, #Hw⟩ | ⟨%Hnil, -⟩)
  · iexists hs2
    rw [Hbal]
    isplitr
    · ipureintro; exact ⟨Heq, Hbal ▸ Hnl⟩
    iexact Hw
  · subst Hnil
    exfalso
    have := Heq.1
    simp at this
    exact hcs this

/-- The fast entries of a reached quorum, collected. -/
theorem entries_fast (γ : sp.Names) (γc γm : GName) (N : Nat) (cid : w32) (x : sp.CmdId)
    (lm : GoInterface) (fa : swift.MFastAck) (csL : List sp.Hash) (hcs : csL ≠ [])
    (hlm : lm ≠ interface.nil) (kms : List (w32 × GoInterface)) :
    ackObj lm fa csL ∗
      (□ ∀ k m, ⌜(k, m) ∈ kms⌝ → entryP γ γc γm N cid true x k m ∗
        replica.mset.accOk accA lm m) ⊢
    ∃ acks : List (w32 × List sp.Hash), ⌜acks.map Prod.fst = kms.map Prod.fst ∧
        ∀ a ∈ acks, sp.shashesEq csL a.2 ∧ sp.rid a.1 ≠ sp.leaderOf N (sp.bal fa.Ballot')⌝ ∗
      □ (∀ a, ⌜a ∈ acks⌝ → sp.msgOk γ γc γm (.fastAckClient a.1 fa.Ballot' x a.2)) := by
  haveI := sp.msgOk_persistent (γ := γ) (γc := γc) (γm := γm)
  induction kms with
  | nil =>
    iintro -
    iexists []
    isplitr
    · ipureintro; simp
    imodintro; iintro %a %ha; simp at ha
  | cons km kms ih =>
    obtain ⟨k, m⟩ := km
    iintro ⟨#HL, #Hall⟩
    ihave #Hhd := Hall $$ %k %m %(List.mem_cons_self : (k, m) ∈ (k, m) :: kms)
    ihave ⟨%hs, %Hhs, #Hw⟩ := entry_fast γ γc γm N cid x lm fa csL hcs hlm k m $$ [HL Hhd]
    · iframe #
    ihave ⟨%acks, %Hacks, #Hws⟩ := ih $$ [HL Hall]
    · iframe HL
      imodintro
      iintro %k' %m' %hkm
      iapply Hall
      ipureintro; simp [hkm]
    iexists (k, hs) :: acks
    isplitr
    · ipureintro
      refine ⟨by simp [Hacks.1], ?_⟩
      intro a ha
      simp only [List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact Hhs
      · exact Hacks.2 a ha
    imodintro
    iintro %a %ha
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · iexact Hw
    · iapply Hws; ipureintro; exact ha

/-- One slow-path entry, accepted relative to a leader entry of ballot `fa.Ballot'`: a light
slow ack of that ballot, not from the ballot's leader. -/
theorem entry_slow (γ : sp.Names) (γc γm : GName) (N : Nat) (cid : w32) (x : sp.CmdId)
    (lm : GoInterface) (fa : swift.MFastAck) (hsL : List sp.Hash)
    (hlm : lm ≠ interface.nil) (k : w32) (m : GoInterface) :
    ackObj lm fa hsL ∗ entryP γ γc γm N cid false x k m ∗ replica.mset.accOk accA lm m ⊢
    ⌜sp.rid k ≠ sp.leaderOf N (sp.bal fa.Ballot')⌝ ∗
      sp.msgOk γ γc γm (.lightSlowAck ⟨k, fa.Ballot', x⟩) := by
  haveI := sp.msgOk_persistent (γ := γ) (γc := γc) (γm := γm)
  unfold entryP replica.mset.accOk accA
  iintro ⟨#HL, ⟨%fa2, %hs2, #H2, ⟨%Hk, %Hx, %Hcl, %Hdep, %Hnl⟩, #Hw⟩, Hacc⟩
  icases Hacc with (%Hn | ⟨%fa1', %fa2', %hs1', %hs2', #HL', #H2', ⟨%Hbal, %Heq⟩⟩)
  · exact absurd Hn hlm
  ihave %HaL := ackObj_agree lm fa fa1' hsL hs1' $$ [HL HL']
  · iframe #
  ihave %Ha2 := ackObj_agree m fa2 fa2' hs2 hs2' $$ [H2 H2']
  · iframe #
  obtain ⟨rfl, rfl⟩ := HaL
  obtain ⟨rfl, rfl⟩ := Ha2
  icases Hw with (⟨%Hf, -⟩ | ⟨-, #Hw⟩)
  · cases Hf
  · rw [Hbal]
    isplitr
    · ipureintro; exact Hbal ▸ Hnl
    iexact Hw

/-- The slow entries of a reached quorum, collected. -/
theorem entries_slow (γ : sp.Names) (γc γm : GName) (N : Nat) (cid : w32) (x : sp.CmdId)
    (lm : GoInterface) (fa : swift.MFastAck) (hsL : List sp.Hash)
    (hlm : lm ≠ interface.nil) (kms : List (w32 × GoInterface)) :
    ackObj lm fa hsL ∗
      (□ ∀ k m, ⌜(k, m) ∈ kms⌝ → entryP γ γc γm N cid false x k m ∗
        replica.mset.accOk accA lm m) ⊢
    ⌜∀ r ∈ kms.map Prod.fst, sp.rid r ≠ sp.leaderOf N (sp.bal fa.Ballot')⌝ ∗
      □ (∀ r, ⌜r ∈ kms.map Prod.fst⌝ → sp.msgOk γ γc γm (.lightSlowAck ⟨r, fa.Ballot', x⟩)) := by
  haveI := sp.msgOk_persistent (γ := γ) (γc := γc) (γm := γm)
  induction kms with
  | nil =>
    iintro -
    isplitr
    · ipureintro; simp
    imodintro; iintro %a %ha; simp at ha
  | cons km kms ih =>
    obtain ⟨k, m⟩ := km
    iintro ⟨#HL, #Hall⟩
    ihave #Hhd := Hall $$ %k %m %(List.mem_cons_self : (k, m) ∈ (k, m) :: kms)
    ihave ⟨%Hk, #Hw⟩ := entry_slow γ γc γm N cid x lm fa hsL hlm k m $$ [HL Hhd]
    · iframe #
    ihave ⟨%Hrs, #Hws⟩ := ih $$ [HL Hall]
    · iframe HL
      imodintro
      iintro %k' %m' %hkm
      iapply Hall
      ipureintro; simp [hkm]
    isplitr
    · ipureintro
      intro r hr
      simp only [List.map_cons, List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact Hk
      · exact Hrs r hr
    imodintro
    iintro %r %hr
    simp only [List.map_cons, List.mem_cons] at hr
    rcases hr with rfl | hr
    · iexact Hw
    · iapply Hws; ipureintro; exact hr

/-- **The certificate of a reached quorum** (`handleFastAndSlowAcks`'s premise): what
`MsgSet.Add` gives the handler for `x`'s fast or slow message set, with a leader entry, is
the leader's object (a reply of `x`, ballot `b`, recorded in `reps`) and the fast or the slow
certificate of `b` (`Decide.lean`). -/
theorem cert (γ : sp.Names) (γc γm γr : GName) (N : Nat) (cid : w32) (fast : Bool)
    (x : sp.CmdId) (lm : GoInterface) (ms : List GoInterface) (hlm : lm ≠ interface.nil) :
    replica.mset.handlerPre (N / 2 + 1) (entryP γ γc γm N cid fast x) accA
      (leaderP γ γc γm γr cid fast x) lm ms ⊢
    ∃ (fa : swift.MFastAck) (hs : List sp.Hash), ackObj lm fa hs ∗
      ⌜cmdOf fa.CmdId' = x ∧ x.cl = cid⌝ ∗ repRec γr x fa.Ballot' ∗
      (fastCert γ γc γm N fa.Ballot' x ∨ slowCert γ γc γm N fa.Ballot' x) := by
  haveI := sp.msgOk_persistent (γ := γ) (γc := γc) (γm := γm)
  unfold replica.mset.handlerPre replica.mset.leaderOk
  iintro ⟨%kms, ⟨%Hms, %Hnd, %Hthr⟩, HL, #Hall⟩
  icases HL with (%Hn | #HL)
  · exact absurd Hn hlm
  unfold leaderP
  icases HL with ⟨%fa, %hs, %csL, %v, #Hobj, ⟨%Hx, %Hcl, %Hdep, %Hhs⟩, #Hrep, #Hrec⟩
  have hlen : N / 2 ≤ kms.length := by
    have : ms.length = kms.length := by rw [Hms]; simp
    omega
  iexists fa, hs
  iframe Hobj Hrec
  isplitr
  · ipureintro; exact ⟨Hx, Hcl⟩
  cases fast
  · -- slow
    iright
    unfold slowCert
    iexists fa.Replica', csL, v, kms.map Prod.fst
    simp only [Bool.false_eq_true, ↓reduceIte] at Hhs
    subst Hhs
    ihave ⟨%Hrs, #Hws⟩ := entries_slow γ γc γm N cid x lm fa [] hlm kms $$ [Hobj Hall]
    · iframe #
    iframe Hrep
    isplitr
    · ipureintro
      refine ⟨Hnd, by simp; omega, Hrs⟩
    iapply BigSepL.bigSepL_forall_elim
    iintro %i %a %Hi
    iapply Hws
    ipureintro
    exact List.mem_of_getElem? Hi
  · -- fast
    ileft
    simp only [↓reduceIte] at Hhs
    subst Hhs
    ihave %Hcs := reply_cs_ne γ γc γm _ _ x hs v $$ Hrep
    ihave ⟨%acks, ⟨%Hacks1, %Hacks2⟩, #Hws⟩ :=
      entries_fast γ γc γm N cid x lm fa hs Hcs hlm kms $$ [Hobj Hall]
    · iframe #
    unfold fastCert
    iexists fa.Replica', hs, v, acks
    iframe Hrep
    isplitr
    · ipureintro
      refine ⟨Hacks1 ▸ Hnd, ?_, Hacks2⟩
      have := congrArg List.length Hacks1
      simp only [List.length_map] at this
      omega
    iapply BigSepL.bigSepL_forall_elim
    iintro %i %a %Hi
    iapply Hws
    ipureintro
    exact List.mem_of_getElem? Hi

end cert

end swift.handler

end Perennial.github_com.imdea_software.swiftpaxos
