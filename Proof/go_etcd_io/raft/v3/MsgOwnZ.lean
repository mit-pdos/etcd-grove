/-
**Raft's messages at a content of bounded size** (out_size C3, P3, 2026-11-12; the Scope's `msgQC`).

A message raft queues (its outbox, `msgQ`), hands out (`Ready`) or sends is owned at a wire content
(`msgOwnZ sz l dq st`): an object at a content `c` (`msgPtsCC`, the entries' slice read-only) whose
model is `st`, which raft pins (`sentOk`: no unknown fields on a `MsgSnap`, none on a snapshot's conf
state), and which, when the node's flag `sz` is set (a cluster that bounds proposed data, the storage
names' `sz`), is of bounded size (`msgSizeOk`) unless a `MsgSnap`. It replaces today's pair `msgOwn l
dq st ∗ snapUf l st`: a persistent witness next to `msgOwn` cannot pin the content's size, since
`msgOwn`'s entry objects are existential and `pbMsg` has no agreement law (the Scope's §1). Readers
take half in today's form (`msgOwnZ_read`, `MsgRead.lean`'s trick); `send`'s stores keep the content
(`msgOwnZ_store_From`/`_Term`), changing only scalars, which the size does not count.
-/
module

public import Proof.go_etcd_io.raft.v3.MsgOut
public import Proof.go_etcd_io.raft.v3.MsgRead
public import Proof.go_etcd_io.raft.v3.InvPbMsg

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The size condition of a message raft holds at the content `c`, under the node's flag `sz`. -/
def msgSzOk (sz : Bool) (c : MsgC) : Prop :=
  c.sentOk ∧ (sz = true → c.model.msg.Type' ≠ MsgSnap → msgSizeOk c)

/-- **A message raft holds, at a content** (see the file header). -/
def msgOwnZ (sz : Bool) (l : Loc) (dq : DFrac) (st : MsgSt) : IProp GF :=
  iprop(∃ c : MsgC, msgPtsCC l dq DFrac.discard false c ∗ ⌜c.model = st ∧ msgSzOk sz c⌝)

/-- (out_size C3, Scope §2.3) **A received message at a content**, as `msgIn` holds it (the struct
owned, the entries slice at `dqe`, its capacity when `needsCap`), of bounded size under the node's flag
`sz` but a `MsgSnap`: what `raft.Step` takes, so that the handlers that move the message's objects
(forwards, appended entries, stored read requests) keep their sizes. -/
def msgInC (sz : Bool) (l : Loc) (dqe : DFrac) (st : MsgSt) : IProp GF :=
  iprop(∃ c : MsgC, msgPtsCC l (DFrac.own 1) dqe (needsCap st.msg) c ∗
    ⌜c.model = st ∧ c.csUfNil ∧ (sz = true → st.msg.Type' ≠ MsgSnap → msgSizeOk c)⌝)

end defs

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- A message at a content is owned in today's form. -/
theorem msgOwnZ_msgOwn (sz : Bool) (l : Loc) (dq : DFrac) (st : MsgSt) :
    msgOwnZ (GF := GF) sz l dq st ⊢ msgOwn l dq st := by
  unfold msgOwnZ
  iintro ⟨%c, Hc, %H⟩
  obtain ⟨Hm, Hok, -⟩ := H
  rw [← Hm]
  simp only [msgOwn, msgPts]
  iapply msgPtsCC_msgPtsC l dq DFrac.discard false c Hok.1 $$ Hc

/-- (out_size C3) A received message at a content is one in today's form (`msgIn`). -/
theorem msgInC_msgIn (sz : Bool) (l : Loc) (dqe : DFrac) (st : MsgSt) :
    msgInC (GF := GF) sz l dqe st ⊢ msgIn l dqe st := by
  unfold msgInC
  iintro ⟨%c, Hc, %H⟩
  obtain ⟨Hm, Hok, -⟩ := H
  simp only [msgIn]
  ihave H := msgPtsCC_msgPtsC l (DFrac.own 1) dqe (needsCap st.msg) c Hok $$ Hc
  rw [Hm]; iexact H

/-- (out_size C3) At the flag `false`, a received message in today's form is one at a content. -/
theorem msgIn_msgInC (l : Loc) (dqe : DFrac) (st : MsgSt) :
    msgIn (GF := GF) l dqe st ⊢ msgInC false l dqe st := by
  simp only [msgIn]
  iintro H
  ihave ⟨%c, Hc, %Hc⟩ := (msgPtsC_iff_CC l (DFrac.own 1) dqe (needsCap st.msg) st).1 $$ H
  unfold msgInC
  iexists c
  iframe Hc
  ipureintro
  exact ⟨Hc.1, Hc.2, fun h => absurd h (by simp)⟩

/-- The flag forgotten. -/
theorem msgOwnZ_unsize (sz : Bool) (l : Loc) (dq : DFrac) (st : MsgSt) :
    msgOwnZ (GF := GF) sz l dq st ⊢ msgOwnZ false l dq st := by
  unfold msgOwnZ
  iintro ⟨%c, Hc, %H⟩
  iexists c
  iframe Hc
  ipureintro
  exact ⟨H.1, H.2.1, fun h => absurd h (by simp)⟩

/-- At the flag `false`, today's pair (`msgOwn_snapUf_CC`). -/
theorem msgOwnZ_of_snapUf (l : Loc) (dq : DFrac) (st : MsgSt) :
    msgOwn (GF := GF) l dq st ∗ snapUf l st ⊢ msgOwnZ false l dq st := by
  iintro H
  icases msgOwn_snapUf_CC l dq st $$ H with ⟨%c, Hc, %Hm⟩
  unfold msgOwnZ
  iexists c
  iframe Hc
  ipureintro
  exact ⟨Hm.1, Hm.2, fun h => absurd h (by simp)⟩

/-- The pure size facts of a content without unknown fields, entries, snapshot and responses, whose
context is at most `entBytesMax` bytes. -/
theorem msgSizeOk_of_lit (c : MsgC) (hu : c.f.uf = []) (he : c.model.ents = [])
    (hs : c.model.snap = none) (hr : c.model.resps = []) (hc : c.model.ctx.length ≤ entBytesMax) :
    msgSizeOk c := by
  obtain ⟨f, rs⟩ := c
  simp only [MsgC.model, MsgC.f, MsgC.resps, List.map_eq_nil_iff, Option.map_eq_none_iff] at he hs hr hc hu
  refine ⟨by simpa [MsgC.resps] using hr, ?_, ?_, ?_⟩
  · simp only [hdrBytes, MsgC.f, hu, hs, optSnapSize, List.length_nil, Nat.add_zero]; exact hc
  · simp [MsgC.f, he]
  · simp [MsgC.f, he]

/-- **A message raft built** (a literal's `msgOwn`, with the fresh object's `pbMsg` at no unknown
fields, `msgOwn_of_struct_uf`): at a content of bounded size when it has no entries, no snapshot and
a context of at most `entBytesMax` bytes, unless a `MsgSnap`. -/
theorem msgOwnZ_of_uf (sz : Bool) (l : Loc) (dq : DFrac) (st : MsgSt)
    (Hst : st.resps = [] ∧ (sz = true → st.msg.Type' ≠ MsgSnap →
      st.ents = [] ∧ st.snap = none ∧ st.ctx.length ≤ entBytesMax)) :
    msgOwn (GF := GF) l dq st ∗ pbMsg raftpb.Message l [] ⊢ msgOwnZ sz l dq st := by
  iintro ⟨H, #Hp⟩
  simp only [msgOwn, msgPts]
  icases msgPtsC_msgPtsCC_uf l dq DFrac.discard false st [] $$ [H Hp] with ⟨%c, Hc, %Hm⟩
  · iframe H Hp
  obtain ⟨Hmod, Hcs, Hu⟩ := Hm
  unfold msgOwnZ
  iexists c
  iframe Hc
  ipureintro
  refine ⟨Hmod, ⟨Hcs, fun _ => Hu⟩, fun hs hty => ?_⟩
  rw [Hmod] at hty
  obtain ⟨h1, h2, h3, h4⟩ := (⟨Hst.1, Hst.2 hs hty⟩ : _ ∧ _)
  exact msgSizeOk_of_lit c Hu (by rw [Hmod]; exact h2) (by rw [Hmod]; exact h3)
    (by rw [Hmod]; exact h1) (by rw [Hmod]; exact h4)

end lemmas

section halves
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

theorem discard_op_discard : (DFrac.discard • DFrac.discard : DFrac) = DFrac.discard := rfl

/-- **Half of a message held at a content**, the other half in today's form. -/
theorem msgOwnZ_halves (sz : Bool) (l : Loc) (st : MsgSt) :
    msgOwnZ (GF := GF) sz l (DFrac.own 1) st ⊢ msgOwnZ sz l dqh st ∗ msgOwn l dqh st := by
  unfold msgOwnZ
  iintro ⟨%c, Hc, %H⟩
  have h := msgPtsCC_splitE (GF := GF) l false c DFrac.discard DFrac.discard
  rw [discard_op_discard] at h
  icases h $$ Hc with ⟨H1, H2⟩
  isplitl [H1]
  · iexists c; iframe H1; ipureintro; exact H
  · obtain ⟨Hm, Hok, -⟩ := H
    rw [← Hm]
    simp only [msgOwn, msgPts]
    iapply msgPtsCC_msgPtsC l dqh DFrac.discard false c Hok.1 $$ H2

/-- ... and back, at the kept half's content. -/
theorem msgOwnZ_unhalves (sz : Bool) (l : Loc) (st : MsgSt) :
    msgOwnZ (GF := GF) sz l dqh st ∗ msgOwn l dqh st ⊢ msgOwnZ sz l (DFrac.own 1) st := by
  unfold msgOwnZ
  iintro ⟨⟨%c, H1, %H⟩, H2⟩
  simp only [msgOwn, msgPts]
  icases msgPtsC_msgPtsCC l dqh DFrac.discard false st $$ H2 with ⟨%c', H2, -⟩
  have h := msgPtsCC_joinE (GF := GF) l false c c' DFrac.discard DFrac.discard
  rw [discard_op_discard] at h
  iexists c
  isplitl [H1 H2]
  · iapply h; iframe H1 H2
  · ipureintro; exact H

/-- **Reading a message held at a content** through today's specs (the getters): half of it in
today's form, and what rebuilds it at the same content from that half given back. -/
theorem msgOwnZ_read (sz : Bool) (l : Loc) (st : MsgSt) :
    msgOwnZ (GF := GF) sz l (DFrac.own 1) st ⊢
      msgOwn l dqh st ∗ (msgOwn l dqh st -∗ msgOwnZ sz l (DFrac.own 1) st) := by
  iintro H
  icases msgOwnZ_halves sz l st $$ H with ⟨H1, H2⟩
  iframe H2
  iintro H2
  iapply msgOwnZ_unhalves sz l st
  iframe H1 H2

end halves

section stores
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- A scalar cell read-only (`cellRO`) is a set or unset optional field at the same value. -/
theorem cellRO_optCell' {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (p : Loc) (v : V) :
    cellRO (GF := GF) p v ⊢ ∃ o : Option V, optCell p o ∗ ⌜o.getD (zero_val V) = v⌝ := by
  unfold cellRO
  iintro (%H | #H)
  · obtain ⟨rfl, rfl⟩ := H
    iexists none
    simp only [optCell]
    ipureintro; simp
  · iexists (some v)
    simp only [optCell]
    iframe H
    ipureintro; rfl

/-- `m.From = new(r.id)` (`send`) on a message at a content: only the field's presence changes. -/
theorem msgPtsCC_store_From (l : Loc) (dqe : DFrac) (cap : Bool) (c : MsgC) :
    msgPtsCC (GF := GF) l (DFrac.own 1) dqe cap c ⊢
      ∃ p : Loc, l.[raftpb.Message, go!"From"] ↦ p ∗
        (∀ (p' : Loc) (v : w64), l.[raftpb.Message, go!"From"] ↦ p' -∗ cellRO p' v -∗
          ∃ o : Option w64, msgPtsCC l (DFrac.own 1) dqe cap (.mk { c.f with frm := o } c.resps) ∗
            ⌜o.getD (zero_val w64) = v⌝) := by
  unfold msgPtsCC
  iintro ⟨%pty, %pto, %pfr, %pte, %plt, %pix, %pco, %pvo, %prj, %prh, %es, %els, %ps, %cs, %rs,
    %Hnn, HTy, #cTy, HTo, #cTo, HFr, #cFr, HTe, #cTe, HLt, #cLt, HIx, #cIx, HCo, #cCo,
    HVo, #cVo, HRj, #cRj, HRh, #cRh, HEs, Hes, #Hents, Hcap, HSn, Hsn, HCx, #Hcx, HRs, Hrs, #Hpb⟩
  iexists pfr
  iframe HFr
  iintro %p' %v HFr #cFr'
  icases cellRO_optCell' p' v $$ cFr' with ⟨%o, #cO, %Ho⟩
  iexists o
  isplitl
  · iexists pty, pto, p', pte, plt, pix, pco, pvo, prj, prh, es, els, ps, cs, rs
    simp only [MsgC.f, MsgC.resps]
    isplitr
    · ipureintro; exact Hnn
    iframe
    iframe cTy cTo cO cTe cLt cIx cCo cVo cRj cRh Hents Hcx Hpb
  · ipureintro; exact Ho

/-- `m.Term = new(r.Term)` (`send`) on a message at a content. -/
theorem msgPtsCC_store_Term (l : Loc) (dqe : DFrac) (cap : Bool) (c : MsgC) :
    msgPtsCC (GF := GF) l (DFrac.own 1) dqe cap c ⊢
      ∃ p : Loc, l.[raftpb.Message, go!"Term"] ↦ p ∗
        (∀ (p' : Loc) (v : w64), l.[raftpb.Message, go!"Term"] ↦ p' -∗ cellRO p' v -∗
          ∃ o : Option w64, msgPtsCC l (DFrac.own 1) dqe cap (.mk { c.f with term := o } c.resps) ∗
            ⌜o.getD (zero_val w64) = v⌝) := by
  unfold msgPtsCC
  iintro ⟨%pty, %pto, %pfr, %pte, %plt, %pix, %pco, %pvo, %prj, %prh, %es, %els, %ps, %cs, %rs,
    %Hnn, HTy, #cTy, HTo, #cTo, HFr, #cFr, HTe, #cTe, HLt, #cLt, HIx, #cIx, HCo, #cCo,
    HVo, #cVo, HRj, #cRj, HRh, #cRh, HEs, Hes, #Hents, Hcap, HSn, Hsn, HCx, #Hcx, HRs, Hrs, #Hpb⟩
  iexists pte
  iframe HTe
  iintro %p' %v HTe #cTe'
  icases cellRO_optCell' p' v $$ cTe' with ⟨%o, #cO, %Ho⟩
  iexists o
  isplitl
  · iexists pty, pto, pfr, p', plt, pix, pco, pvo, prj, prh, es, els, ps, cs, rs
    simp only [MsgC.f, MsgC.resps]
    isplitr
    · ipureintro; exact Hnn
    iframe
    iframe cTy cTo cFr cO cLt cIx cCo cVo cRj cRh Hents Hcx Hpb
  · ipureintro; exact Ho

/-- `send`'s `From` store on a message raft holds at a content: the size kept. -/
theorem msgOwnZ_store_From (sz : Bool) (l : Loc) (st : MsgSt) :
    msgOwnZ (GF := GF) sz l (DFrac.own 1) st ⊢
      ∃ p : Loc, l.[raftpb.Message, go!"From"] ↦ p ∗
        (∀ (p' : Loc) (v : w64), l.[raftpb.Message, go!"From"] ↦ p' -∗ cellRO p' v -∗
          msgOwnZ sz l (DFrac.own 1) { st with msg := { st.msg with From' := v } }) := by
  unfold msgOwnZ
  iintro ⟨%c, Hc, %H⟩
  icases msgPtsCC_store_From l DFrac.discard false c $$ Hc with ⟨%p, Hp, Hback⟩
  iexists p
  iframe Hp
  iintro %p' %v Hp #cv
  icases Hback $$ %p' %v Hp cv with ⟨%o, Hc, %Ho⟩
  iexists _
  iframe Hc
  ipureintro
  obtain ⟨Hm, ⟨Hcs, Hsn⟩, Hsz⟩ := H
  obtain ⟨f, rs⟩ := c
  subst Hm
  refine ⟨?_, ⟨Hcs, Hsn⟩, fun hs ht => ?_⟩
  · simp only [MsgC.model, MsgC.f, MsgC.resps, MsgFC.msgM, Ho]
  · obtain ⟨h1, h2, h3, h4⟩ := Hsz hs ht
    exact ⟨h1, h2, h3, h4⟩

/-- `send`'s `Term` store on a message raft holds at a content: the size kept. -/
theorem msgOwnZ_store_Term (sz : Bool) (l : Loc) (st : MsgSt) :
    msgOwnZ (GF := GF) sz l (DFrac.own 1) st ⊢
      ∃ p : Loc, l.[raftpb.Message, go!"Term"] ↦ p ∗
        (∀ (p' : Loc) (v : w64), l.[raftpb.Message, go!"Term"] ↦ p' -∗ cellRO p' v -∗
          msgOwnZ sz l (DFrac.own 1) { st with msg := { st.msg with Term' := v } }) := by
  unfold msgOwnZ
  iintro ⟨%c, Hc, %H⟩
  icases msgPtsCC_store_Term l DFrac.discard false c $$ Hc with ⟨%p, Hp, Hback⟩
  iexists p
  iframe Hp
  iintro %p' %v Hp #cv
  icases Hback $$ %p' %v Hp cv with ⟨%o, Hc, %Ho⟩
  iexists _
  iframe Hc
  ipureintro
  obtain ⟨Hm, ⟨Hcs, Hsn⟩, Hsz⟩ := H
  obtain ⟨f, rs⟩ := c
  subst Hm
  refine ⟨?_, ⟨Hcs, Hsn⟩, fun hs ht => ?_⟩
  · simp only [MsgC.model, MsgC.f, MsgC.resps, MsgFC.msgM, Ho]
  · obtain ⟨h1, h2, h3, h4⟩ := Hsz hs ht
    exact ⟨h1, h2, h3, h4⟩

end stores

/-! ### Received messages at a content (out_size C3, the msgInC plan) -/

section recv
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- (out_size C3) **The message types whose handlers move the received message's objects** (Scope
§2.3): a proposal (appended, or forwarded), a `MsgApp` (its entries appended), a heartbeat (its
context echoed), a read-index request (stored and answered, or forwarded) and a leader-transfer
request (forwarded). The `stepX` specs take a received message at its content under the node's flag
for these types only (`msgInC (s.gh.sn.sz && movesB m.Type')`). -/
def movesB (t : w32) : Bool :=
  decide (t = MsgProp ∨ t = MsgApp ∨ t = MsgHeartbeat ∨ t = MsgReadIndex ∨ t = MsgTransferLeader)

set_option hygiene false in
/-- `movesB m.Type' = false` from the type hypothesis `Hty` in scope. -/
macro "movesB_tac" : tactic =>
  `(tactic| first
    | decide
    | (rw [Hty]; decide)
    | (simp only [movesB, decide_eq_false_iff_not]; intro hc;
       rcases hc with hc | hc | hc | hc | hc <;>
         simp_all [MsgProp, MsgApp, MsgHeartbeat, MsgReadIndex, MsgTransferLeader]))

theorem movesB_MsgProp : movesB MsgProp = true := by decide
theorem movesB_MsgApp : movesB MsgApp = true := by decide
theorem movesB_MsgHeartbeat : movesB MsgHeartbeat = true := by decide
theorem movesB_MsgReadIndex : movesB MsgReadIndex = true := by decide
theorem movesB_MsgTransferLeader : movesB MsgTransferLeader = true := by decide

theorem movesB_false_of {t : w32} (h1 : t ≠ MsgProp) (h2 : t ≠ MsgApp) (h3 : t ≠ MsgHeartbeat)
    (h4 : t ≠ MsgReadIndex) (h5 : t ≠ MsgTransferLeader) : movesB t = false := by
  simp only [movesB, decide_eq_false_iff_not]
  rintro (h | h | h | h | h) <;> contradiction

/-- The flag of a moving type is the node's. -/
theorem flag_moves {sz : Bool} {t : w32} (ht : movesB t = true) : (sz && movesB t) = sz := by
  simp [ht]

/-- The flag of another type is `false`. -/
theorem flag_nomoves {sz : Bool} {t : w32} (ht : movesB t = false) : (sz && movesB t) = false := by
  simp [ht]

/-- A weaker flag. -/
theorem msgInC_flag (sz sz' : Bool) (h : sz' = true → sz = true) (l : Loc) (dqe : DFrac) (st : MsgSt) :
    msgInC (GF := GF) sz l dqe st ⊢ msgInC sz' l dqe st := by
  unfold msgInC
  iintro ⟨%c, Hc, %H⟩
  iexists c
  iframe Hc
  ipureintro
  exact ⟨H.1, H.2.1, fun hs ht => H.2.2 (h hs) ht⟩

/-- A received message's pointer is not `nil`. -/
theorem msgInC_nn (sz : Bool) (l : Loc) (dqe : DFrac) (st : MsgSt) :
    msgInC (GF := GF) sz l dqe st ⊢ ⌜l ≠ null⌝ ∗ msgInC sz l dqe st := by
  unfold msgInC
  iintro ⟨%c, Hc, %H⟩
  unfold msgPtsCC
  icases Hc with ⟨%pty, %pto, %pfr, %pte, %plt, %pix, %pco, %pvo, %prj, %prh, %es, %els, %ps, %cs,
    %rs, %Hnn, Hc⟩
  isplitr
  · ipureintro; exact Hnn
  iexists c
  isplitl
  · iexists pty, pto, pfr, pte, plt, pix, pco, pvo, prj, prh, es, els, ps, cs, rs
    isplitr
    · ipureintro; exact Hnn
    iexact Hc
  · ipureintro; exact H

/-- At a moving type, the node's flag. -/
theorem msgInC_moves {sz : Bool} {t : w32} (ht : movesB t = true) (l : Loc) (dqe : DFrac)
    (st : MsgSt) : msgInC (GF := GF) (sz && movesB t) l dqe st ⊢ msgInC sz l dqe st := by
  rw [flag_moves ht]

/-- The context of a received message at a content is at most `entBytesMax` bytes under the flag
(unless a `MsgSnap`): what an echo of it (`handleHeartbeat`'s response) needs. -/
theorem msgInC_ctx (sz : Bool) (l : Loc) (dqe : DFrac) (st : MsgSt) :
    msgInC (GF := GF) sz l dqe st ⊢ msgInC sz l dqe st ∗
      ⌜sz = true → st.msg.Type' ≠ MsgSnap → st.ctx.length ≤ entBytesMax⌝ := by
  unfold msgInC
  iintro ⟨%c, Hc, %H⟩
  isplitl [Hc]
  · iexists c; iframe Hc; ipureintro; exact H
  ipureintro
  intro hs ht
  obtain ⟨Hm, -, Hz⟩ := H
  have h2 := (Hz hs ht).2.1
  rw [← Hm]
  simp only [MsgC.model, hdrBytes] at h2 ⊢
  omega

theorem ite_dfrac_halves (P : Prop) [Decidable P] :
    (if P then DFrac.own 1 else DFrac.discard) =
      (if P then dqh else DFrac.discard) • (if P then dqh else DFrac.discard) := by
  split
  · exact dqh_op.symm
  · rfl

/-- **Reading a received message at a content** through today's specs (the getters): half of it in
today's form (no capacity; the entries' slice at half the fraction), and what rebuilds it. -/
theorem msgInC_half (sz : Bool) (l : Loc) (P : Prop) [Decidable P] (st : MsgSt) :
    msgInC (GF := GF) sz l (if P then DFrac.own 1 else DFrac.discard) st ⊢
      msgPtsC l dqh (if P then dqh else DFrac.discard) false st ∗
        (msgPtsC l dqh (if P then dqh else DFrac.discard) false st -∗
          msgInC sz l (if P then DFrac.own 1 else DFrac.discard) st) := by
  unfold msgInC
  iintro ⟨%c, Hc, %H⟩
  obtain ⟨Hm, Hcs, Hz⟩ := H
  subst Hm
  have h := msgPtsCC_readE (GF := GF) l (needsCap c.model.msg) c Hcs
    (if P then dqh else DFrac.discard) (if P then dqh else DFrac.discard)
  rw [← ite_dfrac_halves P] at h
  icases h $$ Hc with ⟨Hh, Hback⟩
  iframe Hh
  iintro Hh
  iexists c
  isplitl
  · iapply Hback $$ Hh
  · ipureintro; exact ⟨rfl, Hcs, Hz⟩

/-- `m.To = new(r.lead)` (`stepFollower`'s forwards) on a message at a content. -/
theorem msgPtsCC_store_To (l : Loc) (dqe : DFrac) (cap : Bool) (c : MsgC) :
    msgPtsCC (GF := GF) l (DFrac.own 1) dqe cap c ⊢
      ∃ p : Loc, l.[raftpb.Message, go!"To"] ↦ p ∗
        (∀ (p' : Loc) (v : w64), l.[raftpb.Message, go!"To"] ↦ p' -∗ cellRO p' v -∗
          ∃ o : Option w64, msgPtsCC l (DFrac.own 1) dqe cap (.mk { c.f with to := o } c.resps) ∗
            ⌜o.getD (zero_val w64) = v⌝) := by
  unfold msgPtsCC
  iintro ⟨%pty, %pto, %pfr, %pte, %plt, %pix, %pco, %pvo, %prj, %prh, %es, %els, %ps, %cs, %rs,
    %Hnn, HTy, #cTy, HTo, #cTo, HFr, #cFr, HTe, #cTe, HLt, #cLt, HIx, #cIx, HCo, #cCo,
    HVo, #cVo, HRj, #cRj, HRh, #cRh, HEs, Hes, #Hents, Hcap, HSn, Hsn, HCx, #Hcx, HRs, Hrs, #Hpb⟩
  iexists pto
  iframe HTo
  iintro %p' %v HTo #cTo'
  icases cellRO_optCell' p' v $$ cTo' with ⟨%o, #cO, %Ho⟩
  iexists o
  isplitl
  · iexists pty, p', pfr, pte, plt, pix, pco, pvo, prj, prh, es, els, ps, cs, rs
    simp only [MsgC.f, MsgC.resps]
    isplitr
    · ipureintro; exact Hnn
    iframe
    iframe cTy cO cFr cTe cLt cIx cCo cVo cRj cRh Hents Hcx Hpb
  · ipureintro; exact Ho

/-- **A received message forwarded** (`stepFollower`: `m.To = new(r.lead)`, then `send`): at its
content, frozen, with its size, as raft holds the messages it sends (`msgOwnZ`). -/
theorem msgInC_store_To (sz : Bool) (l : Loc) (dqe : DFrac) (st : MsgSt)
    (hty : st.msg.Type' ≠ MsgSnap) :
    msgInC (GF := GF) sz l dqe st ⊢
      ∃ p : Loc, l.[raftpb.Message, go!"To"] ↦ p ∗
        (∀ (p' : Loc) (v : w64), l.[raftpb.Message, go!"To"] ↦ p' -∗ cellRO p' v -∗
          |==> msgOwnZ sz l (DFrac.own 1) { st with msg := { st.msg with To' := v } }) := by
  unfold msgInC
  iintro ⟨%c, Hc, %H⟩
  icases msgPtsCC_store_To l dqe _ c $$ Hc with ⟨%p, Hp, Hback⟩
  iexists p
  iframe Hp
  iintro %p' %v Hp #cv
  icases Hback $$ %p' %v Hp cv with ⟨%o, Hc, %Ho⟩
  imod msgPtsCC_freeze $$ Hc with Hc
  imodintro
  unfold msgOwnZ
  iexists _
  iframe Hc
  ipureintro
  obtain ⟨Hm, Hcs, Hsz⟩ := H
  obtain ⟨f, rs⟩ := c
  subst Hm
  refine ⟨?_, ⟨Hcs, fun h => absurd h hty⟩, fun hs ht => ?_⟩
  · simp only [MsgC.model, MsgC.f, MsgC.resps, MsgFC.msgM, Ho]
  · obtain ⟨h1, h2, h3, h4⟩ := Hsz hs hty
    exact ⟨h1, h2, h3, h4⟩

/-- (out_size C3) `m.From = new(r.id)` (`run` stamping a proposal) on a received message at a
content: its size kept. -/
theorem msgInC_store_From (sz : Bool) (l : Loc) (dqe : DFrac) (st : MsgSt) :
    msgInC (GF := GF) sz l dqe st ⊢
      ∃ p : Loc, l.[raftpb.Message, go!"From"] ↦ p ∗
        (∀ (p' : Loc) (v : w64), l.[raftpb.Message, go!"From"] ↦ p' -∗ cellRO p' v -∗
          msgInC sz l dqe { st with msg := { st.msg with From' := v } }) := by
  unfold msgInC
  iintro ⟨%c, Hc, %H⟩
  icases msgPtsCC_store_From l dqe _ c $$ Hc with ⟨%p, Hp, Hback⟩
  iexists p
  iframe Hp
  iintro %p' %v Hp #cv
  icases Hback $$ %p' %v Hp cv with ⟨%o, Hc, %Ho⟩
  iexists _
  iframe Hc
  ipureintro
  obtain ⟨Hm, Hcs, Hsz⟩ := H
  obtain ⟨f, rs⟩ := c
  subst Hm
  refine ⟨?_, Hcs, fun hs ht => ?_⟩
  · simp only [MsgC.model, MsgC.f, MsgC.resps, MsgFC.msgM, Ho]
  · obtain ⟨h1, h2, h3, h4⟩ := Hsz hs ht
    exact ⟨h1, h2, h3, h4⟩

/-- The `Entries` field out of a message at a content (`msgPtsC_acc_entries`'s content form): the
slice, its entry objects at their contents, and what closes it back. -/
theorem msgPtsCC_acc_entries (l : Loc) (dq dqe : DFrac) (cap : Bool) (c : MsgC) :
    msgPtsCC (GF := GF) l dq dqe cap c ⊢
      ∃ (es : GoSlice) (els : List Loc), ⌜l ≠ null⌝ ∗
        l.[raftpb.Message, go!"Entries"] ↦{dq} es ∗ es ↦*{dqe} els ∗
        ([∗list] p;e ∈ els;c.f.entries, entRoC p e) ∗
        (if cap then ownSliceCap Loc es (DFrac.own 1) else emp) ∗
        (∀ (els' : List Loc) (ents' : List EntryC) (cap' : Bool),
          l.[raftpb.Message, go!"Entries"] ↦{dq} es -∗ es ↦*{dqe} els' -∗
          ([∗list] p;e ∈ els';ents', entRoC p e) -∗
          (if cap' then ownSliceCap Loc es (DFrac.own 1) else emp) -∗
          msgPtsCC l dq dqe cap' (.mk { c.f with entries := ents' } c.resps)) := by
  unfold msgPtsCC
  iintro ⟨%pty, %pto, %pfr, %pte, %plt, %pix, %pco, %pvo, %prj, %prh, %es, %els, %ps, %cs, %rs,
    %Hnn, HTy, #cTy, HTo, #cTo, HFr, #cFr, HTe, #cTe, HLt, #cLt, HIx, #cIx, HCo, #cCo,
    HVo, #cVo, HRj, #cRj, HRh, #cRh, HEs, Hes, #Hents, Hcap, HSn, Hsn, HCx, #Hcx, HRs, Hrs, #Hpb⟩
  iexists es, els
  isplitr
  · ipureintro; exact Hnn
  iframe HEs Hes Hents Hcap
  iintro %els' %ents' %cap' HEs Hes #Hents' Hcap
  iexists pty, pto, pfr, pte, plt, pix, pco, pvo, prj, prh, es, els', ps, cs, rs
  simp only [MsgC.f, MsgC.resps]
  isplitr
  · ipureintro; exact Hnn
  iframe
  iframe cTy cTo cFr cTe cLt cIx cCo cVo cRj cRh Hents' Hcx Hpb

/-- A message `Step` received, off a proposal and of a type whose objects no step moves, as the
`stepX` specs take it (at the flag `false`). (Over any capacity flag `cap`, `msgIn`'s `needsCap
st.msg`, so that it applies to a `msgIn` unfolded by a generic `msgPtsC` lemma.) -/
theorem msgIn_nonprop {ml : Loc} {m : MessageM} {st : MsgSt} {cap b : Bool} (h : m.Type' ≠ MsgProp)
    (hm : movesB m.Type' = false := by movesB_tac) (hcap : cap = needsCap st.msg := by rfl) :
    msgPtsC (GF := GF) ml (DFrac.own 1) DFrac.discard cap st ⊢
      msgInC (b && movesB m.Type') ml
        (if m.Type' = MsgProp then DFrac.own 1 else DFrac.discard) st := by
  subst hcap
  simp only [h, ↓reduceIte, flag_nomoves hm]
  exact msgIn_msgInC ml DFrac.discard st

/-- `msgInC_half` at read-only entries. -/
theorem msgInC_halfD (sz : Bool) (l : Loc) (st : MsgSt) :
    msgInC (GF := GF) sz l DFrac.discard st ⊢
      msgPtsC l dqh DFrac.discard false st ∗
        (msgPtsC l dqh DFrac.discard false st -∗ msgInC sz l DFrac.discard st) := by
  have h := msgInC_half (GF := GF) sz l False st
  simp only [if_false] at h
  exact h

/-- `msgInC_half` at owned entries (a proposal). -/
theorem msgInC_halfO (sz : Bool) (l : Loc) (st : MsgSt) :
    msgInC (GF := GF) sz l (DFrac.own 1) st ⊢
      msgPtsC l dqh dqh false st ∗ (msgPtsC l dqh dqh false st -∗ msgInC sz l (DFrac.own 1) st) := by
  have h := msgInC_half (GF := GF) sz l True st
  simp only [if_true] at h
  exact h

/-- A received message read through `msgInC_halfD`, rebuilt and handed to a `stepX` callee (a
moving type off a proposal), at the callee's state's flag. -/
theorem msgInC_pass {ml : Loc} {m : MessageM} {st : MsgSt} {sz sz' : Bool}
    (h : m.Type' ≠ MsgProp) (hm : movesB m.Type' = true) (hs : sz' = true → sz = true) :
    (msgPtsC (GF := GF) ml dqh DFrac.discard false st -∗ msgInC sz ml DFrac.discard st) ∗
      msgPtsC ml dqh DFrac.discard false st ⊢
      msgInC (sz' && movesB m.Type') ml
        (if m.Type' = MsgProp then DFrac.own 1 else DFrac.discard) st := by
  iintro ⟨Hb, Hm⟩
  ihave Hm := Hb $$ Hm
  simp only [h, ↓reduceIte, flag_moves hm]
  iapply msgInC_flag sz sz' hs $$ Hm

/-- The same for a proposal. -/
theorem msgInC_passP {ml : Loc} {m : MessageM} {st : MsgSt} {sz sz' : Bool}
    (h : m.Type' = MsgProp) (hs : sz' = true → sz = true) :
    (msgPtsC (GF := GF) ml dqh dqh false st -∗ msgInC sz ml (DFrac.own 1) st) ∗
      msgPtsC ml dqh dqh false st ⊢
      msgInC (sz' && movesB m.Type') ml
        (if m.Type' = MsgProp then DFrac.own 1 else DFrac.discard) st := by
  iintro ⟨Hb, Hm⟩
  ihave Hm := Hb $$ Hm
  simp only [h, ↓reduceIte, flag_moves movesB_MsgProp]
  iapply msgInC_flag sz sz' hs $$ Hm

/-- (out_size C3) A received message at a content, off a proposal, of a type whose objects the step
moves (`movesB`), as the `stepX` specs take it. -/
theorem msgInC_nonprop {ml : Loc} {m : MessageM} {st : MsgSt} {sz : Bool} (h : m.Type' ≠ MsgProp)
    (hm : movesB m.Type' = true) :
    msgInC (GF := GF) sz ml DFrac.discard st ⊢
      msgInC (sz && movesB m.Type') ml
        (if m.Type' = MsgProp then DFrac.own 1 else DFrac.discard) st := by
  simp only [h, ↓reduceIte, flag_moves hm]; exact .rfl

/-- A proposal `Step` received, as the `stepX` specs take it. -/
theorem msgIn_prop {ml : Loc} {m : MessageM} {st : MsgSt} {sz : Bool} (h : m.Type' = MsgProp) :
    msgInC (GF := GF) sz ml (DFrac.own 1) st ⊢
      msgInC (sz && movesB m.Type') ml
        (if m.Type' = MsgProp then DFrac.own 1 else DFrac.discard) st := by
  simp only [h, ↓reduceIte, flag_moves movesB_MsgProp]; exact .rfl

/-- A received message in today's form, of a type whose objects no step moves, at a content
under any flag (`raft.Step`'s and the `stepX` specs' `s.gh.sn.sz && movesB m.Type'`). -/
theorem msgIn_toC {t : w32} {b : Bool} (hm : movesB t = false) (l : Loc) (dqe : DFrac) (st : MsgSt) :
    msgIn (GF := GF) l dqe st ⊢ msgInC (b && movesB t) l dqe st := by
  rw [flag_nomoves hm]; exact msgIn_msgInC l dqe st

/-- A message raft built, owned at a content (`msgOwnZ`), handed to `Step` as a received one (no
capacity needed: not a `MsgApp`). -/
theorem msgOwnZ_to_msgInC (sz : Bool) (l : Loc) (st : MsgSt) (hcap : needsCap st.msg = false) :
    msgOwnZ (GF := GF) sz l (DFrac.own 1) st ⊢ msgInC sz l DFrac.discard st := by
  unfold msgOwnZ msgInC
  iintro ⟨%c, Hc, %H⟩
  obtain ⟨Hm, Hok, Hz⟩ := H
  iexists c
  rw [hcap]
  iframe Hc
  ipureintro
  refine ⟨Hm, Hok.1, fun hs ht => Hz hs (by rw [Hm]; exact ht)⟩

/-- (out_size C3) A message at a content is not at `null`. -/
theorem msgPtsCC_nn (l : Loc) (dq dqe : DFrac) (cap : Bool) (c : MsgC) :
    msgPtsCC (GF := GF) l dq dqe cap c ⊢ ⌜l ≠ null⌝ ∗ msgPtsCC l dq dqe cap c := by
  iintro H
  ihave ⟨%es, %els, %Hnn, HEs, Hes, Hents, Hcap, Hback⟩ := msgPtsCC_acc_entries l dq dqe cap c $$ H
  isplitr
  · ipureintro; exact Hnn
  ihave H := Hback $$ %els %c.f.entries %cap HEs Hes Hents Hcap
  obtain ⟨f, rs⟩ := c
  iExactEq H; rfl

/-- (out_size C3) A message at a content with its capacity holds any capacity flag. -/
theorem msgPtsCC_cap_any (l : Loc) (dq dqe : DFrac) (cap : Bool) (c : MsgC) :
    msgPtsCC (GF := GF) l dq dqe true c ⊢ msgPtsCC l dq dqe cap c := by
  iintro H
  ihave ⟨%es, %els, -, HEs, Hes, Hents, Hcap, Hback⟩ := msgPtsCC_acc_entries l dq dqe true c $$ H
  ihave H := Hback $$ %els %c.f.entries %cap HEs Hes Hents [Hcap]
  · cases cap
    · simp only [Bool.false_eq_true, ↓reduceIte]; iempintro
    · iexact Hcap
  obtain ⟨f, rs⟩ := c
  iExactEq H; rfl

/-- (out_size C3) A message at a content, its `Entries` elements frozen (`msgPtsC_persist_els`). -/
theorem msgPtsCC_persist_els (l : Loc) (dq dqe : DFrac) (cap : Bool) (c : MsgC) :
    msgPtsCC (GF := GF) l dq dqe cap c ⊢ |==> msgPtsCC l dq DFrac.discard cap c := by
  unfold msgPtsCC
  iintro ⟨%pty, %pto, %pfr, %pte, %plt, %pix, %pco, %pvo, %prj, %prh, %es, %els, %ps, %cs, %rs,
    %Hnn, HTy, #cTy, HTo, #cTo, HFr, #cFr, HTe, #cTe, HLt, #cLt, HIx, #cIx, HCo, #cCo,
    HVo, #cVo, HRj, #cRj, HRh, #cRh, HEs, Hes, #Hents, Hcap, HSn, Hsn, HCx, #Hcx, HRs, Hrs, #Hpb⟩
  imod (ownSlice_dfractional (GF := GF) _ _).dfractional_persist _ $$ Hes with #Hes
  imodintro
  iexists pty, pto, pfr, pte, plt, pix, pco, pvo, prj, prh, es, els, ps, cs, rs
  isplitr
  · ipureintro; exact Hnn
  iframe
  iframe cTy cTo cFr cTe cLt cIx cCo cVo cRj cRh Hes Hents Hcx Hpb

/-- (out_size C3) A received message at a content, from its parts. -/
theorem msgInC_of_CC (sz : Bool) (l : Loc) (dqe : DFrac) (c : MsgC) (st : MsgSt) (hm : c.model = st)
    (hcs : c.csUfNil) (hsz : sz = true → st.msg.Type' ≠ MsgSnap → msgSizeOk c) :
    msgPtsCC (GF := GF) l (DFrac.own 1) dqe (needsCap st.msg) c ⊢ msgInC sz l dqe st := by
  iintro H
  unfold msgInC
  iexists c
  iframe H
  ipureintro; exact ⟨hm, hcs, hsz⟩

/-- (out_size C3) **A message raft builds with entries, handed to `Step`** (`RawNode.Propose`,
`ReadIndex`, `ProposeConfChange`): a fresh literal with no snapshot, no responses and no unknown
fields, its entries at `entRZ sz` (each within the bound when `sz`), its context within the bound,
and few enough entries for the framed sum (`2^36`): a received message at a content of bounded
size (`msgInC sz`), no capacity needed (not a `MsgApp`). -/
theorem msgInC_of_struct (sz : Bool) (l : Loc) (v : raftpb.Message) (dqe : DFrac) (els : List Loc)
    (ms : MsgSt) (E : CoPset) (Hu : v.unknownFields' = slice.nil) (Hsn : v.Snapshot' = null)
    (hs : ms.snap = none) (hr : ms.resps = []) (hcap : needsCap ms.msg = false)
    (Hsz : sz = true → ms.ctx.length ≤ entBytesMax ∧ ms.ents.length * (entBytesMax + 64) ≤ 2 ^ 36) :
    (l ↦ v ∗ cellRO v.Type' ms.msg.Type' ∗ cellRO v.To' ms.msg.To' ∗
      cellRO v.From' ms.msg.From' ∗ cellRO v.Term' ms.msg.Term' ∗
      cellRO v.LogTerm' ms.msg.LogTerm' ∗ cellRO v.Index' ms.msg.Index' ∗
      cellRO v.Commit' ms.msg.Commit' ∗ cellRO v.Vote' ms.msg.Vote' ∗
      cellRO v.Reject' ms.msg.Reject' ∗ cellRO v.RejectHint' ms.msg.RejectHint' ∗
      v.Entries' ↦*{dqe} els ∗ ([∗list] p;e ∈ els;ms.ents, entRZ sz p e) ∗
      v.Context' ↦*□ ms.ctx ∗ v.Responses' ↦* ([] : List Loc) : IProp GF) ⊢
      |={E}=> msgInC sz l dqe ms := by
  iintro ⟨Hl, #cTy, #cTo, #cFr, #cTe, #cLt, #cIx, #cCo, #cVo, #cRj, #cRh, Hes, #Hents, #Hcx, Hrs⟩
  ihave ⟨%oTy, #oTy, %hTy⟩ := cellRO_optCell _ _ $$ cTy
  ihave ⟨%oTo, #oTo, %hTo⟩ := cellRO_optCell _ _ $$ cTo
  ihave ⟨%oFr, #oFr, %hFr⟩ := cellRO_optCell _ _ $$ cFr
  ihave ⟨%oTe, #oTe, %hTe⟩ := cellRO_optCell _ _ $$ cTe
  ihave ⟨%oLt, #oLt, %hLt⟩ := cellRO_optCell _ _ $$ cLt
  ihave ⟨%oIx, #oIx, %hIx⟩ := cellRO_optCell _ _ $$ cIx
  ihave ⟨%oCo, #oCo, %hCo⟩ := cellRO_optCell _ _ $$ cCo
  ihave ⟨%oVo, #oVo, %hVo⟩ := cellRO_optCell _ _ $$ cVo
  ihave ⟨%oRj, #oRj, %hRj⟩ := cellRO_optCell _ _ $$ cRj
  ihave ⟨%oRh, #oRh, %hRh⟩ := cellRO_optCell _ _ $$ cRh
  ihave ⟨%oCx, #oCx, %hCx⟩ := ownSlice_bytesC _ _ $$ Hcx
  ihave ⟨%cs, #Hcs, %hcs⟩ := entsBigZ_entsBigC sz els ms.ents $$ Hents
  imod msgPtsCC_of_struct l v dqe false els
      ⟨oTy, oTo, oFr, oTe, oLt, oIx, cs, oCo, oVo, none, oRj, oRh, oCx, []⟩ E Hu rfl
      $$ [Hl Hes Hrs] with Hm
  · iframe Hl Hes Hrs oTy oTo oFr oTe oLt oIx oCo oVo oRj oRh oCx Hcs
    simp only [Bool.false_eq_true, ↓reduceIte, snapOptCC]
    isplitl []; · iempintro
    ipureintro; exact Hsn
  imodintro
  unfold msgInC
  iexists _
  rw [hcap]
  iframe Hm
  ipureintro
  obtain ⟨mm, ents, snap, ctx, resps⟩ := ms
  simp only at hs hr hcs hCx Hsz hTy hTo hFr hTe hLt hIx hCo hVo hRj hRh
  subst hs hr
  obtain ⟨hcs1, hcs2⟩ := hcs
  refine ⟨?_, ?_, fun hsz _ => ?_⟩
  · simp only [MsgC.model, MsgC.f, MsgC.resps, MsgFC.msgM, List.map_nil, Option.map_none, hcs1, hCx,
      hTy, hTo, hFr, hTe, hLt, hIx, hCo, hVo, hRj, hRh]
  · intro s hs'; simp [MsgC.f] at hs'
  · obtain ⟨hc, hn⟩ := Hsz hsz
    have he : ∀ e ∈ cs, entBytes e ≤ entBytesMax := fun e he => hcs2 hsz e he
    refine ⟨rfl, ?_, he, ?_⟩
    · simp only [hdrBytes, MsgC.f, optSnapSize, List.length_nil, Nat.add_zero, hCx]; exact hc
    · simp only [MsgC.f]
      have hlen : cs.length = ents.length := by rw [← hcs1, List.length_map]
      have : (cs.map (fun e => entBytes e + 64)).sum ≤ cs.length * (entBytesMax + 64) := by
        clear hlen hcs1 hcs2
        induction cs with
        | nil => simp
        | cons c cs ih =>
          simp only [List.map_cons, List.sum_cons, List.length_cons]
          have h1 := he c (by simp)
          have h2 := ih (fun e he' => he e (by simp [he']))
          rw [Nat.add_mul, Nat.one_mul]; omega
      rw [hlen] at this; omega

/-- (out_size C3, step 3) A frozen message at a content is persistent (a stored read request). -/
instance msgOwnZ_discard_persistent (sz : Bool) (l : Loc) (st : MsgSt) :
    Persistent (msgOwnZ (GF := GF) sz l DFrac.discard st) := by
  unfold msgOwnZ; infer_instance

/-- (out_size C3, step 3) **A received message stored** (`stepLeader`'s read requests, queued or
pending): frozen at its content, with its size. -/
theorem msgInC_freeze (sz : Bool) (l : Loc) (dqe : DFrac) (st : MsgSt)
    (hty : st.msg.Type' ≠ MsgSnap) :
    msgInC (GF := GF) sz l dqe st ⊢ |==> msgOwnZ sz l DFrac.discard st := by
  unfold msgInC
  iintro ⟨%c, Hc, %H⟩
  imod msgPtsCC_freeze $$ Hc with Hc
  imod msgPtsCC_persist $$ Hc with Hc
  imodintro
  unfold msgOwnZ
  iexists c
  iframe Hc
  ipureintro
  obtain ⟨Hm, Hcs, Hsz⟩ := H
  refine ⟨Hm, ⟨Hcs, fun h => ?_⟩, fun hs ht => ?_⟩
  · exact absurd (show st.msg.Type' = MsgSnap by rw [← Hm]; exact h) hty
  · rw [Hm] at ht; exact Hsz hs ht

/-- (out_size C3, step 3) **A message raft builds from contents** (`responseToReadIndexReq`'s
`MsgReadIndexResp`, sharing a stored request's entries): a fresh literal with no snapshot, no
responses and no unknown fields, its entries slice read-only over objects at the contents `cs`: at a
content of bounded size when, under the flag and off a `MsgSnap`, its context and entries are. -/
theorem msgOwnZ_of_structC (sz : Bool) (l : Loc) (v : raftpb.Message) (els : List Loc)
    (cs : List EntryC) (mm : MessageM) (ctx : List w8) (E : CoPset)
    (Hu : v.unknownFields' = slice.nil) (Hsn : v.Snapshot' = null)
    (Hsz : sz = true → mm.Type' ≠ MsgSnap → ctx.length ≤ entBytesMax ∧
      (∀ e ∈ cs, entBytes e ≤ entBytesMax) ∧ (cs.map (fun e => entBytes e + 64)).sum ≤ 2 ^ 36) :
    (l ↦ v ∗ cellRO v.Type' mm.Type' ∗ cellRO v.To' mm.To' ∗
      cellRO v.From' mm.From' ∗ cellRO v.Term' mm.Term' ∗
      cellRO v.LogTerm' mm.LogTerm' ∗ cellRO v.Index' mm.Index' ∗
      cellRO v.Commit' mm.Commit' ∗ cellRO v.Vote' mm.Vote' ∗
      cellRO v.Reject' mm.Reject' ∗ cellRO v.RejectHint' mm.RejectHint' ∗
      v.Entries' ↦*□ els ∗ ([∗list] p;e ∈ els;cs, entRoC p e) ∗
      v.Context' ↦*□ ctx ∗ v.Responses' ↦* ([] : List Loc) : IProp GF) ⊢
      |={E}=> msgOwnZ sz l (DFrac.own 1) ⟨mm, cs.map EntryC.model, none, ctx, []⟩ := by
  iintro ⟨Hl, #cTy, #cTo, #cFr, #cTe, #cLt, #cIx, #cCo, #cVo, #cRj, #cRh, Hes, #Hents, #Hcx, Hrs⟩
  ihave ⟨%oTy, #oTy, %hTy⟩ := cellRO_optCell _ _ $$ cTy
  ihave ⟨%oTo, #oTo, %hTo⟩ := cellRO_optCell _ _ $$ cTo
  ihave ⟨%oFr, #oFr, %hFr⟩ := cellRO_optCell _ _ $$ cFr
  ihave ⟨%oTe, #oTe, %hTe⟩ := cellRO_optCell _ _ $$ cTe
  ihave ⟨%oLt, #oLt, %hLt⟩ := cellRO_optCell _ _ $$ cLt
  ihave ⟨%oIx, #oIx, %hIx⟩ := cellRO_optCell _ _ $$ cIx
  ihave ⟨%oCo, #oCo, %hCo⟩ := cellRO_optCell _ _ $$ cCo
  ihave ⟨%oVo, #oVo, %hVo⟩ := cellRO_optCell _ _ $$ cVo
  ihave ⟨%oRj, #oRj, %hRj⟩ := cellRO_optCell _ _ $$ cRj
  ihave ⟨%oRh, #oRh, %hRh⟩ := cellRO_optCell _ _ $$ cRh
  ihave ⟨%oCx, #oCx, %hCx⟩ := ownSlice_bytesC _ _ $$ Hcx
  imod msgPtsCC_of_struct l v DFrac.discard false els
      ⟨oTy, oTo, oFr, oTe, oLt, oIx, cs, oCo, oVo, none, oRj, oRh, oCx, []⟩ E Hu rfl
      $$ [Hl Hes Hrs] with Hm
  · iframe Hl Hes Hrs oTy oTo oFr oTe oLt oIx oCo oVo oRj oRh oCx Hents
    simp only [Bool.false_eq_true, ↓reduceIte, snapOptCC]
    isplitl []; · iempintro
    ipureintro; exact Hsn
  imodintro
  unfold msgOwnZ
  iexists _
  iframe Hm
  ipureintro
  refine ⟨?_, ⟨fun s hs => by simp [MsgC.f] at hs, fun _ => rfl⟩, fun hsz hty => ?_⟩
  · simp only [MsgC.model, MsgC.f, MsgC.resps, MsgFC.msgM, List.map_nil, Option.map_none, hCx,
      hTy, hTo, hFr, hTe, hLt, hIx, hCo, hVo, hRj, hRh]
  · have hty' : mm.Type' ≠ MsgSnap := by rw [← hTy]; exact hty
    obtain ⟨hc, he, hs⟩ := Hsz hsz hty'
    refine ⟨rfl, ?_, he, hs⟩
    simp only [hdrBytes, MsgC.f, optSnapSize, List.length_nil, Nat.add_zero, hCx]; exact hc

end recv

end EtcdGrove
end Perennial
