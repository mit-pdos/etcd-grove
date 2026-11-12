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
def msgSzC (sz : Bool) (c : MsgC) : Prop :=
  c.sentOk ∧ (sz = true → c.model.msg.Type' ≠ MsgSnap → msgSizeOk c)

/-- **A message raft holds, at a content** (see the file header). -/
def msgOwnZ (sz : Bool) (l : Loc) (dq : DFrac) (st : MsgSt) : IProp GF :=
  iprop(∃ c : MsgC, msgPtsCC l dq DFrac.discard false c ∗ ⌜c.model = st ∧ msgSzC sz c⌝)

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
    (Hst : st.resps = [] ∧ (st.msg.Type' ≠ MsgSnap →
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
  refine ⟨Hmod, ⟨Hcs, fun _ => Hu⟩, fun _ hty => ?_⟩
  rw [Hmod] at hty
  obtain ⟨h1, h2, h3, h4⟩ := (⟨Hst.1, Hst.2 hty⟩ : _ ∧ _)
  exact msgSizeOk_of_lit c Hu (by rw [Hmod]; exact h2) (by rw [Hmod]; exact h3)
    (by rw [Hmod]; exact h1) (by rw [Hmod]; exact h4)

/-- **TEMPORARY (out_size C3, branch only; gone before C3 lands).** A message raft holds in today's
form (not a `MsgSnap`), at a content of bounded size under any flag. The `sorry` is the size fact
alone (`msgSizeOk` under `sz`), for the senders whose bound waits on P4 or on the read requests at
contents: `maybeSendAppend` (the `MsgApp` sum), `stepFollower`'s three forwards (received:
`msgInC`), `sendMsgReadIndexResponse` and `stepLeader`'s `MsgReadIndexResp` (the stored request's
entries), `sendHeartbeat` and `handleHeartbeat` (the contexts). Listed in the handoff. -/
theorem msgOwnZ_sized_TODO (sz : Bool) (l : Loc) (dq : DFrac) (st : MsgSt)
    (hty : st.msg.Type' ≠ MsgSnap) :
    msgOwn (GF := GF) l dq st ⊢ msgOwnZ sz l dq st := by
  iintro H
  ihave H := msgOwnZ_of_snapUf l dq st $$ [H]
  · iframe H; unfold snapUf snapUfT; ileft; ipureintro; exact hty
  unfold msgOwnZ
  icases H with ⟨%c, Hc, %Hok⟩
  iexists c
  iframe Hc
  ipureintro
  exact ⟨Hok.1, Hok.2.1, fun _ _ => sorry⟩

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

end EtcdGrove
end Perennial
