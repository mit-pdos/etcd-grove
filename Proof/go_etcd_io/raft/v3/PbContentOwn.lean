/-
**Owned objects at their wire content** (raft-entsize §2 step 1, 2026-11-09): the content form of
today's `msgPtsC` (`InvPb.lean`), `msgPtsCC l dq dqe cap c`, with its entries slice's fraction `dqe`
and capacity flag `cap` carried through, and the equivalence

  `msgPtsC l dq dqe cap st ⊣⊢ ∃ c, msgPtsCC l dq dqe cap c ∗ ⌜c.model = st ∧ c.csUfNil⌝`

(`msgPtsC_iff_CC`), so that today's users are unaffected. Corrections to the Scope's §2
(accepted by etcd-grove-81, 2026-11-09): the equivalence needs `csUfNil` (today's `csPts` fixes the
`ConfState`'s unknown fields to none); the snapshot is owned at `dq` (`msgPtsC`'s `snapOpt ps dq`,
which `createMergedSnapshotMessage` writes through), so its content forms are owned too
(`snapOptCC`, `smOptCC`, `csOptCC`, with `bytesCC` for its `Data`); the responses are pinned as
pointers only (`msgPtsC` holds only those; `msgSizeOk` requires `resps = []`).

The entries stay frozen (`entRoC`, as `msgPtsC`'s `entRO`) and so does the `Context` (`bytesC`, as
`msgPtsC`'s `cs ↦*□`). Stage A's `msgRoC` is the frozen (`discard`) form.
-/
module

public import Proof.go_etcd_io.raft.v3.PbContent

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

/-- A blank message content (no field set, no responses): the content of a response, which an
owned message pins as a pointer only. -/
def MsgC.blank [GooseExts] : MsgC :=
  .mk ⟨none, none, none, none, none, none, [], none, none, none, none, none, none, []⟩ []

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- A `bytes` field owned at `dq`: `nil`, or a non-nil slice holding the bytes at `dq`. -/
def bytesCC (ds : GoSlice) (dq : DFrac) : Option (List w8) → IProp GF
  | none => iprop(⌜ds = slice.nil⌝)
  | some bs => iprop(⌜ds ≠ slice.nil⌝ ∗ ds ↦*{dq} bs)

/-- **A `*ConfState` at `dq` holding exactly `c`** (`csPts`'s content form; `al`: `AutoLeave` set). -/
def csPtsCC (p : Loc) (dq : DFrac) (c : CSC) (al : Bool) : IProp GF :=
  iprop(∃ (sv sl so sn : GoSlice) (pa : Loc),
    ⌜p ≠ null⌝ ∗
    p.[raftpb.ConfState, go!"Voters"] ↦{dq} sv ∗ sv ↦*{dq} c.voters ∗
    p.[raftpb.ConfState, go!"Learners"] ↦{dq} sl ∗ sl ↦*{dq} c.learners ∗
    p.[raftpb.ConfState, go!"VotersOutgoing"] ↦{dq} so ∗ so ↦*{dq} c.votersOutgoing ∗
    p.[raftpb.ConfState, go!"LearnersNext"] ↦{dq} sn ∗ sn ↦*{dq} c.learnersNext ∗
    p.[raftpb.ConfState, go!"AutoLeave"] ↦{dq} pa ∗ optCell pa c.autoLeave ∗
      ⌜al = true → pa ≠ null⌝ ∗
    pbMsg raftpb.ConfState p c.uf)

/-- A snapshot's nested conf state at its content (`csOptA`'s form). -/
def csOptCC (p : Loc) (dq : DFrac) : Option CSC → IProp GF
  | none => iprop(⌜p = null⌝)
  | some c => iprop(csPtsCC p dq c false ∨ csPtsCC p DFrac.discard c true)

/-- **A `*SnapshotMetadata` at `dq` holding exactly `m`** (`smPts`'s content form). -/
def smPtsCC (p : Loc) (dq : DFrac) (m : SnapMetaC) : IProp GF :=
  iprop(∃ (pc pi pt : Loc),
    ⌜p ≠ null⌝ ∗
    p.[raftpb.SnapshotMetadata, go!"ConfState"] ↦{dq} pc ∗ csOptCC pc dq m.confState ∗
    p.[raftpb.SnapshotMetadata, go!"Index"] ↦{dq} pi ∗ optCell pi m.index ∗
    p.[raftpb.SnapshotMetadata, go!"Term"] ↦{dq} pt ∗ optCell pt m.term ∗
    pbMsg raftpb.SnapshotMetadata p m.uf)

def smOptCC (p : Loc) (dq : DFrac) : Option SnapMetaC → IProp GF
  | none => iprop(⌜p = null⌝)
  | some m => smPtsCC p dq m

/-- **A `*Snapshot` at `dq` holding exactly `s`** (`ownSnapM`'s content form). -/
def ownSnapCC (p : Loc) (dq : DFrac) (s : SnapC) : IProp GF :=
  iprop(∃ (ds : GoSlice) (pm : Loc),
    ⌜p ≠ null⌝ ∗
    p.[raftpb.Snapshot, go!"Data"] ↦{dq} ds ∗ bytesCC ds dq s.data ∗
    p.[raftpb.Snapshot, go!"Metadata"] ↦{dq} pm ∗ smOptCC pm dq s.metadata ∗
    pbMsg raftpb.Snapshot p s.uf)

def snapOptCC (p : Loc) (dq : DFrac) : Option SnapC → IProp GF
  | none => iprop(⌜p = null⌝)
  | some s => ownSnapCC p dq s

/-- **A `*Message` at `dq` holding exactly the content `c`** (raft-entsize §2: the one name for
content ownership; the content form of `msgPtsC l dq dqe cap`): its scalars at their presences, its
entries slice at `dqe` with each entry frozen at its content (and the slice's capacity if `cap`),
its snapshot owned at `dq` at its content, its `Context` frozen at its presence, its responses'
pointers, and its unknown fields. -/
def msgPtsCC (l : Loc) (dq dqe : DFrac) (cap : Bool) (c : MsgC) : IProp GF :=
  iprop(∃ (pty pto pfr pte plt pix pco pvo prj prh : Loc) (es : GoSlice) (els : List Loc)
      (ps : Loc) (cs rs : GoSlice),
    ⌜l ≠ null⌝ ∗
    l.[raftpb.Message, go!"Type"] ↦{dq} pty ∗ optCell pty c.f.type ∗
    l.[raftpb.Message, go!"To"] ↦{dq} pto ∗ optCell pto c.f.to ∗
    l.[raftpb.Message, go!"From"] ↦{dq} pfr ∗ optCell pfr c.f.frm ∗
    l.[raftpb.Message, go!"Term"] ↦{dq} pte ∗ optCell pte c.f.term ∗
    l.[raftpb.Message, go!"LogTerm"] ↦{dq} plt ∗ optCell plt c.f.logTerm ∗
    l.[raftpb.Message, go!"Index"] ↦{dq} pix ∗ optCell pix c.f.index ∗
    l.[raftpb.Message, go!"Commit"] ↦{dq} pco ∗ optCell pco c.f.commit ∗
    l.[raftpb.Message, go!"Vote"] ↦{dq} pvo ∗ optCell pvo c.f.vote ∗
    l.[raftpb.Message, go!"Reject"] ↦{dq} prj ∗ optCell prj c.f.reject ∗
    l.[raftpb.Message, go!"RejectHint"] ↦{dq} prh ∗ optCell prh c.f.rejectHint ∗
    l.[raftpb.Message, go!"Entries"] ↦{dq} es ∗ es ↦*{dqe} els ∗
      ([∗list] p;e ∈ els;c.f.entries, entRoC p e) ∗
      (if cap then ownSliceCap Loc es (DFrac.own 1) else emp) ∗
    l.[raftpb.Message, go!"Snapshot"] ↦{dq} ps ∗ snapOptCC ps dq c.f.snapshot ∗
    l.[raftpb.Message, go!"Context"] ↦{dq} cs ∗ bytesC cs c.f.context ∗
    l.[raftpb.Message, go!"Responses"] ↦{dq} rs ∗ rs ↦*{dq} c.resps.map Prod.fst ∗
    pbMsg raftpb.Message l c.f.uf)

/-! ### From today's form to the content form -/

theorem ownSlice_bytesCC (ds : GoSlice) (dq : DFrac) (xs : List w8) :
    (ds ↦*{dq} xs : IProp GF) ⊢ ∃ o : Option (List w8), bytesCC ds dq o ∗ ⌜o.getD [] = xs⌝ := by
  iintro H
  by_cases hn : ds = slice.nil
  · subst hn
    ihave %Hl := ownSlice_len _ _ _ $$ H
    have hx : xs = [] := List.eq_nil_of_length_eq_zero (by rw [Hl.1]; rfl)
    subst hx
    iexists none
    simp only [bytesCC, Option.getD_none]
    ipureintro; simp
  · iexists (some xs)
    simp only [bytesCC, Option.getD_some]
    iframe H
    ipureintro; simpa using hn

theorem csPts_csPtsCC (p : Loc) (dq : DFrac) (c : ConfStateM) (al : Bool) :
    csPts (GF := GF) p dq c al ⊢ ∃ cc : CSC, csPtsCC p dq cc al ∗ ⌜cc.model = c ∧ cc.uf = []⌝ := by
  iunfold csPts
  iintro ⟨%sv, %sl, %so, %sn, %pa, %Hnn, HV, Hv, HL, Hl, HO, Ho, HN, Hn, HA, #cA, %Hal, #Hpb⟩
  ihave ⟨%oA, #oA', %hA⟩ := cellRO_optCell pa c.AutoLeave' $$ cA
  iexists ⟨c.Voters', c.Learners', c.VotersOutgoing', c.LearnersNext', oA, []⟩
  unfold csPtsCC
  isplitl
  · iexists sv, sl, so, sn, pa
    iframe HV Hv HL Hl HO Ho HN Hn HA oA' Hpb
    ipureintro; exact ⟨Hnn, Hal⟩
  ipureintro
  refine ⟨?_, rfl⟩
  obtain ⟨a, b, d, e, f⟩ := c
  simp only [CSC.model] at *
  rw [hA]

theorem csOptA_csOptCC (p : Loc) (dq : DFrac) (c : ConfStateM) :
    csOptA (GF := GF) p dq c ⊢
      ∃ o : Option CSC, csOptCC p dq o ∗
        ⌜(o.map CSC.model).getD csZero = c ∧ ∀ cc ∈ o, cc.uf = []⌝ := by
  unfold csOptA
  iintro (%H | H | H)
  · iexists none
    simp only [csOptCC, Option.map_none, Option.getD_none]
    ipureintro; exact ⟨H.1, H.2.symm, by simp⟩
  · ihave ⟨%cc, Hc, %hc⟩ := csPts_csPtsCC p dq c false $$ H
    iexists (some cc)
    simp only [csOptCC, Option.map_some, Option.getD_some]
    isplitl
    · ileft; iexact Hc
    ipureintro; exact ⟨hc.1, by simp [hc.2]⟩
  · ihave ⟨%cc, Hc, %hc⟩ := csPts_csPtsCC p DFrac.discard c true $$ H
    iexists (some cc)
    simp only [csOptCC, Option.map_some, Option.getD_some]
    isplitl
    · iright; iexact Hc
    ipureintro; exact ⟨hc.1, by simp [hc.2]⟩

theorem smPts_smPtsCC (p : Loc) (dq : DFrac) (md : SnapshotMetadataM) :
    smPts (GF := GF) p dq md ⊢
      ∃ m : SnapMetaC, smPtsCC p dq m ∗ ⌜m.model = md ∧ ∀ cs ∈ m.confState, cs.uf = []⌝ := by
  iunfold smPts
  iintro ⟨%pc, %pi, %pt, %uf, %Hnn, HC, Hc, HI, #cI, HT, #cT, #Hpb⟩
  ihave ⟨%oC, oC', %hC⟩ := csOptA_csOptCC pc dq md.ConfState' $$ Hc
  ihave ⟨%oI, #oI', %hI⟩ := cellRO_optCell pi md.Index' $$ cI
  ihave ⟨%oT, #oT', %hT⟩ := cellRO_optCell pt md.Term' $$ cT
  iexists ⟨oC, oI, oT, uf⟩
  unfold smPtsCC
  isplitl
  · iexists pc, pi, pt
    iframe HC oC' HI oI' HT oT' Hpb
    ipureintro; exact Hnn
  ipureintro
  refine ⟨?_, hC.2⟩
  obtain ⟨a, b, d⟩ := md
  simp only [SnapMetaC.model] at *
  rw [hC.1, hI, hT]

theorem smOpt_smOptCC (p : Loc) (dq : DFrac) (md : SnapshotMetadataM) :
    smOpt (GF := GF) p dq md ⊢
      ∃ o : Option SnapMetaC, smOptCC p dq o ∗
        ⌜(o.map SnapMetaC.model).getD metaZero = md ∧ ∀ m ∈ o, ∀ cs ∈ m.confState, cs.uf = []⌝ := by
  unfold smOpt
  iintro (%H | H)
  · iexists none
    simp only [smOptCC, Option.map_none, Option.getD_none]
    ipureintro; exact ⟨H.1, H.2.symm, by simp⟩
  · ihave ⟨%m, Hm, %hm⟩ := smPts_smPtsCC p dq md $$ H
    iexists (some m)
    simp only [smOptCC, Option.map_some, Option.getD_some]
    iframe Hm; ipureintro; exact ⟨hm.1, by simpa using hm.2⟩

theorem snapOpt_snapOptCC (p : Loc) (dq : DFrac) (o : Option SnapshotM) :
    snapOpt (GF := GF) p dq o ⊢
      ∃ oc : Option SnapC, snapOptCC p dq oc ∗
        ⌜oc.map SnapC.model = o ∧ ∀ s ∈ oc, ∀ m ∈ s.metadata, ∀ cs ∈ m.confState, cs.uf = []⌝ := by
  cases o with
  | none =>
    simp only [snapOpt]
    iintro %H
    iexists none
    simp only [snapOptCC, Option.map_none]
    ipureintro; simpa using H
  | some s =>
    simp only [snapOpt]
    iunfold ownSnapM
    iintro ⟨%ds, %pm, %uf, %Hnn, HD, Hd, HM, Hm, #Hpb⟩
    ihave ⟨%oD, oD', %hD⟩ := ownSlice_bytesCC ds dq s.Data' $$ Hd
    ihave ⟨%oM, oM', %hM⟩ := smOpt_smOptCC pm dq s.Metadata' $$ Hm
    iexists (some ⟨oD, oM, uf⟩)
    simp only [snapOptCC, Option.map_some]
    unfold ownSnapCC
    isplitl
    · iexists ds, pm
      iframe HD oD' HM oM' Hpb
      ipureintro; exact Hnn
    ipureintro
    refine ⟨?_, by simpa using hM.2⟩
    obtain ⟨a, b⟩ := s
    simp only [SnapC.model] at *
    rw [hD, hM.1]

/-! ### From the content form to today's form -/

theorem bytesCC_own (ds : GoSlice) (dq : DFrac) (o : Option (List w8)) :
    bytesCC (GF := GF) ds dq o ⊢ ds ↦*{dq} o.getD [] := by
  cases o with
  | none =>
    unfold bytesCC; iintro %h; subst h
    simp only [Option.getD_none]
    iapply ownSlice_nil
  | some bs =>
    simp only [bytesCC, Option.getD_some]
    iintro ⟨-, H⟩; iexact H

theorem csPtsCC_csPts (p : Loc) (dq : DFrac) (c : CSC) (al : Bool) (h : c.uf = []) :
    csPtsCC (GF := GF) p dq c al ⊢ csPts p dq c.model al := by
  unfold csPtsCC
  iintro ⟨%sv, %sl, %so, %sn, %pa, %Hnn, HV, Hv, HL, Hl, HO, Ho, HN, Hn, HA, #cA, %Hal, #Hpb⟩
  rw [h]
  ihave #cA' := optCell_cellRO pa c.autoLeave $$ cA
  unfold csPts
  iexists sv, sl, so, sn, pa
  simp only [CSC.model]
  iframe HV Hv HL Hl HO Ho HN Hn HA cA' Hpb
  ipureintro; exact ⟨Hnn, Hal⟩

theorem csOptCC_csOptA (p : Loc) (dq : DFrac) (o : Option CSC) (h : ∀ cs ∈ o, cs.uf = []) :
    csOptCC (GF := GF) p dq o ⊢ csOptA p dq ((o.map CSC.model).getD csZero) := by
  cases o with
  | none =>
    simp only [csOptCC, csOptA, Option.map_none, Option.getD_none]
    iintro %Hp
    ileft; ipureintro; exact ⟨Hp, rfl⟩
  | some cs =>
    simp only [csOptCC, csOptA, Option.map_some, Option.getD_some]
    iintro (H | H)
    · iright; ileft
      iapply csPtsCC_csPts p dq cs false (h cs rfl) $$ H
    · iright; iright
      iapply csPtsCC_csPts p DFrac.discard cs true (h cs rfl) $$ H

theorem smPtsCC_smPts (p : Loc) (dq : DFrac) (m : SnapMetaC) (h : ∀ cs ∈ m.confState, cs.uf = []) :
    smPtsCC (GF := GF) p dq m ⊢ smPts p dq m.model := by
  unfold smPtsCC
  iintro ⟨%pc, %pi, %pt, %Hnn, HC, Hc, HI, #cI, HT, #cT, #Hpb⟩
  ihave #cI' := optCell_cellRO pi m.index $$ cI
  ihave #cT' := optCell_cellRO pt m.term $$ cT
  ihave Hc' := csOptCC_csOptA pc dq m.confState h $$ Hc
  unfold smPts
  iexists pc, pi, pt, m.uf
  simp only [SnapMetaC.model]
  iframe HC Hc' HI cI' HT cT' Hpb
  ipureintro; exact Hnn

theorem smOptCC_smOpt (p : Loc) (dq : DFrac) (o : Option SnapMetaC)
    (h : ∀ m ∈ o, ∀ cs ∈ m.confState, cs.uf = []) :
    smOptCC (GF := GF) p dq o ⊢ smOpt p dq ((o.map SnapMetaC.model).getD metaZero) := by
  cases o with
  | none =>
    simp only [smOptCC, smOpt, Option.map_none, Option.getD_none]
    iintro %Hp
    ileft; ipureintro; exact ⟨Hp, rfl⟩
  | some m =>
    simp only [smOptCC, smOpt, Option.map_some, Option.getD_some]
    iintro H
    iright
    iapply smPtsCC_smPts p dq m (h m rfl) $$ H

theorem snapOptCC_snapOpt (p : Loc) (dq : DFrac) (o : Option SnapC)
    (h : ∀ s ∈ o, ∀ m ∈ s.metadata, ∀ cs ∈ m.confState, cs.uf = []) :
    snapOptCC (GF := GF) p dq o ⊢ snapOpt p dq (o.map SnapC.model) := by
  cases o with
  | none =>
    simp only [snapOptCC, snapOpt, Option.map_none]
    iintro %Hp; ipureintro; exact Hp
  | some s =>
    simp only [snapOptCC, snapOpt, Option.map_some]
    unfold ownSnapCC
    iintro ⟨%ds, %pm, %Hnn, HD, Hd, HM, Hm, #Hpb⟩
    ihave Hd' := bytesCC_own ds dq s.data $$ Hd
    ihave Hm' := smOptCC_smOpt pm dq s.metadata (h s rfl) $$ Hm
    unfold ownSnapM
    iexists ds, pm, s.uf
    simp only [SnapC.model]
    iframe HD Hd' HM Hm' Hpb
    ipureintro; exact Hnn

/-! ### The equivalence -/

/-- **Today's message at `dq` is at some content** whose snapshot's conf state has no unknown
fields; its responses' contents blank (pinned as pointers only). -/
theorem msgPtsC_msgPtsCC (l : Loc) (dq dqe : DFrac) (cap : Bool) (st : MsgSt) :
    msgPtsC (GF := GF) l dq dqe cap st ⊢
      ∃ c : MsgC, msgPtsCC l dq dqe cap c ∗ ⌜c.model = st ∧ c.csUfNil⌝ := by
  iintro H
  iunfold msgPtsC at H
  icases H with ⟨%pty, %pto, %pfr, %pte, %plt, %pix, %pco, %pvo, %prj, %prh, %es, %els, %ps, %cs,
    %rsl, %uf, %Hnn, HTy, #cTy, HTo, #cTo, HFr, #cFr, HTe, #cTe, HLt, #cLt, HIx, #cIx,
    HCo, #cCo, HVo, #cVo, HRj, #cRj, HRh, #cRh, HEs, Hes, #Hents, Hcap, HSn, Hsn, HCx,
    #Hcx, HRs, Hrs, #Hpb⟩
  ihave ⟨%oTy, #oTy', %hTy⟩ := cellRO_optCell pty st.msg.Type' $$ cTy
  ihave ⟨%oTo, #oTo', %hTo⟩ := cellRO_optCell pto st.msg.To' $$ cTo
  ihave ⟨%oFr, #oFr', %hFr⟩ := cellRO_optCell pfr st.msg.From' $$ cFr
  ihave ⟨%oTe, #oTe', %hTe⟩ := cellRO_optCell pte st.msg.Term' $$ cTe
  ihave ⟨%oLt, #oLt', %hLt⟩ := cellRO_optCell plt st.msg.LogTerm' $$ cLt
  ihave ⟨%oIx, #oIx', %hIx⟩ := cellRO_optCell pix st.msg.Index' $$ cIx
  ihave ⟨%oCo, #oCo', %hCo⟩ := cellRO_optCell pco st.msg.Commit' $$ cCo
  ihave ⟨%oVo, #oVo', %hVo⟩ := cellRO_optCell pvo st.msg.Vote' $$ cVo
  ihave ⟨%oRj, #oRj', %hRj⟩ := cellRO_optCell prj st.msg.Reject' $$ cRj
  ihave ⟨%oRh, #oRh', %hRh⟩ := cellRO_optCell prh st.msg.RejectHint' $$ cRh
  ihave ⟨%oCx, #oCx', %hCx⟩ := ownSlice_bytesC cs st.ctx $$ Hcx
  ihave ⟨%oSn, oSn', %hSn⟩ := snapOpt_snapOptCC ps dq st.snap $$ Hsn
  ihave ⟨%ecs, #Hecs, %hecs⟩ := entsRO_entsRoC els st.ents $$ Hents
  iexists (MsgC.mk ⟨oTy, oTo, oFr, oTe, oLt, oIx, ecs, oCo, oVo, oSn, oRj, oRh, oCx, uf⟩
    (st.resps.map fun r => (r, MsgC.blank)))
  isplitl
  · unfold msgPtsCC
    iexists pty, pto, pfr, pte, plt, pix, pco, pvo, prj, prh, es, els, ps, cs, rsl
    simp only [MsgC.f, MsgC.resps, List.map_map, Function.comp_def, List.map_id']
    iframe HTy oTy' HTo oTo' HFr oFr' HTe oTe' HLt oLt' HIx oIx' HCo oCo' HVo oVo' HRj oRj'
    iframe HRh oRh' HEs Hes Hecs Hcap HSn oSn' HCx oCx' HRs Hrs Hpb
    ipureintro; exact Hnn
  ipureintro
  refine ⟨?_, ?_⟩
  · obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩, b, d, e, f⟩ := st
    simp only [MsgC.model, MsgC.f, MsgC.resps, MsgFC.msgM, List.map_map, Function.comp_def,
      List.map_id'] at *
    rw [hTy, hTo, hFr, hTe, hLt, hIx, hCo, hVo, hRj, hRh, hecs, hSn.1, hCx]
  · intro s hs m hm cc hcc
    exact hSn.2 s hs m hm cc hcc

/-- **The content form gives today's message at `dq`**, when the snapshot's conf state has no
unknown fields. -/
theorem msgPtsCC_msgPtsC (l : Loc) (dq dqe : DFrac) (cap : Bool) (c : MsgC) (h : c.csUfNil) :
    msgPtsCC (GF := GF) l dq dqe cap c ⊢ msgPtsC l dq dqe cap c.model := by
  unfold msgPtsCC
  iintro ⟨%pty, %pto, %pfr, %pte, %plt, %pix, %pco, %pvo, %prj, %prh, %es, %els, %ps, %cs, %rsl,
    %Hnn, HTy, #cTy, HTo, #cTo, HFr, #cFr, HTe, #cTe, HLt, #cLt, HIx, #cIx, HCo, #cCo,
    HVo, #cVo, HRj, #cRj, HRh, #cRh, HEs, Hes, #Hents, Hcap, HSn, Hsn, HCx, #Hcx, HRs, Hrs,
    #Hpb⟩
  ihave #cTy' := optCell_cellRO pty c.f.type $$ cTy
  ihave #cTo' := optCell_cellRO pto c.f.to $$ cTo
  ihave #cFr' := optCell_cellRO pfr c.f.frm $$ cFr
  ihave #cTe' := optCell_cellRO pte c.f.term $$ cTe
  ihave #cLt' := optCell_cellRO plt c.f.logTerm $$ cLt
  ihave #cIx' := optCell_cellRO pix c.f.index $$ cIx
  ihave #cCo' := optCell_cellRO pco c.f.commit $$ cCo
  ihave #cVo' := optCell_cellRO pvo c.f.vote $$ cVo
  ihave #cRj' := optCell_cellRO prj c.f.reject $$ cRj
  ihave #cRh' := optCell_cellRO prh c.f.rejectHint $$ cRh
  ihave #Hcx' := bytesC_ro cs c.f.context $$ Hcx
  ihave Hsn' := snapOptCC_snapOpt ps dq c.f.snapshot h $$ Hsn
  ihave #Hents' := entsRoC_entsRO els c.f.entries $$ Hents
  unfold msgPtsC
  iexists pty, pto, pfr, pte, plt, pix, pco, pvo, prj, prh, es, els, ps, cs, rsl, c.f.uf
  simp only [MsgC.model, MsgFC.msgM]
  iframe HTy cTy' HTo cTo' HFr cFr' HTe cTe' HLt cLt' HIx cIx' HCo cCo' HVo cVo' HRj cRj' HRh cRh'
  iframe HEs Hes Hents' Hcap HSn Hsn' HCx Hcx' HRs Hrs Hpb
  ipureintro; exact Hnn

/-- **Today's message and its content form agree** (raft-entsize §2, with the correction: the
snapshot's conf state has no unknown fields). -/
theorem msgPtsC_iff_CC (l : Loc) (dq dqe : DFrac) (cap : Bool) (st : MsgSt) :
    msgPtsC (GF := GF) l dq dqe cap st ⊣⊢
      ∃ c : MsgC, msgPtsCC l dq dqe cap c ∗ ⌜c.model = st ∧ c.csUfNil⌝ := by
  constructor
  · exact msgPtsC_msgPtsCC l dq dqe cap st
  · iintro ⟨%c, H, %hc⟩
    obtain ⟨rfl, hu⟩ := hc
    iapply msgPtsCC_msgPtsC l dq dqe cap c hu $$ H

/-! ### Entries -/

/-- **A `*Entry` at `dq` holding exactly the content `c`** (raft-entsize §2: `entPts`'s content
form; `entRoC` is its `discard` instance up to the fraction's form). -/
def entPtsCC (l : Loc) (dq : DFrac) (c : EntryC) : IProp GF :=
  iprop(∃ (pt pi pty : Loc) (ds : GoSlice),
    ⌜l ≠ null⌝ ∗
    l.[raftpb.Entry, go!"Term"] ↦{dq} pt ∗ optCell pt c.term ∗
    l.[raftpb.Entry, go!"Index"] ↦{dq} pi ∗ optCell pi c.index ∗
    l.[raftpb.Entry, go!"Type"] ↦{dq} pty ∗ optCell pty c.type ∗
    l.[raftpb.Entry, go!"Data"] ↦{dq} ds ∗ bytesC ds c.data ∗
    pbMsg raftpb.Entry l c.uf)

/-- **Today's entry and its content form agree.** -/
theorem entPts_iff_CC (l : Loc) (dq : DFrac) (e : EntryM) :
    entPts (GF := GF) l dq e ⊣⊢ ∃ c : EntryC, entPtsCC l dq c ∗ ⌜c.model = e⌝ := by
  constructor
  · iunfold entPts
    iintro ⟨%pt, %pi, %pty, %ds, %uf, %Hnn, HT, #cT, HI, #cI, HY, #cY, HD, #Hd, #Hpb⟩
    ihave ⟨%oT, #oT', %hT⟩ := cellRO_optCell pt e.Term' $$ cT
    ihave ⟨%oI, #oI', %hI⟩ := cellRO_optCell pi e.Index' $$ cI
    ihave ⟨%oY, #oY', %hY⟩ := cellRO_optCell pty e.Type' $$ cY
    ihave ⟨%oD, #oD', %hD⟩ := ownSlice_bytesC ds e.Data' $$ Hd
    iexists ⟨oT, oI, oY, oD, uf⟩
    unfold entPtsCC
    isplitl
    · iexists pt, pi, pty, ds
      iframe HT HI HY HD Hpb oT' oI' oY' oD'
      ipureintro; exact Hnn
    ipureintro
    obtain ⟨a, b, c, d⟩ := e
    simp only [EntryC.model] at *
    rw [hT, hI, hY, hD]
  · iintro ⟨%c, H, %hc⟩
    subst hc
    unfold entPtsCC
    icases H with ⟨%pt, %pi, %pty, %ds, %Hnn, HT, #cT, HI, #cI, HY, #cY, HD, #Hd, #Hpb⟩
    ihave #cT' := optCell_cellRO pt c.term $$ cT
    ihave #cI' := optCell_cellRO pi c.index $$ cI
    ihave #cY' := optCell_cellRO pty c.type $$ cY
    ihave #Hd' := bytesC_ro ds c.data $$ Hd
    iunfold entPts
    iexists pt, pi, pty, ds, c.uf
    simp only [EntryC.model]
    iframe HT cT' HI cI' HY cY' HD Hd' Hpb
    ipureintro; exact Hnn

end defs

end EtcdGrove
end Perennial
