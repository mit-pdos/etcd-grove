/-
`epaxos.New`'s assembly lemmas: the initial protocol state's heap image (`ownRep_init`, from the
fields `New` fills), the rpc table's entries after the nine registrations (`tableEntries_new`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.RunSpec

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs
open model

attribute [local instance] GooseGlobalGS.gooseInvGS

variable [GooseExts]

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS]
variable [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions] [TH : StateTreemap GF]

theorem range_map_const {A : Type} (n : Nat) (a : A) :
    (List.range n).map (fun _ => a) = List.replicate n a := by
  apply List.ext_getElem <;> simp

/-- A fresh row (`MAX_INSTANCE` nil pointers) is an empty row of the initial state. -/
theorem ownRowI_init (γ : EpNames) (i q : Nat) (row : GoSlice) (n : Nat) (hn : n = MAX_INSTANCE) :
    row ↦* List.replicate n (null : Loc) ⊢
      ownRowI (GF := GF) γ i q row (RState.init i).inst := by
  unfold ownRowI
  iintro H
  iexists List.replicate n (null : Loc)
  iframe H
  isplitr
  · ipureintro; rw [List.length_replicate, hn]
  simp only [RState.init]
  iapply (BigSepL.bigSepL_pure (PROP := IProp GF)).2
  ipureintro
  intro _ _ h
  exact List.eq_of_mem_replicate (List.mem_of_getElem? h)

/-- An empty conflicts map is an empty row of the initial state. -/
theorem ownConflictRow_init (m : GoMap) :
    m ↦$ (∅ : GMap w64 Loc) ⊢ ownConflictRow (GF := GF) m (fun _ => none) := by
  unfold ownConflictRow
  iintro H
  iexists ∅
  iframe H
  isplitr
  · ipureintro; intro k; rfl
  iapply BigSepM.bigSepM_empty.2
  iempintro

/-- The heap image of the initial state `RState.init i` from the fields `New` fills. -/
theorem ownRep_init (γ : EpNames) (i : Nat) (r rr st : Loc)
    (iss crt cut eut cfs ls lp : GoSlice) (msk : GoMap) (rows : List GoSlice) (cms : List GoMap)
    (hrows : rows.length = 5) (hcms : cms.length = 5) :
    efld r go!"InstanceSpace" ↦□ iss ∗ iss ↦*□ rows ∗
      ([∗list] row ∈ rows, row ↦* List.replicate MAX_INSTANCE (null : Loc)) ∗
      efld r go!"crtInstance" ↦□ crt ∗ crt ↦* List.replicate 5 (W32 (-1)) ∗
      efld r go!"CommittedUpTo" ↦□ cut ∗ cut ↦* List.replicate 5 (W32 (-1)) ∗
      efld r go!"ExecedUpTo" ↦□ eut ∗ eut ↦* List.replicate 5 (W32 (-1)) ∗
      efld r go!"conflicts" ↦□ cfs ∗ cfs ↦*□ cms ∗
      ([∗list] m ∈ cms, m ↦$ (∅ : GMap w64 Loc)) ∗
      efld r go!"maxSeqPerKey" ↦□ msk ∗ msk ↦$ (∅ : GMap w64 w32) ∗
      efld r go!"lastScan" ↦□ ls ∗ ls ↦* List.replicate 5 (W32 (-1)) ∗
      efld r go!"lastPut" ↦□ lp ∗ lp ↦* List.replicate 5 (W32 (-1)) ∗
      efld r go!"maxSeq" ↦ W32 0 ∗ efld r go!"IsLeader" ↦ false ∗
      efld r go!"maxRecvBallot" ↦ W32 (-1) ∗
      efld r go!"Replica" ↦□ rr ∗ fld rr go!"State" ↦□ st ∗ isState (GF := GF) st ∅ ⊢
    ownRep γ i r (RState.init i) := by
  rw [ownRep_unseal]; unfold ownRepDef repInsts repRowArr repConf repMsk repStore repPeer
  iintro ⟨#Hissf, #Hiss, Hrows, #Hcrtf, Hcrt, #Hcutf, Hcut, #Heutf, Heut, #Hcff, #Hcfs, Hcms,
    #Hmskf, Hmsk, #Hlsf, Hls, #Hlpf, Hlp, Hms, Hil, Hmrb, #Hrr, #Hst, Hstate⟩
  isplitr
  · ipureintro; intro x _; rfl
  isplitr
  · ipureintro; intro q _
    simp only [RState.init, zz, MAX_INSTANCE]; decide
  isplitl [Hrows]
  · iexists iss, rows
    iframe Hissf Hiss
    isplitr
    · ipureintro; exact hrows
    iapply BigSepL.bigSepL_mono ?_ $$ Hrows
    intro q row _
    exact ownRowI_init γ i q row MAX_INSTANCE rfl
  simp only [RState.init, range_map_const, show nR = 5 from rfl]
  isplitl [Hcrt]
  · iexists crt; iframe Hcrtf Hcrt
  isplitl [Hcut]
  · iexists cut; iframe Hcutf Hcut
  isplitl [Heut]
  · iexists eut; iframe Heutf Heut
  isplitl [Hcms]
  · iexists cfs, cms
    iframe Hcff Hcfs
    isplitr
    · ipureintro; exact hcms
    iapply BigSepL.bigSepL_mono ?_ $$ Hcms
    intro q m _
    exact ownConflictRow_init m
  isplitl [Hmsk]
  · iexists msk, (∅ : GMap w64 w32)
    isplitr
    · iexact Hmskf
    isplitl [Hmsk]
    · iexact Hmsk
    ipureintro; intro k; rfl
  isplitl [Hls]
  · iexists ls; iframe Hlsf Hls
  isplitl [Hlp]
  · iexists lp; iframe Hlpf Hlp
  iframe Hms Hil Hmrb
  isplitl [Hstate]
  · iexists rr, st, (∅ : GMap w64 (List w8))
    isplitr
    · iexact Hrr
    isplitr
    · iexact Hst
    isplitl [Hstate]
    · iexact Hstate
    ipureintro; intro k; rfl
  ileft; ipureintro; first | trivial | rfl

/-- A function on the kinds, by its nine values (in `MsgKind.all`'s order). -/
def kindSel {A : Type} (a0 a1 a2 a3 a4 a5 a6 a7 a8 : A) : MsgKind → A
  | .prepare => a0 | .prepareReply => a1 | .preAccept => a2 | .preAcceptReply => a3
  | .accept => a4 | .acceptReply => a5 | .commit => a6 | .tryPreAccept => a7
  | .tryPreAcceptReply => a8

/-- A big separating conjunction over the kinds, from its nine parts. -/
theorem allKinds_intro (Q : MsgKind → IProp GF) :
    Q .prepare ∗ Q .prepareReply ∗ Q .preAccept ∗ Q .preAcceptReply ∗ Q .accept ∗
      Q .acceptReply ∗ Q .commit ∗ Q .tryPreAccept ∗ Q .tryPreAcceptReply ⊢
    [∗list] k ∈ MsgKind.all, Q k := by
  unfold MsgKind.all
  iintro ⟨H0, H1, H2, H3, H4, H5, H6, H7, H8⟩
  iapply BigSepL.bigSepL_cons.2
  isplitl [H0]
  · iexact H0
  iapply BigSepL.bigSepL_cons.2
  isplitl [H1]
  · iexact H1
  iapply BigSepL.bigSepL_cons.2
  isplitl [H2]
  · iexact H2
  iapply BigSepL.bigSepL_cons.2
  isplitl [H3]
  · iexact H3
  iapply BigSepL.bigSepL_cons.2
  isplitl [H4]
  · iexact H4
  iapply BigSepL.bigSepL_cons.2
  isplitl [H5]
  · iexact H5
  iapply BigSepL.bigSepL_cons.2
  isplitl [H6]
  · iexact H6
  iapply BigSepL.bigSepL_cons.2
  isplitl [H7]
  · iexact H7
  iapply BigSepL.bigSepL_cons.2
  isplitl [H8]
  · iexact H8
  iapply BigSepL.bigSepL_nil.2
  iempintro

/-- The table `New`'s nine registrations build: code `9 + j` for the `j`-th kind of
`MsgKind.all`, with a fresh prototype of the kind and the kind's channel. -/
def newTable (o : MsgKind → Loc) (ch : MsgKind → GoChan) : GMap w8 rpc.Pair' :=
  MsgKind.all.foldl (fun E k =>
    E.insert k.code (rpc.Pair'.mk (interface.mkOk (go.GoType.PointerType k.ty) #(o k)) (ch k))) ∅

/-- The table's entries are `tableEntriesOk` given the channels' bags. -/
theorem tableEntries_new (γ : EpNames) (i : Nat) (o : MsgKind → Loc) (ch : MsgKind → GoChan)
    (g : MsgKind → ChanNames) :
    ([∗list] k ∈ MsgKind.all, isChanBag (g k) (ch k) (deliverChanP (GF := GF) γ i k)) ⊢
      tableEntriesOk γ i (newTable o ch) := by
  unfold tableEntriesOk
  iintro #H
  isplitr
  · ipureintro
    intro c hc
    simp only [newTable, MsgKind.all, List.foldl, GMap.lookup_insert_eq_iff] at hc
    have hall : ∀ k, k ∈ MsgKind.all := by intro k; cases k <;> simp [MsgKind.all]
    by_cases h9 : W8 9 = c
    · exact ⟨.prepare, hall _, h9.symm⟩
    by_cases h10 : W8 10 = c
    · exact ⟨.prepareReply, hall _, h10.symm⟩
    by_cases h11 : W8 11 = c
    · exact ⟨.preAccept, hall _, h11.symm⟩
    by_cases h12 : W8 12 = c
    · exact ⟨.preAcceptReply, hall _, h12.symm⟩
    by_cases h13 : W8 13 = c
    · exact ⟨.accept, hall _, h13.symm⟩
    by_cases h14 : W8 14 = c
    · exact ⟨.acceptReply, hall _, h14.symm⟩
    by_cases h15 : W8 15 = c
    · exact ⟨.commit, hall _, h15.symm⟩
    by_cases h16 : W8 16 = c
    · exact ⟨.tryPreAccept, hall _, h16.symm⟩
    by_cases h17 : W8 17 = c
    · exact ⟨.tryPreAcceptReply, hall _, h17.symm⟩
    simp only [MsgKind.code, h9, h10, h11, h12, h13, h14, h15, h16, h17, ↓reduceIte] at hc
    exact absurd rfl hc
  iapply BigSepL.bigSepL_mono ?_ $$ H
  intro _ k hk
  iintro #Hb
  iexists interface.mkOk (go.GoType.PointerType k.ty) #(o k), ch k, g k
  iframe Hb
  ipureintro
  refine ⟨?_, o k, rfl⟩
  have hmem : k ∈ MsgKind.all := List.mem_of_getElem? hk
  simp only [MsgKind.all, List.mem_cons, List.not_mem_nil, _root_.or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [newTable, MsgKind.all, List.foldl, GMap.lookup_insert_eq_iff, MsgKind.code]

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
