/-
Lean-first (no Rocq counterpart).

# The end of `run`'s `dmu` section (2026-11-01, stage II (j))

After a `Ready`'s storage changes, `dmu`'s invariant at the new image `M'`: the frozen bound raised to
`fz'` (with its record, which the caller builds), the snapshot index's bound raised, the image's hard
state's halves moved to the `Ready`'s, and the batch either recorded (`KdPhase.waiting`: a cut batch,
which `persist` enters when it writes) or entered at once (a commit-only batch: the file's durable
state moves without a write, the file lagging at most in its commit index; the writer is `dmu`'s
also after a crash, the retired state refuted by `run`'s claim).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.RunInv
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.RunImage
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.Replica__crash

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- **A commit-only batch on stored contents**: the durable state's term and vote kept, its commit
moved to one at least the stored one; contents that held it hold the new one. -/
theorem holds_commit_only (S : RaftState) (σ : StorContents) (h : HardStateM)
    (Hh : StorageHolds S σ) (Ht : h.Term' = S.term) (Hv : h.Vote' = S.vote)
    (Hc : σ.commit ≤ uint.nat h.Commit') :
    StorageHolds (readyDurable S h none []) σ := by
  obtain ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9⟩ := Hh
  unfold readyDurable
  simp only [Option.map_none, RaftState.next, appendEnts]
  exact ⟨H1, H2, H3, H4.trans Ht.symm, H5.trans Hv.symm, H6, Hc, H8, H9⟩

/-- The batch's durable state's term and vote are its hard state's. -/
theorem readyDurable_tv (S : RaftState) (h : HardStateM) (L : Option SnapLoan) (es : List EntryM) :
    (readyDurable S h L es).term = h.Term' ∧ (readyDurable S h L es).vote = h.Vote' ∧
      (readyDurable S h L es).commit = h.Commit' := by
  unfold readyDurable RaftState.next
  cases L <;> exact ⟨rfl, rfl, rfl⟩

/-- Two contents with the same bytes have the same commit index (the bytes start with the hard
state). -/
theorem encStor_commit (f f' : StorFile) (h : encStor f = encStor f') :
    f.hs.Commit' = f'.hs.Commit' := by
  have h1 := congrArg (fun b => (decU64 b).bind (fun p => (decU64 p.2).bind
    (fun q => (decU64 q.2).map Prod.fst))) h
  simp only [encStor, decU64_enc, Option.bind_some, Option.map_some] at h1
  exact Option.some.inj h1

/-- The file's commit index, from its bytes. -/
theorem fileVal_commit (o o' : Option StorFile) (h : kdFileVal o = kdFileVal o') (M : StorFile)
    (Hfb : ∀ f, o = some f → uint.nat f.hs.Commit' ≤ uint.nat M.hs.Commit') :
    (kdContents o').commit ≤ uint.nat M.hs.Commit' := by
  unfold kdFileVal at h
  cases o' with
  | none => simp [kdContents, kdEmpty, StorContents.commit]
  | some f' =>
    cases o with
    | none => cases h
    | some f =>
      simp only [Option.map_some, Option.some.injEq] at h
      have := Hfb f rfl
      simp only [kdContents, StorContents.commit]
      rw [← encStor_commit _ _ h]; exact this

end pure

section dmu
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KdStor GF]

attribute [local instance] kdStorageModel

/-- raft's namespace is open inside the replica's file invariant. -/
theorem kdRaftN_rep (id : w64) : (↑kdRaftN : CoPset) ⊆ ⊤ \ ↑(kdRepN .@ uint.nat id) := by
  intro p hp
  rw [Std.LawfulSet.mem_diff]
  exact ⟨CoPset.mem_full, fun h' => ndot_ne_disjoint nroot
    (show "kvdurable_raft" ≠ "kvdurable_rep" by decide) p ⟨hp, nclose_subseteq _ _ p h'⟩⟩

/-- `run`'s claim at `(none, S)` finds the phase idle, at `S`. -/
theorem kd_claim_idle (γ : KdNames) (id : w64) (n : Loc) (g : GName) (S S0 : RaftState)
    (M : StorFile) (pz : KdPhase) :
    ghostVar g (1 : Qp).half ((none : Option GName), S) ∗ kdPhaseInv (GF := GF) γ id n g S0 M pz ⊢
      ghostVar g (1 : Qp).half ((none : Option GName), S) ∗ ghostVar g (1 : Qp).half ((none : Option GName), S) ∗
        ⌜pz = KdPhase.idle ∧ S0 = S ∧ StorageHolds S (kdContents (some M))⌝ := by
  cases pz with
  | idle =>
    simp only [kdPhaseInv]
    iintro ⟨Hc, Hp, %Hh⟩
    ihave %Hag := ghostVar_agree g _ _ _ _ $$ Hc Hp
    obtain ⟨-, h2⟩ := Prod.mk.inj Hag
    subst h2
    iframe Hc Hp
    ipureintro; exact ⟨trivial, rfl, Hh⟩
  | waiting st st' ms γb =>
    simp only [kdPhaseInv]
    iintro ⟨Hc, Hp, -⟩
    ihave %Hag := ghostVar_agree g _ _ _ _ $$ Hc Hp
    cases (Prod.mk.inj Hag).1
  | fired γb =>
    simp only [kdPhaseInv]
    iintro ⟨Hc, Hp, -⟩
    ihave %Hag := ghostVar_agree g _ _ _ _ $$ Hc Hp
    cases (Prod.mk.inj Hag).1

/-- What `dmu`'s invariant keeps of the image beside the record the section changes. -/
def kdDmuRest (γ : KdNames) (id : w64) (r : Loc) (ph : KdDmuNames) (crashed : Bool) (S : RaftState)
    (M : StorFile) : IProp GF :=
  iprop(r.[KReplica, go!"crashed"] ↦{DFrac.own (1 : Qp).half} crashed ∗
    ∃ o : Option StorFile, (if crashed then iprop(kdWriter γ id S o ∨
          ∃ v : Option GName × RaftState, ghostVar ph.ph (1 : Qp).half v)
        else kdWriter γ id S o) ∗ ⌜∀ f, o = some f → uint.nat f.hs.Commit' ≤ uint.nat M.hs.Commit'⌝)

/-- **The `dmu` section's end, a cut batch**: recorded, `waiting`. -/
theorem dmu_close_cut (γ : KdNames) (id : w64) (r n st ms : Loc) (γs : MemStorNames)
    (ph : KdDmuNames) (crashed : Bool) (ip : Loc) (M M' : StorFile) (fz fz' : Nat) (S : RaftState)
    (stI stI' : NodeDriverState) (qs : List QMsg)
    (Hok : KdFileOk M') (Hh : StorageHolds stI'.durable (kdContents (some M'))) (HS : stI.durable = S)
    (Hc : uint.nat M.hs.Commit' ≤ uint.nat M'.hs.Commit') (Hfz : fz ≤ fz')
    (Hfzc : fz' ≤ uint.nat M'.hs.Commit' ∨ fz' ≤ uint.nat M'.prev)
    (His : uint.nat M.snap.Metadata'.Index' ≤ uint.nat M'.snap.Metadata'.Index') :
    kdDmuRest γ id r ph crashed S M ∗ st.[KStorage, go!"img"] ↦□ ip ∗ ownImage ip M' ∗
      memStorMeta ms γs M'.hs ∗ monoNatAuthOwn ph.ic 1 fz ∗
      memLog γs (uint.nat M'.prev + 1) DFrac.discard (M'.ents.take (fz' - uint.nat M'.prev)) ∗
      monoNatAuthOwn ph.is 1 (uint.nat M.snap.Metadata'.Index') ∗ ghostVar ph.cm (1 : Qp).half M.hs ∗
      kdSnapCert γ M'.snap ∗ ghostVar ph.ph (1 : Qp).half ((none : Option GName), S) ∗
      ghostVar ph.ph (1 : Qp).half ((none : Option GName), S) ∗ ghostVar ph.cm (1 : Qp).half M.hs ∗
      readyEnter n γ.r.cluster kdRaftN id stI stI' qs ==∗
    ∃ γb : GName, kdDmuInv γ id r n st ms γs ph ∗
      ghostVar ph.ph (1 : Qp).half (some γb, stI'.durable) ∗
      savedPropOwn γb DFrac.discard (kdBatchRes γ id n stI' qs) ∗
      ghostVar ph.cm (1 : Qp).half M'.hs ∗ monoNatLbOwn ph.ic fz' := by
  iintro ⟨Hrest, #Himg, Himage, Hmeta, Hic, #Hfz', His', Hcm, #Hcert, Hph, Hclaim, Hcmh,
    Henter⟩
  iunfold kdDmuRest at Hrest
  icases Hrest with ⟨Hcr, %o, Hwr, %Hfb⟩
  imod saved_prop_alloc (GF := GF) (kdBatchRes γ id n stI' qs) DFrac.discard DFrac.valid_discard
    with ⟨%γb, #Hsv⟩
  imod ghostVar_update_halves (some γb, stI'.durable) ph.ph _ _ $$ Hph Hclaim with ⟨Hph, Hclaim⟩
  imod ghostVar_update_halves M'.hs ph.cm _ _ $$ Hcm Hcmh with ⟨Hcm, Hcmh⟩
  imod mono_nat_own_update fz' Hfz $$ Hic with ⟨Hic, #Hlb⟩
  imod mono_nat_own_update (uint.nat M'.snap.Metadata'.Index') His $$ His' with ⟨His', -⟩
  imodintro
  iexists γb
  iframe Hclaim Hsv Hcmh Hlb
  iunfold kdDmuInv
  iexists crashed, ip, M', fz'
  iframe Hcr Himg Himage Hmeta Hic Hfz' His' Hcm
  isplitr
  · ipureintro; exact Hfzc
  iexists S, o, KdPhase.waiting stI stI' qs γb
  iframe Hwr Hcert
  isplitr
  · ipureintro; exact Hok
  isplitr
  · ipureintro; intro f hf; have := Hfb f hf; omega
  simp only [kdPhaseInv]
  iframe Hph Hsv Henter
  ipureintro; exact ⟨HS, Hh⟩

/-- **The `dmu` section's end, a commit-only batch**: entered at once, the file's durable state moved
without a write. -/
theorem dmu_close_enter (γ : KdNames) (dir : GoString) (id : w64) (r n st ms : Loc)
    (γs : MemStorNames) (ph : KdDmuNames) (crashed : Bool) (ip : Loc) (M M' : StorFile) (fz fz' : Nat)
    (S : RaftState) (stI stI' : NodeDriverState) (qs : List QMsg)
    (Hok : KdFileOk M') (Hh : StorageHolds stI'.durable (kdContents (some M'))) (HS : stI.durable = S)
    (Hc : uint.nat M.hs.Commit' ≤ uint.nat M'.hs.Commit') (Hfz : fz ≤ fz')
    (Hfzc : fz' ≤ uint.nat M'.hs.Commit' ∨ fz' ≤ uint.nat M'.prev)
    (His : uint.nat M.snap.Metadata'.Index' ≤ uint.nat M'.snap.Metadata'.Index')
    (Hfile : ∀ σ : StorContents, StorageHolds S σ → σ.commit ≤ uint.nat M'.hs.Commit' →
      StorageHolds stI'.durable σ) :
    £ 1 ∗ kdFileInv γ dir id ∗ kdDmuRest γ id r ph crashed S M ∗ st.[KStorage, go!"img"] ↦□ ip ∗
      ownImage ip M' ∗
      memStorMeta ms γs M'.hs ∗ monoNatAuthOwn ph.ic 1 fz ∗
      memLog γs (uint.nat M'.prev + 1) DFrac.discard (M'.ents.take (fz' - uint.nat M'.prev)) ∗
      monoNatAuthOwn ph.is 1 (uint.nat M.snap.Metadata'.Index') ∗ ghostVar ph.cm (1 : Qp).half M.hs ∗
      kdSnapCert γ M'.snap ∗ ghostVar ph.ph (1 : Qp).half ((none : Option GName), S) ∗
      ghostVar ph.ph (1 : Qp).half ((none : Option GName), S) ∗ ghostVar ph.cm (1 : Qp).half M.hs ∗
      readyEnter n γ.r.cluster kdRaftN id stI stI' qs ∗ nodeRunning n γ.r.cluster kdRaftN (1 : Qp).half
      ={⊤}=∗
    kdDmuInv γ id r n st ms γs ph ∗
      ghostVar ph.ph (1 : Qp).half ((none : Option GName), stI'.durable) ∗
      kdBatchRes γ id n stI' qs ∗ nodeRunning n γ.r.cluster kdRaftN (1 : Qp).half ∗
      ghostVar ph.cm (1 : Qp).half M'.hs ∗ monoNatLbOwn ph.ic fz' := by
  iintro ⟨Hlc, #HfInv, Hrest, #Himg, Himage, Hmeta, Hic, #Hfz', His', Hcm, #Hcert, Hph,
    Hclaim, Hcmh, Henter, Hrun⟩
  iunfold kdDmuRest at Hrest
  icases Hrest with ⟨Hcr, %o, Hwr, %Hfb⟩
  -- the writer: also `dmu`'s after a crash, the retired state refuted by the claim
  ihave ⟨Hwr, Hph, Hclaim⟩ : iprop(kdWriter γ id S o ∗
      ghostVar ph.ph (1 : Qp).half ((none : Option GName), S) ∗
      ghostVar ph.ph (1 : Qp).half ((none : Option GName), S)) $$ [Hwr Hph Hclaim]
  · cases crashed
    · simp only [Bool.false_eq_true, ↓reduceIte]; iframe Hwr Hph Hclaim
    · simp only [↓reduceIte]
      icases Hwr with (Hwr | ⟨%v, Hv⟩)
      · iframe Hwr Hph Hclaim
      · iexfalso
        iapply ghostVar_three_halves ph.ph _ _ v
        iframe Hph Hclaim Hv
  iunfold kdFileInv at HfInv
  iinv HfInv with HI Hclose
  imod lc_fupd_elim_later $$ Hlc HI with HI
  icases HI with ⟨%S0, %o0, HD, Hwv, %HSH, HcF⟩
  icases HD with (⟨HrS, Hdf⟩ | Hlent)
  rotate_left
  · iexfalso
    iapply kdWriter_lent_absurd γ id _ _ _ _
    iframe Hwr Hwv Hlent
  iunfold kdWriter at Hwr
  ihave %Hag := ghostVar_agree (γ.wr id) _ _ _ _ $$ Hwr Hwv
  obtain ⟨h1, h2⟩ := Prod.mk.inj Hag
  subst h1
  iunfold readyEnter at Henter
  ihave HrS : raftState γ.r.cluster id stI.durable $$ [HrS]
  · rw [HS]; iexact HrS
  imod Henter $$ %(⊤ \ ↑(kdRepN .@ uint.nat id)) %((1 : Qp).half) %(kdRaftN_rep id) [$HrS $Hrun]
    with ⟨HrS, Hrun, Hdrv, #Hmsgs⟩
  imod ghostVar_update_halves (stI'.durable, kdFileVal o) (γ.wr id) _ _ $$ Hwr Hwv with ⟨Hwr, Hwv⟩
  imod Hclose $$ [HrS Hdf Hwv HcF] with -
  · inext
    iexists stI'.durable, o0
    rw [h2]
    isplitl [HrS Hdf]
    · ileft; iframe HrS Hdf
    iframe Hwv HcF
    ipureintro
    refine ⟨Hfile _ HSH.1 ?_, HSH.2⟩
    have := fileVal_commit o o0 h2 M Hfb
    omega
  imod ghostVar_update_halves ((none : Option GName), stI'.durable) ph.ph _ _ $$ Hph Hclaim
    with ⟨Hph, Hclaim⟩
  imod ghostVar_update_halves M'.hs ph.cm _ _ $$ Hcm Hcmh with ⟨Hcm, Hcmh⟩
  imod mono_nat_own_update fz' Hfz $$ Hic with ⟨Hic, #Hlb⟩
  imod mono_nat_own_update (uint.nat M'.snap.Metadata'.Index') His $$ His' with ⟨His', -⟩
  imodintro
  iframe Hclaim Hcmh Hlb Hrun
  isplitr [Hdrv]
  · iunfold kdDmuInv
    iexists crashed, ip, M', fz'
    iframe Hcr Himg Himage Hmeta Hic Hfz' His' Hcm
    isplitr
    · ipureintro; exact Hfzc
    iexists stI'.durable, o, KdPhase.idle
    isplitl [Hwr]
    · iunfold kdWriter
      cases crashed
      · simp only [Bool.false_eq_true, ↓reduceIte]; iexact Hwr
      · simp only [↓reduceIte]; ileft; iexact Hwr
    iframe Hcert
    isplitr
    · ipureintro; exact Hok
    isplitr
    · ipureintro; intro f hf; have := Hfb f hf; omega
    simp only [kdPhaseInv]
    iframe Hph
    ipureintro; exact Hh
  iunfold kdBatchRes
  iframe Hdrv Hmsgs

/-- **The frozen record raised to the delivered log `D'`**: the image's entries up to `fz` were
frozen; those from `fz` to `len D'` are `D'`'s (the batch's durable log's, G14), which the applier's
frozen record (`frozenTo c D'`, `c ≤ fz`) has frozen. -/
theorem frozen_extend (γs : MemStorNames) (p : Nat) (E E' : List EntryM) (c fz : Nat)
    (D' : List LogEntry) (Hc : c ≤ fz) (Hp : p ≤ fz)
    (Htk : E'.take (fz - p) = E.take (fz - p))
    (Hent : ∀ i, fz < i → i ≤ D'.length →
      ∃ x, D'[i - 1]? = some x ∧ E'[i - p - 1]? = some (x.toEntryM (W64 i))) :
    memLog (GF := GF) γs (p + 1) DFrac.discard (E.take (fz - p)) ∗ kvreconf.frozenTo γs c D' ⊢
      memLog γs (p + 1) DFrac.discard (E'.take (max fz D'.length - p)) := by
  iintro ⟨#Hold, #Hf⟩
  by_cases hle : D'.length ≤ fz
  · rw [show max fz D'.length = fz by omega, Htk]; iexact Hold
  rw [show max fz D'.length = D'.length by omega]
  have hlen : D'.length - p ≤ E'.length := by
    obtain ⟨x, -, hx⟩ := Hent D'.length (by omega) (Nat.le_refl _)
    have := (List.getElem?_eq_some_iff.1 hx).1
    omega
  have hsplit : E'.take (D'.length - p) =
      E'.take (fz - p) ++ (LogEntry.toEntries D' 0).drop fz := by
    apply List.ext_getElem?
    intro j
    by_cases hj : j < fz - p
    · rw [List.getElem?_append_left (by rw [List.length_take]; omega), List.getElem?_take_of_lt hj,
        List.getElem?_take_of_lt (by omega)]
    · rw [List.getElem?_append_right (by rw [List.length_take]; omega), List.length_take,
        show min (fz - p) E'.length = fz - p by omega]
      by_cases hj2 : j < D'.length - p
      · rw [List.getElem?_take_of_lt hj2, List.getElem?_drop]
        obtain ⟨x, hx, hx'⟩ := Hent (p + j + 1) (by omega) (by omega)
        rw [show p + j + 1 - p - 1 = j by omega] at hx'
        rw [hx', show fz + (j - (fz - p)) = p + j + 1 - 1 by omega,
          kvreconf.kvr_toEntries_get D' 0 _ x hx]
        congr 3; push_cast; omega
      · rw [List.getElem?_eq_none (by rw [List.length_take]; omega), List.getElem?_eq_none
          (by rw [List.length_drop, kvreconf.kvr_toEntries_length]; omega)]
  rw [hsplit]
  iapply (memLog_app γs (p + 1) DFrac.discard _ _).2
  rw [show (E'.take (fz - p)).length = fz - p by rw [List.length_take]; omega]
  isplitl []
  · rw [Htk]; iexact Hold
  unfold kvreconf.frozenTo
  have hd : (LogEntry.toEntries D' 0).drop c =
      ((LogEntry.toEntries D' 0).drop c).take (fz - c) ++ (LogEntry.toEntries D' 0).drop fz := by
    conv => lhs; rw [← List.take_append_drop (fz - c) ((LogEntry.toEntries D' 0).drop c)]
    rw [List.drop_drop, show c + (fz - c) = fz by omega]
  ihave #Hf' : memLog γs (c + 1) DFrac.discard
      (((LogEntry.toEntries D' 0).drop c).take (fz - c) ++ (LogEntry.toEntries D' 0).drop fz) $$ []
  · rw [← hd]; iexact Hf
  ihave ⟨-, H2⟩ := (memLog_app γs (c + 1) DFrac.discard _ _).1 $$ Hf'
  rw [List.length_take, List.length_drop, kvreconf.kvr_toEntries_length,
    show min (fz - c) (D'.length - c) = fz - c by omega,
    show c + 1 + (fz - c) = p + 1 + (fz - p) by omega]
  iexact H2

end dmu

end kvdurable
end EtcdGrove
end Perennial
