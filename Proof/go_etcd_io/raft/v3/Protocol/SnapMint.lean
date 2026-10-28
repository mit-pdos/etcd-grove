/-
Lean-first (no Rocq counterpart). D22 S-b (2026-10-19): etcd's merged snapshot as a protocol
`.snap` message (`notes/decisions.md`, "D22 S-b carried out").

etcd's `createMergedSnapshotMessage` overwrites the snapshot of a `MsgSnap` raft made (the
storage's, at some `i0`) with the apply thread's `(appliedi, appliedt, confState)`, and (D22a,
the fork's `de825d8c6`) sends it only when the batch's `toApply.raftTerm`, the latest non-empty
`HardState` term the raft goroutine saw, is the message's term `T`. This file states what that
check buys at the protocol level:

- `commitWit γ T c` (`CommitWit.lean`): what a node at term `T` with commit index `c` knows of its full log `F`:
  its records, `commitIn γ F c T` and the committed prefix `F.take c`. Every node holds it of its
  own state (`ownRaftGhost_commitWit`); raft's `Ready` hands it out with a non-empty `HardState`
  `(T, c)` (`readyData`, `InvNode.lean`), so the raft goroutine has it for the term it records.
- `isMessage_snap_recontent`: from a `.snap` message of term `T`, a `commitWit` at `T` with
  `c ≥ appliedi`, and the apply thread's committed prefix `A` (`appliedi = |A|`, `appliedt` its
  last term), the message with its snapshot metadata replaced by `(appliedi, appliedt)` is again a
  `.snap` message (the clause unchanged). The leader log of `T` holding `appliedi` comes from the
  commit fact's justification: the bootstrap log (in every leader log), a commit fact of `T` (a
  log of `T`'s leader, the message's sender: one base per term, `leadPrefix_base`), or one of an
  earlier term (Leader Completeness, `lc_core`, puts it in the sender's log: hence the vote
  table, and the fancy update). The one premise beyond the witness: `appliedi` is at least the
  message's own index (the snapshot raft made is the storage's, at most what the apply thread
  applied), which puts `appliedi` above the term's leader-log base.
-/
module

public import Proof.go_etcd_io.raft.v3.Protocol.Facts
public import Proof.go_etcd_io.raft.v3.Protocol.CommitWit

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI GMap go_etcd_io.raft.v3

section ghost
variable [GooseExts]
variable {GF : BundledGFunctors} [AllG GF] [ReceiptGS GF] [InvGS GF]

/-- A full log's last entry at `i ≥ 1`, from its term there. -/
private theorem full_entry_of_term (F : List EntryM) (i t : w64) :
    PlogWf base0 F → plogTermAt base0 F i = some t → 0 < uint.Z i →
    ∃ e, F[(uint.Z i - 1).toNat]? = some e ∧ e.Index' = i ∧ e.Term' = t := by
  intro Hwf Ht Hi
  obtain ⟨e, He, Hix, Het⟩ :=
    plogTermAt_some_entry base0 F i t (PlogWf_wfR _ _ Hwf) Ht (by rw [base0_index]; exact Hi)
  refine ⟨e, ?_, Hix, Het⟩
  rw [base0_index] at He
  simpa using He

/-- The prefix of length `i` of a log that reaches `i`, as the committed prefix `A` of that
length: the same list, whose last term is the log's term at `i`. -/
private theorem take_last_term (F A : List EntryM) (i t : w64) :
    PlogWf base0 F → (plogTermAt base0 F i).isSome →
    (A <+: F.take (uint.Z i).toNat ∨ F.take (uint.Z i).toNat <+: A) →
    (A.length : Int) = uint.Z i → A.getLast?.map EntryM.Term' = some t →
    A = F.take (uint.Z i).toNat ∧ plogTermAt base0 F i = some t := by
  intro Hwf Hs Hpre Hlen Hlast
  obtain ⟨x, Hx⟩ := Option.isSome_iff_exists.mp Hs
  have Hr := (plogTermAt_some_range _ _ _ _ Hx).2
  unfold plogLastIndexZ at Hr; rw [base0_index] at Hr
  have HtL : (F.take (uint.Z i).toNat).length = (uint.Z i).toNat := by
    rw [List.length_take]; omega
  have HA : A = F.take (uint.Z i).toNat := by
    rcases Hpre with Hp | Hp
    · exact Hp.eq_of_length (by rw [HtL]; omega)
    · exact (Hp.eq_of_length (by rw [HtL]; omega)).symm
  refine ⟨HA, ?_⟩
  have Hi0 : 0 < uint.Z i := by
    cases A with
    | nil => simp at Hlast
    | cons _ _ => simp at Hlen; omega
  obtain ⟨e, He, -, Het⟩ := full_entry_of_term F i x Hwf Hx Hi0
  have HAl : A.getLast? = some e := by
    rw [HA, List.getLast?_eq_getElem?, HtL, List.getElem?_take]
    simp only [show (uint.Z i).toNat - 1 < (uint.Z i).toNat by omega, ite_true]
    rw [show (uint.Z i).toNat - 1 = (uint.Z i - 1).toNat by omega]; exact He
  rw [HAl] at Hlast
  simp only [Option.map_some, Option.some.injEq] at Hlast
  rw [Hx, ← Het, Hlast]

/-- A leader log of `T` (the leader `src`'s, at the base `bL` of its log `l`) holding a commit
fact's index `ai` of term at most `T`, agreeing there with the fact's log `F` (see the file
header: the bootstrap log, the term-`T` leader's log, or Leader Completeness). -/
private theorem snap_leadLog (γ : RaftNames) (E : CoPset) (src T ai : w64) (bL : entryID)
    (l fp F : List EntryM) :
    ↑(raftLogN γ) ⊆ E → PlogWf base0 F →
    ⊢ raftCommitInv (GF := GF) γ -∗ leadPrefix γ src T bL l -∗ lpfull γ src T bL l fp -∗
      logRecs γ base0 F -∗ commitIn γ F ai T ={E}=∗
      ∃ l' fp', leadPrefix γ src T bL l' ∗ lpfull γ src T bL l' fp' ∗
        ⌜FullOk bL fp' ∧ PlogWf bL l' ∧ (plogTermAt base0 F ai).isSome ∧
          plogTermAt base0 (fp' ++ l') ai = plogTermAt base0 F ai⌝ := by
  intro HE HwF
  iintro #Hinv #Hp #Hpf #HrF #Hc
  ihave #Hpf0 := Hpf
  iunfold lpfull at Hpf0
  icases Hpf0 with ⟨%F0, #Hc0, #Hfr, %Hpure⟩
  obtain ⟨Hfull, HF0, HwL, -⟩ := Hpure
  ihave #⟨-, #HrL⟩ := leadPrefix_wf γ src T bL l $$ Hp
  ihave #HrG2 := logRecs_full γ bL fp l Hfull $$ Hfr HrL
  have HwG2 := full_wf _ _ _ Hfull HwL
  ihave #Hl := Hp
  iunfold leadPrefix at Hl
  icases Hl with ⟨#Hl, -⟩
  ihave #Hj := commitIn_j γ F ai T $$ Hc
  iunfold commitJ at Hj
  icases Hj with (%H0 | ⟨%t, %n, %G, #Hq, %Hcn⟩)
  · -- the bootstrap log, at the start of every leader log
    obtain ⟨Hab, Hat⟩ := H0
    ihave #Hlf := leadFull_intro γ src T bL l fp $$ Hp Hpf
    icases leadFull_boot γ T (fp ++ l) $$ Hlf with %Hb
    have Hsb : (plogTermAt base0 γ.reBoot ai).isSome :=
      plogTermAt_in_range _ _ _ ⟨by rw [base0_index]; exact uint_Z_nonneg ai, by
        unfold plogLastIndexZ; rw [base0_index]; omega⟩
    icases logRecs_boot_termAt γ (fp ++ l) HwG2 $$ HrG2 with %Hag
    have Hlen := Hb.1.length_le
    imodintro
    iexists l, fp
    iframe Hp Hpf
    ipureintro
    refine ⟨Hfull, HwL, by rw [← Hat]; exact Hsb, ?_⟩
    rw [← Hat, Hag ai Hab (by omega)]
  obtain ⟨Han, HtT, HGF⟩ := Hcn
  icases cq_full γ t n G $$ Hq with ⟨%HwG, #HrG⟩
  icases cq_base γ t n G $$ Hq with ⟨%HGn, #HGl⟩
  have HsG : (plogTermAt base0 G ai).isSome := full_term_at_some G ai n (by rw [HGn]; rfl) Han
  have HsF : (plogTermAt base0 F ai).isSome := by rw [← HGF]; exact HsG
  by_cases Hne : t = T
  · -- a commit fact of `T`: a log of `T`'s leader, the sender, at the term's one base
    subst Hne
    iunfold leadFull at HGl
    icases HGl with ⟨%ldr, %bL', %l', %fp', #Hp', #Hpf', %HG⟩
    ihave #Hl' := Hp'
    iunfold leadPrefix at Hl'
    icases Hl' with ⟨#Hl', -⟩
    icases isLeader_unique γ src ldr t $$ Hl Hl' with %Hsrc
    subst Hsrc
    icases leadPrefix_base γ src src t bL bL' l l' $$ Hp Hp' with %Hb
    subst Hb
    ihave #Hpf1 := Hpf'
    iunfold lpfull at Hpf1
    icases Hpf1 with ⟨%F1, -, -, %Hpure1⟩
    imodintro
    iexists l', fp'
    iframe Hp' Hpf'
    ipureintro
    exact ⟨Hpure1.1, Hpure1.2.2.1, HsF, by rw [← HG]; exact HGF⟩
  · -- an earlier term's: Leader Completeness puts it in the sender's campaign log
    have Hlt : uint.Z t < uint.Z T := by
      have : uint.Z t ≠ uint.Z T := fun h => Hne (uint_Z_inj.mp h)
      omega
    icases isCamp_ok γ src T F0 $$ Hc0 with %Hcok
    have Hcl := camp_last _ _ Hcok
    have HGl2 : plogTermAt base0 (fp ++ l) (W64 (plogLastIndexZ base0 F0))
        = some (plogLast base0 F0).term' := by
      rw [plogTermAt_prefix _ F0 _ _ HF0 (by rw [Hcl]; rfl), Hcl]
    ihave #Hli := raftCommitInv_log γ $$ Hinv
    unfold raftLogInv raftLogInvBody logRest
    iinv Hli with ⟨%P, >HP, >#Hjs, >Htbl, >Hwt, >#Hds, >Hq1⟩ Hclose
    icases lc_core γ ((uint.Z T).toNat + 1) T t n G src F0 (fp ++ l)
        (by have := uint_Z_nonneg T; omega) Hlt HwG2 HGl2 $$ Htbl Hq Hl Hc0 HrG2 with %H2n
    imod Hclose $$ [HP Htbl Hwt Hq1] with -
    · inext
      iexists P
      iframe HP Hjs Htbl Hwt Hds Hq1
    icases full_match γ G (fp ++ l) n HwG HwG2 (by rw [HGn]; rfl) (by rw [HGn, H2n])
      $$ HrG HrG2 with %Hm
    imodintro
    iexists l, fp
    iframe Hp Hpf
    ipureintro
    exact ⟨Hfull, HwL, HsF, by rw [← Hm ai Han, HGF]⟩

/-- **etcd's merged snapshot is a `.snap` message** (see the file header). The `.snap` clause
(`isMessage`, `GhostState.lean`) holds of `m` with `(index, logterm)` replaced by
`(ai, at_)`, given a witness `commitWit γ m.term c` with `ai ≤ c`, the committed prefix `A` of
length `ai` with last term `at_`, and `m.index ≤ ai`. -/
theorem isMessage_snap_recontent (γ : RaftNames) (E : CoPset) (m : Msg) (c ai at_ : w64)
    (A : List EntryM) :
    ↑(raftLogN γ) ⊆ E →
    m.ty = .snap →
    uint.Z m.index ≤ uint.Z ai → uint.Z ai ≤ uint.Z c →
    (A.length : Int) = uint.Z ai → A.getLast?.map EntryM.Term' = some at_ →
    ⊢ raftCommitInv (GF := GF) γ -∗ isMessage γ m -∗ commitWit γ m.term c -∗ isCommitted γ A
      ={E}=∗ isMessage γ { m with index := ai, logterm := at_ } := by
  intro HE Hty Hmi Hac HAlen HAlast
  have Hai0 : 0 < uint.Z ai := by
    cases A with
    | nil => simp at HAlast
    | cons _ _ => simp at HAlen; omega
  generalize Hm' : ({ m with index := ai, logterm := at_ } : Msg) = m'
  have Hty' : m'.ty = .snap := by rw [← Hm']; exact Hty
  have Hsrc : m'.src = m.src := by rw [← Hm']
  have Hterm : m'.term = m.term := by rw [← Hm']
  have Hdst : m'.dst = m.dst := by rw [← Hm']
  have Hix : m'.index = ai := by rw [← Hm']
  have Hlg : m'.logterm = at_ := by rw [← Hm']
  iintro #Hinv #Hm #Hw #HA
  iunfold isMessage at Hm
  rw [Hty]
  icases Hm with ⟨#Hl, -, ⟨%bL, %l, %fp, #Hp, %Hlt, #Hpf, -, -⟩, %Hnz, %Hds⟩
  iunfold commitWit at Hw
  icases Hw with ⟨%F, %HwF, #HrF, #HcF, #HcmF⟩
  -- the witness lowered to `ai`
  ihave #HcFa := commitIn_le γ F c ai m.term HwF Hac $$ HrF HcF
  have HbL := (plogTermAt_some_range _ _ _ _ Hlt).1
  imod snap_leadLog γ E m.src m.term ai bL l fp F HE HwF $$ Hinv Hp Hpf HrF HcFa
    with ⟨%l', %fp', #Hp', #Hpf', %Hk⟩
  obtain ⟨Hfull', HwL', HsF, Heq⟩ := Hk
  ihave #⟨-, #HrL'⟩ := leadPrefix_wf γ m.src m.term bL l' $$ Hp'
  ihave #Hpf1 := Hpf'
  iunfold lpfull at Hpf1
  icases Hpf1 with ⟨%F1, -, #Hfr', -⟩
  ihave #HrG := logRecs_full γ bL fp' l' Hfull' $$ Hfr' HrL'
  have HwG := full_wf _ _ _ Hfull' HwL'
  -- the commit fact and the committed prefix, moved to the leader log
  ihave #HcG := commitIn_move γ F (fp' ++ l') ai m.term m.term (Int.le_refl _) HwF HwG HsF Heq
    $$ HrF HrG HcFa
  icases full_take_eq γ F (fp' ++ l') ai HwF HwG HsF Heq.symm $$ HrF HrG with %Htk
  have Hci : (uint.Z ai).toNat ≤ (uint.Z c).toNat := by omega
  ihave #HcmFa := isCommitted_mono γ _ _ (List.take_prefix_take_left (l := F) Hci) $$ HcmF
  icases isCommitted_agree γ A _ $$ HA HcmFa with %Hpre
  obtain ⟨-, HFt⟩ := take_last_term F A ai at_ HwF HsF Hpre HAlen HAlast
  have HGt : plogTermAt base0 (fp' ++ l') ai = some at_ := by rw [Heq, HFt]
  have HLt : plogTermAt bL l' ai = some at_ := by
    rw [← full_term_at bL fp' l' ai Hfull' (by omega)]; exact HGt
  -- the snapshot's metadata names a real entry: the leader log's record at `ai`
  obtain ⟨e, He, Heix, Het⟩ := full_entry_of_term (fp' ++ l') ai at_ HwG HGt Hai0
  ihave ⟨%pt, -, #Hre⟩ := logRecs_lookup γ (fp' ++ l') (uint.Z ai - 1).toNat e He
    (by have := uint_Z_lt ai; omega) $$ HrG
  iunfold isMessage
  rw [Hty', Hsrc, Hterm, Hdst, Hix, Hlg]
  isplitr; · iexact Hl
  isplitr
  · unfold isSnapMeta
    iexists e
    isplitr
    · unfold isEntry; iexists pt; iexact Hre
    · ipureintro; exact ⟨Het, Heix⟩
  isplitr
  · iexists bL, l', fp'
    iframe Hp' Hpf' HcG
    isplitr; · ipureintro; exact HLt
    rw [← Htk]; iexact HcmFa
  isplitr; · ipureintro; exact Hnz
  ipureintro; exact Hds

end ghost

end EtcdGrove
end Perennial
