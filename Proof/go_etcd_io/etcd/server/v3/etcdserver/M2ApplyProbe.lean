/-
**M2, the apply side: the Probe's proofs** (`notes/m2-apply-plan.md`, "The Probe"; 2026-10-31).
Imported by nothing (as the Drafts): the first proofs over the approved drafted statements, to test
that they are provable before the switch.

* **The commit step (G4, item 6)**: a compaction proposal's update over the KV invariant in the
  cluster's mode (`kv_prop_au_cmp`, `reqPropOkD`'s compaction form). Its leading step
  (`cmpReach_reqLb`), at the caller's mask, reads the proposer's KV certificate through the
  certificates' invariant (`kvCertInv`) and turns it into a lower bound of the server's log of
  requested entries (`srvReqLogLb_of_rlogLb`); inside the update the lower bound is a prefix of the
  committed log (`srvReqLogLb_prefix`), where the invariant records the compaction's claim
  (`cmpLogOk`): its revision one of the model's before the entry.

Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.M2ApplyDraft
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section pure
variable [GooseExts]

/-- The claims, one entry on. -/
theorem cmpLogOk_snoc (γk : KVNames) (cmp : Bool) (L : List EntryModel) (e : EntryModel)
    (h : cmpLogOk γk cmp L) (he : cmpEntryOk γk cmp L e) : cmpLogOk γk cmp (L ++ [e]) := by
  intro i m hi
  have hil := (List.getElem?_eq_some_iff.1 hi).1
  simp only [List.length_append, List.length_singleton] at hil
  rcases Nat.lt_or_ge i L.length with hlt | hge
  · rw [List.getElem?_append_left hlt] at hi
    rw [List.take_append_of_le_length (Nat.le_of_lt hlt)]
    exact h i m hi
  · have hi' : i = L.length := by omega
    subst hi'
    simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero,
      Option.some.injEq] at hi
    subst hi
    simpa using he

/-- A compaction is no write: the model's log and state stay. -/
theorem compactPropOkD_nonwrite (rq : apply.IRRModel) (h : compactPropOkD rq) :
    ¬ writeKind (apply.dispatchKind rq) := by
  rw [h.1.1]
  unfold writeKind
  simp

end pure

section probe
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The workload facts, one entry on**, under item 1 (`kvWork_snoc` over `kvWorkD`). -/
theorem kvWorkD_snoc (cfg : SrvRaft) (γk : KVNames) (L : List EntryModel) (e : EntryModel)
    (hs : entryShapeD e) (hc : e.typ ≠ W32 0 → ccPolOk cfg e.data) :
    ⊢ kvWorkD (GF := GF) cfg γk L -∗ entryClaim γk.ids e -∗ kvWorkD cfg γk (L ++ [e]) := by
  iintro Hw #He
  iunfold kvWorkD at Hw
  icases Hw with ⟨%Hsh, #Hcl⟩
  iunfold kvWorkD
  isplitr
  · ipureintro
    refine ⟨fun m hm => ?_, fun m hm => ?_⟩
    · rw [List.mem_append, List.mem_singleton] at hm
      rcases hm with hm | hm
      · exact Hsh.1 m hm
      · subst hm; exact hs
    · rw [List.mem_append, List.mem_singleton] at hm
      rcases hm with hm | hm
      · exact Hsh.2 m hm
      · subst hm; exact hc
  iapply BigSepL.bigSepL_snoc.2
  iframe Hcl He

/-- **The commit step's leading step** (item 6, review rounds 5-6): a compaction's revision reached
(`cmpReach`, a KV certificate) gives a lower bound `L₀` of the server's log of requested entries
whose model has the revision (given the invariant's `c0 ≤ ai0`, which `kvModel_eqv` needs). At the
caller's mask: it opens the certificates' invariant and the server's raft log's, never the KV
invariant. -/
theorem cmpReach_reqLb (γ : ServerRaftNames) (γk : KVNames) (E : CoPset)
    (hE1 : ↑kvcN ⊆ E) (hE2 : ↑srvRaftN ⊆ E) (r : w64) :
    ⊢ kvCertInv (GF := GF) γ γk -∗ srvRaftLogInv γ -∗ cmpReach γk r ={E}=∗
      ∃ L₀, srvReqLogLb γ L₀ ∗
        ⌜uint.Z γk.c0 ≤ uint.Z γ.ai0 → sint.Z r < (kvModel γk L₀).length⌝ := by
  iintro #Hci #Hrl #Hr
  iunfold cmpReach at Hr
  icases Hr with ⟨%l, #Hc, %Hl⟩
  ihave #Hci' := Hci
  iunfold kvCertInv at Hci'
  iunfold kvCert at Hc
  icases Hc with (%h | #He)
  · -- one of the start's two revisions: below the start log's (at least two revisions)
    iinv Hci' with >Hi Hclose
    icases Hi with ⟨%C, %hi, %Lb, HC, Hhi', #HLb, %Hok⟩
    imod Hclose $$ [HC Hhi'] with -
    · inext; iexists C, hi, Lb; iframe HC Hhi' HLb; ipureintro; exact Hok
    imod srvReqLogLb_nil γ with #H0
    imodintro
    iexists []
    iframe H0
    ipureintro
    intro _
    have h0 : kvModel γk [] = γk.log0 := rfl
    rw [h0]
    have := Hok.2
    omega
  · -- an element of the map: the model of a committed raft log, read as requested entries
    iinv Hci' with >Hi Hclose
    icases Hi with ⟨%C, %hi, %Lb, HC, Hhi', #HLb, %Hok⟩
    ihave %Hm := ghost_map_lookup $$ HC He
    imod Hclose $$ [HC Hhi'] with -
    · inext; iexists C, hi, Lb; iframe HC Hhi' HLb; ipureintro; exact Hok
    obtain ⟨-, -, -, A, hA, hm⟩ := Hok.1 _ _ Hm
    ihave #HA := srvRLogLb_mono γ A Lb hA $$ HLb
    imod (srvReqLogLb_of_rlogLb γ E hE2 A) $$ Hrl HA with ⟨%L₀, #HL0, %Heqv⟩
    imodintro
    iexists L₀
    iframe HL0
    ipureintro
    intro hc
    rw [← (kvModel_eqv γ γk A L₀ Heqv hc).1, hm]
    exact Hl

/-- **The commit step (G4): a compaction proposal's update** over the KV invariant in the cluster's
mode `cmp` (`reqPropOkD`'s compaction form: `cmp = true`, in M2's scope, of a good shape, at a
reached revision `r`), for data claimed under the request's id, as today's `kv_prop_au`'s arms.
The entry leaves the model (a compaction is no write: `kvModelSt_snoc_nonwrite`), is plain in the
mode (`plainLogM`), and its claim (`cmpEntryOk`) is the leading step's bound, placed below the
committed log. The result is `True`. -/
theorem kv_prop_au_cmp (γ : ServerRaftNames) (γk : KVNames) (cmp : Bool) (d : List w8)
    (rq : apply.IRRModel) (hdec : apply.irrDecode d = some rq)
    (id : w64) (γf : GName) (hid : apply.irrId rq = some id)
    (E : CoPset) (hE1 : ↑kvcN ⊆ E) (hE2 : ↑srvRaftN ⊆ E)
    (r : w64) (hr : rq.compaction = some r)
    (hform : cmp = true ∧ compactPropOkD rq ∧ rqShapeD rq) :
    ⊢ kvInvD (GF := GF) γ γk cmp -∗ kvCertInv γ γk -∗ srvRaftLogInv γ -∗
      idClaim γk.ids id d γf -∗ idRegd γk.ids id -∗ cmpReach γk r ={E}=∗
      srvPropAu1 γ d (fun _ => iprop(True)) := by
  have Hdisj := kvN_raftN
  iintro #Hinv #Hci #Hrl #Hcl #Hreg #Hr
  imod (cmpReach_reqLb γ γk E hE1 hE2 r) $$ Hci Hrl Hr with ⟨%L₀, #HL0, %HL0r⟩
  imodintro
  unfold srvPropAu1
  iauintro
  unfold atomic_acc
  iunfold kvInvD at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%L, HL, Hσ, %Hok, #Hw⟩
  -- the leading step's bound is below the committed log
  icases srvReqLogLb_prefix γ L L₀ $$ [$HL $HL0] with ⟨HL, %Hpre⟩
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  iexists L
  iframe HL
  isplit
  · iintro HL
    imod Hmask with -
    imod Hclose $$ [HL Hσ] with -
    · inext; iexists L; iframe HL Hσ Hw; ipureintro; exact Hok
    imodintro
    itrivial
  · iintro %e ⟨%He, HL⟩
    imod Hmask with -
    obtain ⟨het, hed, hidx⟩ := He
    have hidx' := srvIdxOkW_snoc γ.ai0 L e Hok.2.1 hidx (Or.inl het)
    have hent : kvModelSt γk (L ++ [e]) = kvModelSt γk L := by
      apply kvModelSt_snoc_nonwrite
      right; right
      intro rq' h
      rw [hed, hdec] at h
      cases h
      exact compactPropOkD_nonwrite rq hform.2.1
    -- the entry's claim: its revision one of the model's before it
    have hclaim : cmpEntryOk γk cmp L e := by
      intro _ _ rq' h _
      rw [hed, hdec] at h
      cases h
      refine ⟨hform.1, hform.2.1, fun r' hr' => ?_⟩
      rw [hr] at hr'
      cases hr'
      have h1 := HL0r Hok.2.2.1
      have h2 := (kvRaftOf_prefix γk.c0 γk.ch0 γk.log0 L₀ L Hpre).length_le
      unfold kvModel at h1 ⊢
      omega
    -- plain in the mode: a compaction in M2's scope
    have hplain : plainEntryM cmp e := by
      intro _ _ rq' h
      rw [hed, hdec] at h
      cases h
      exact Or.inr ⟨hform.1, hform.2.1⟩
    have hsh : entryShapeD e :=
      ⟨fun _ => Or.inr ⟨rq, by rw [hed]; exact hdec, ⟨id, hid⟩, hform.2.2⟩, fun h => absurd het h⟩
    ihave #Hecl : entryClaim γk.ids e $$ []
    · iunfold entryClaim
      iright
      iexists rq, id, γf
      rw [hed]
      iframe Hcl Hreg
      ipureintro; exact ⟨hdec, hid⟩
    ihave #Hw' := kvWorkD_snoc γ.raft γk L e hsh (fun h => absurd het h) $$ Hw Hecl
    imod Hclose $$ [HL Hσ] with -
    · inext
      iexists L ++ [e]
      rw [hent]
      iframe HL Hσ Hw'
      ipureintro
      obtain ⟨hpl, -, hc0, hch, h0, hcl⟩ := Hok
      refine ⟨fun m hm => ?_, hidx', hc0, hch, h0, cmpLogOk_snoc γk cmp L e hcl hclaim⟩
      rw [List.mem_append, List.mem_singleton] at hm
      rcases hm with hm | hm
      · exact hpl m hm
      · subst hm; exact hplain
    imodintro
    iintro !>
    itrivial

end probe

end EtcdGrove
end Perennial
