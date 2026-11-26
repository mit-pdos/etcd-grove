/- Lean-first (no Rocq counterpart).

# The crash-aware durability invariant's laws, proved (etcd-dist D6, task T2, 2026-11-24)

Proofs of `InvWalCrash.lean`'s statements: `rnDurK_crash_law_holds` (the crash), with the pure lemma
it needs (`walRead_snapSrc`: the snapshot of what a restart reads is one of the history's records, or
the records start at index `0`), and `walHistCerts_snapCert`/`walHistCertsK_snapCert` (hence the image's
certificate).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvWalCrashPure
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SrvCrash

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section pure
variable [GooseExts]

/-- **The records' snapshot comes from the history `A`**: they start at index `0`, or their
snapshot is (the metadata of) a snapshot record of `A` at their base. -/
def SnapSrc (A : WalHist) (σ : StorContents) : Prop :=
  (σ.b = 0 ∧ σ.snap = none) ∨ ∃ m al, WalOpG.snap m al ∈ A ∧ σ.snap = some (SnapshotM.mk [] m) ∧ uint.nat m.Index' = σ.b

theorem walFold_snapSrc (A : WalHist) :
    ∀ (H : WalHist) (τ σ : StorContents), (∀ o ∈ H, o ∈ A) → SnapSrc A τ →
      walFoldChkFrom τ H = some σ → SnapSrc A σ := by
  intro H
  induction H with
  | nil => intro τ σ _ hτ h; simp only [walFoldChkFrom, Option.some.injEq] at h; subst h; exact hτ
  | cons o H ih =>
    intro τ σ hA hτ h
    have hA' : ∀ o' ∈ H, o' ∈ A := fun o' ho' => hA o' (List.mem_cons_of_mem _ ho')
    cases o with
    | snap m al =>
      simp only [walFoldChkFrom] at h
      refine ih _ _ hA' ?_ h
      unfold walSaveSnap
      split
      · exact hτ
      · right
        exact ⟨m, al, hA _ List.mem_cons_self, rfl, rfl⟩
    | save hs es =>
      simp only [walFoldChkFrom, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨ents, -, h⟩ := h
      refine ih _ _ hA' ?_ h
      exact hτ

/-- **What a restart reads has a snapshot from the history read** (`SnapSrc`). -/
theorem walRead_snapSrc {I : WalHist} {σ : StorContents} (h : walRead I = some σ) : SnapSrc I σ := by
  unfold walRead at h
  refine walFold_snapSrc I _ walFresh σ (fun o ho => (List.mem_filter.1 ho).1) (Or.inl ⟨rfl, rfl⟩) h

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **A record set whose snapshot comes from a certified history is certified.** -/
theorem walHistCerts_snapCert (cl : Cluster) (sd : w64 → IProp GF) (Hs I : WalHist) (σ : StorContents)
    (hI : ∀ o ∈ I, o ∈ Hs) (hs : SnapSrc I σ) :
    walHistCerts (GF := GF) cl sd Hs ⊢ walSnapCert cl σ ∗ walSnapDur sd σ := by
  iintro #Hc
  iunfold walSnapCert
  iunfold walSnapDur
  rcases hs with ⟨hb, hn⟩ | ⟨m, al, hm, hsn, hidx⟩
  · isplitl
    · ileft; ipureintro; exact hb
    · ileft; ipureintro; exact hn
  · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 (hI _ hm)
    iunfold walHistCerts at Hc
    ihave #Hv := BigSepL.bigSepL_lookup (Φ := fun _ (o : WalOp) => walOpCert (GF := GF) cl sd o) hi $$ Hc
    iunfold walOpCert at Hv
    icases Hv with ⟨#Hv, #Hd⟩
    isplitl
    · iright
      iexists m
      iframe Hv
      ipureintro
      exact ⟨hsn, hidx⟩
    · iright
      iexists m
      iframe Hd
      ipureintro
      exact hsn

/-- (P5-RESTART, option (B), 2026-11-26) **A record set whose snapshot comes from a certified base or
from certified records is certified.** -/
theorem snapFrom_snapCert (cl : Cluster) (sd : w64 → IProp GF) (σ0 τ : StorContents) (X : WalHist)
    (hs : SnapFrom σ0 X τ) :
    walSnapCert (GF := GF) cl σ0 ∗ walSnapDur sd σ0 ∗ walHistCerts cl sd X ⊢
      walSnapCert cl τ ∗ walSnapDur sd τ := by
  iintro ⟨#Hc0, #Hd0, #Hc⟩
  rcases hs with ⟨hb, hsn⟩ | ⟨m, al, hm, hsn, hidx⟩
  · iunfold walSnapCert
    iunfold walSnapCert at Hc0
    iunfold walSnapDur
    iunfold walSnapDur at Hd0
    rw [hb, hsn]
    iframe Hc0 Hd0
  · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hm
    iunfold walHistCerts at Hc
    ihave #Hv := BigSepL.bigSepL_lookup (Φ := fun _ (o : WalOp) => walOpCert (GF := GF) cl sd o) hi $$ Hc
    iunfold walOpCert at Hv
    icases Hv with ⟨#Hv, #Hd⟩
    iunfold walSnapCert
    iunfold walSnapDur
    isplitl
    · iright
      iexists m
      iframe Hv
      ipureintro
      exact ⟨hsn, hidx⟩
    · iright
      iexists m
      iframe Hd
      ipureintro
      exact hsn

/-- (P5-RESTART, option (B), 2026-11-26) **The body's certificates give each crash prefix's**: the read of
a prefix from the synced lower bound on is certified (`certBaseK_read`, `snapFrom_snapCert`). -/
theorem walHistCertsK_snapCert (cl : Cluster) (sd : w64 → IProp GF) (Hs : WalHist) (n j : Nat)
    (τ : StorContents) (hnj : n ≤ j) (hj : j ≤ Hs.length) (hrd : walRead (Hs.take j) = some τ) :
    walHistCertsK (GF := GF) cl sd Hs n ⊢ walSnapCert cl τ ∗ walSnapDur sd τ := by
  iintro #Hk
  iunfold walHistCertsK at Hk
  icases Hk with ⟨%σ0, %k, %Hb, #Hc0, #Hd0, #Hc⟩
  obtain ⟨hkn, hb⟩ := Hb
  iapply snapFrom_snapCert cl sd σ0 τ (Hs.drop k) (certBaseK_read hb (by omega) hj hrd)
  iframe Hc0 Hd0 Hc

/-- **The certificates of a history give those of each of its prefixes.** -/
theorem walHistCerts_take (cl : Cluster) (sd : w64 → IProp GF) (Hs : WalHist) (j : Nat) :
    walHistCerts (GF := GF) cl sd Hs ⊢ walHistCerts cl sd (Hs.take j) := by
  have hs : walHistCerts (GF := GF) cl sd Hs = walHistCerts cl sd (Hs.take j ++ Hs.drop j) := by
    rw [List.take_append_drop]
  rw [hs]
  iintro #Hc
  iunfold walHistCerts at Hc
  ihave ⟨#Hc1, -⟩ := BigSepL.bigSepL_append.1 $$ Hc
  iunfold walHistCerts
  iexact Hc1

/-- `rnPendK` at a pending view, unfolded. -/
theorem rnPendK_some (γn : SrvRaft) (id : w64) (x : CrashNames) (v v0 : WalView) (γb : GName)
    (pos : Nat) :
    rnPendK (GF := GF) γn id x (v, some (v0, γb, pos)) =
      iprop(∃ (n : NodeH) (st st' : NodeDriverState) (ms : List QMsg) (q : Qp),
        savedPropOwn γb DFrac.discard (rnPendRec γn id x v0.S v.S n st st' ms q) ∗
        rnPendRec γn id x v0.S v.S n st st' ms q) := rfl

theorem rnLogLbsK_some (cl : Cluster) (v v0 : WalView) (γb : GName) (pos : Nat) :
    rnLogLbsK (GF := GF) cl (v, some (v0, γb, pos)) =
      iprop(isCommittedLogLb cl v.l ∗ isCommittedLogLb cl v0.l) := rfl

theorem rnLogLbsK_none (cl : Cluster) (v : WalView) :
    rnLogLbsK (GF := GF) cl (v, none) = iprop(isCommittedLogLb cl v.l ∗ True) := rfl

/-- **The crash** (`rnDurK_crash.law`; see its statement). -/
theorem rnDurK_crash_law_holds : rnDurK_crash.law (GF := GF) := by
  intro γn id νk h E Φ hE hE2
  letI := srvStor (GF := GF) γn
  iintro #Hinv #Hcl Hlc #Hcr Htk Hct Hwal
  iunfold rnDurInvK at Hinv
  icases Hinv with ⟨-, #Hinv⟩
  imod inv_acc (E := E) hE $$ Hinv with ⟨Hi, Hclose⟩
  imod lc_fupd_elim_later $$ Hlc Hi with Hi
  icases Hi with (Hb | ⟨Hs, Ha, Ho, #Htn⟩)
  rotate_left
  · -- the stop had taken the records
    imod Hclose $$ [Hs Ha Ho] with -
    · inext; iright; iframe Hs Ha Ho Htn
    imodintro; iright; iunfold rnTakenK; iexact Htn
  iunfold rnDurBodyK at Hb
  icases Hb with ⟨%vk, %σ, %Hs, %n, Hv, Hcm, Htn, Hr, #Hsc, #Hsy, #Hhc, #Hlb, %Hp, Hraft⟩
  obtain ⟨Hview, Hpo, Hho, Hrk⟩ := Hp
  have Hho0 := Hho
  obtain ⟨-, -, Hcrh, Hhr, -⟩ := Hho0
  icases Hraft with (⟨HrS, Hpend⟩ | ⟨-, Htk'⟩)
  rotate_left
  · iexfalso; iapply token_exclusive $$ Htk Htk'
  -- the WAL's crash, with the history borrowed
  imod Hwal $$ %Hs %n Hr Hsy with ⟨Hr, %j, %Hj, HΦ⟩
  obtain ⟨hnj, hjl⟩ := Hj
  obtain ⟨σ'', hrd, hok⟩ := Hcrh j hnj hjl
  ihave HΦ := HΦ $$ %σ'' %hrd
  have hrf : walReadFacts σ'' :=
    walReadFacts_of_read hrd (walIdxLe_take Hhr.1 j) (Hhr.2 j hnj hjl)
  -- the image's certificate
  ihave ⟨#Hcert, #Hsdur⟩ := walHistCertsK_snapCert γn.cl νk.sd Hs n j σ'' hnj hjl hrd $$ Hhc
  -- close with the crash's side
  imod Hclose $$ [Hv Hcm Htn Hr Htk] with -
  · inext; ileft; iunfold rnDurBodyK
    iexists vk, σ, Hs, n
    iframe Hv Hcm Htn Hr Hsc Hsy Hhc Hlb
    isplitr
    · ipureintro; exact ⟨Hview, Hpo, Hho, Hrk⟩
    iright; iframe Hcr Htk
  have hN : ↑srvClusterN ⊆ E := fun p hp => (Iris.Std.LawfulSet.mem_diff.1 (hE2 p hp)).1
  obtain ⟨v, pb⟩ := vk
  cases pb with
  | none =>
    dsimp only [durOf]
    imod nodeCrash γn.cl srvClusterN id νk.x E hN $$ Hcl Hcr Hct with Hvac
    imodintro
    ileft
    have hS : ImgOk v.S v.l σ'' := hok
    iexists v.S, σ'', v.l, Hs.take j
    iframe HΦ Hvac Hcert Hsdur
    rw [rnLogLbsK_none]
    icases Hlb with ⟨Hl, -⟩
    iframe Hl
    isplitl [HrS]
    · iexact HrS
    ipureintro
    exact ⟨hS.1, hS.2, Hview.2.2.2.2.1, hrf, hrd⟩
  | some p =>
    obtain ⟨v0, γb, pos⟩ := p
    dsimp only [durOf]
    rw [rnLogLbsK_some]
    icases Hlb with ⟨Hl, Hl0⟩
    simp only [crashOk] at hok
    by_cases hjp : j ≤ pos
    rotate_left
    · rw [if_neg hjp] at hok
      -- the image holds the batch: a crash enters it
      rw [rnPendK_some]
      icases Hpend with ⟨%nd, %st, %st', %ms, %q, -, Hrec⟩
      iunfold rnPendRec at Hrec
      icases Hrec with ⟨#Harm, Hent, Hrun, %Hst⟩
      obtain ⟨Hst1, Hst2⟩ := Hst
      ihave HrS : raftState γn.cl id st.durable $$ [HrS]
      · rw [Hst1]; iexact HrS
      imod readyCrashEnter nd γn.cl srvClusterN id st st' ms νk.x q E hN $$ Hcr Hct Harm Hrun Hent HrS
        with ⟨HrS, Hvac⟩
      imodintro
      ileft
      iexists v.S, σ'', v.l, Hs.take j
      iframe HΦ Hvac Hcert Hsdur Hl
      isplitl [HrS]
      · rw [← Hst2]; iexact HrS
      ipureintro
      exact ⟨hok.1, hok.2, Hview.2.2.2.2.1, hrf, hrd⟩
    · -- the image holds the state before it: a crash drops it
      rw [if_pos hjp] at hok
      imod nodeCrash γn.cl srvClusterN id νk.x E hN $$ Hcl Hcr Hct with Hvac
      imodintro
      ileft
      iexists v0.S, σ'', v0.l, Hs.take j
      iframe HΦ Hvac Hcert Hsdur Hl0
      isplitl [HrS]
      · iexact HrS
      ipureintro
      exact ⟨hok.1, hok.2, Hpo v0 γb pos rfl, hrf, hrd⟩

end defs

end EtcdGrove
end Perennial
