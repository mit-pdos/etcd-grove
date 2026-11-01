/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvdurable/Replica__persist.lean`, its first
spec (`persist.spec`). Lean-first (no Rocq counterpart).

Under `dmu`: crashed, nothing written; otherwise the image `M` encoded and written, the file's
invariant opened in `durable.Write`'s atomic update. A batch pending in `dmu` (`KdPhase.waiting`) is
entered there (its *enter* fired with the caller's share of `nodeRunning`), its results left in
`dmu` for `run` (`KdPhase.fired`); the file moves to `M` and the durable state to the one `M`
holds.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Replica__persist
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Storage__encode
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Stats__add
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.DefsLaws

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [durable_sem : github_com.mit_pdos.etcd_grove.examples.durable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KdStor GF]

attribute [local instance] kdStorageModel

/-- The replica's file's namespace is not the files'. -/
theorem kdRepN_files (id : w64) : (↑(kdRepN .@ uint.nat id) : CoPset) ⊆ ⊤ \ ↑kdFilesN :=
  nclose_subseteq' _ (mask_ndot_ne' nroot "kvdurable_rep" "kvdurable_files" (by decide))

/-- raft's namespace is open inside the file's update. -/
theorem kdRaftN_sub (id : w64) :
    (↑kdRaftN : CoPset) ⊆ (⊤ \ ↑kdFilesN) \ ↑(kdRepN .@ uint.nat id) := by
  intro p hp
  rw [Std.LawfulSet.mem_diff, Std.LawfulSet.mem_diff]
  refine ⟨⟨CoPset.mem_full, fun h' => ndot_ne_disjoint nroot
    (show "kvdurable_raft" ≠ "kvdurable_files" by decide) p ⟨hp, h'⟩⟩, fun h' => ndot_ne_disjoint nroot
    (show "kvdurable_raft" ≠ "kvdurable_rep" by decide) p ⟨hp, nclose_subseteq _ _ p h'⟩⟩

theorem Replica.persist.wp_proof
    (wp_encode : Storage.encode.spec (GF := GF) (hG := hG))
    (wp_Write : github_com.mit_pdos.etcd_grove.examples.durable.Write.spec (GF := GF) (hG := hG))
    (wp_add : Stats.add.spec (GF := GF) (hG := hG)) :
    Replica.persist.spec (GF := GF) (hG := hG) := by
  intro γ vs dir id r n st sts sq ms γs ph q
  wp_start as ⟨#Hrep, Hrun⟩
  ihave #Hrep' := Hrep
  iunfold isReplica at Hrep'
  iNamed Hrep'
  ihave #Hcl' := Hcl
  iunfold kdCluster at Hcl'
  icases Hcl' with ⟨-, -, -, -, -, #Hfiles⟩
  ihave #Hst' := Hstats
  iunfold isStats at Hst'
  ihave #Hfw := BigSepL.bigSepL_mem (x := go!"FileWrites") (by decide) $$ Hst'
  try wp_auto
  wp_apply (lc := 1) sync.Mutex.wp_Lock _ _ $$ [$Hdmu] as ⟨Hlocked, HR⟩
  iunfold kdDmuInv at HR
  iNamed HR
  try wp_auto
  cases crashed
  · -- not crashed: the image written
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Hlive with ⟨%S, %o, %pz, Hwr, %HMok, #Hcert, %Hfb, Hph⟩
    -- the new durable state, `M`'s, and the phase after the write: a pending batch is entered
    -- here and left `fired` for `run`
    ihave Hstep : iprop(∃ (S' : RaftState) (pz' : KdPhase), ⌜StorageHolds S' (kdContents (some M))⌝ ∗
        (∀ (E : CoPset), ⌜↑kdRaftN ⊆ E⌝ -∗ raftState γ.r.cluster id S ={E}=∗
          raftState γ.r.cluster id S' ∗ nodeRunning n γ.r.cluster kdRaftN q ∗
          kdPhaseInv γ id n ph.ph S' M pz')) $$ [Hph Hrun]
    · cases pz with
      | idle =>
        iunfold kdPhaseInv at Hph
        icases Hph with ⟨Hph, %HSM⟩
        iexists S, KdPhase.idle
        isplitr
        · ipureintro; exact HSM
        iintro %E %HE HrS
        imodintro
        iframe HrS Hrun
        simp only [kdPhaseInv]
        iframe Hph
        ipureintro; exact HSM
      | waiting st0 st0' ms0 γb0 =>
        iunfold kdPhaseInv at Hph
        icases Hph with ⟨Hph, #Hsv0, Henter, %Hst0⟩
        iexists st0'.durable, KdPhase.fired γb0
        isplitr
        · ipureintro; exact Hst0.2
        iintro %E %HE HrS
        iunfold readyEnter at Henter
        ihave HrS : raftState γ.r.cluster id st0.durable $$ [HrS]
        · rw [Hst0.1]; iexact HrS
        imod Henter $$ %E %q %HE [$HrS $Hrun] with ⟨HrS, Hrun, Hdrv, #Hmsgs⟩
        imodintro
        iframe HrS Hrun
        simp only [kdPhaseInv]
        iframe Hph
        isplitl
        · iexists kdBatchRes γ id n st0' ms0
          iframe Hsv0
          iunfold kdBatchRes
          iframe Hdrv Hmsgs
        ipureintro; exact Hst0.2
      | fired γb0 =>
        iunfold kdPhaseInv at Hph
        icases Hph with ⟨Hph, HR, %HSM⟩
        iexists S, KdPhase.fired γb0
        isplitr
        · ipureintro; exact HSM
        iintro %E %HE HrS
        imodintro
        iframe HrS Hrun
        simp only [kdPhaseInv]
        iframe Hph
        isplitl [HR]
        · iexact HR
        ipureintro; exact HSM
    icases Hstep with ⟨%S', %pz', %HSM, Hstep⟩
    try wp_auto
    wp_apply wp_encode st ip M $$ [$Hpkg $Himg $Himage] as %sl ⟨Hsl, -, Himage⟩
    wp_apply wp_bytes_to_string sl (encStor M) (DFrac.own 1) $$ [$Hsl] as -
    try wp_auto
    wp_bind (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.durable.Write)) _) _)
    iapply github_com.mit_pdos.etcd_grove.examples.durable.Write.wp_file_au wp_Write γ.files kdFilesN
      _ _ _ $$ Hfiles
    iunfold kdFileInv at HfInv
    iinv HfInv with HI Hclose
    · exact kdRepN_files id
    imod lc_fupd_elim_later $$ Hlc1 HI with HI
    icases HI with ⟨%S0, %o0, HrS, Hdf, Hwv, %HSH, HcF⟩
    iunfold kdWriter at Hwr
    ihave %Hag := ghostVar_agree (γ.wr id) _ _ _ _ $$ Hwr Hwv
    obtain ⟨rfl, -⟩ := Prod.mk.inj Hag
    imod Hstep $$ %_ %(kdRaftN_sub id) HrS with ⟨HrS, Hrun, Hph⟩
    imod ghostVar_update_halves (S', kdFileVal (some M)) (γ.wr id) _ _ $$ Hwr Hwv with ⟨Hwr, Hwv⟩
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    iexists kdFileVal o0
    iframe Hdf
    iintro Hdf
    imod Hmask with -
    imod Hclose $$ [HrS Hdf Hwv] with -
    · inext
      iexists S', some M
      iframe HrS Hwv
      simp only [kdFileVal, Option.map_some]
      iframe Hdf
      isplitl []
      · ipureintro; exact ⟨HSM, fun f hf => by cases hf; exact HMok⟩
      iintro %f %hf
      cases hf
      iexact Hcert
    imodintro
    try wp_auto
    wp_apply wp_add sts _ $$ [$Hpkg $Hfw]
    try wp_auto
    wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hdmu $Hlocked Hcr Himage Hmeta Hic His Hcm Hwr Hph]
    · inext
      iunfold kdDmuInv
      iexists false, ip, M, fz
      iframe Hcr Himg Himage Hmeta Hic Hfz His Hcm
      isplitr
      · ipureintro; exact Hfzc
      simp only [Bool.false_eq_true, ↓reduceIte]
      iexists S', some M, pz'
      iunfold kdWriter
      iframe Hwr Hcert Hph
      ipureintro; exact ⟨HMok, fun f hf => by cases hf; exact Nat.le_refl _⟩
    try wp_auto
    iapply HΦ
    iframe Hrun
  · -- crashed: nothing written
    try wp_auto
    wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hdmu $Hlocked Hcr Himage Hmeta Hic His Hcm Hlive]
    · inext
      iunfold kdDmuInv
      iexists true, ip, M, fz
      iframe Hcr Himg Himage Hmeta Hic Hfz His Hcm Hlive
      ipureintro; exact Hfzc
    try wp_auto
    iapply HΦ
    iframe Hrun

/-- `persist.specRun`: `run`'s write of its pending batch (see the spec's header). The phase is
`waiting` (the batch is entered here, in the file's update) or `fired` (by the snapshotter's write);
either way its results, saved at `γb`, go to `run`, and the phase is idle again. -/
theorem Replica.persist.wp_proofRun
    (wp_encode : Storage.encode.spec (GF := GF) (hG := hG))
    (wp_Write : github_com.mit_pdos.etcd_grove.examples.durable.Write.spec (GF := GF) (hG := hG))
    (wp_add : Stats.add.spec (GF := GF) (hG := hG)) :
    Replica.persist.specRun (GF := GF) (hG := hG) := by
  intro γ vs dir id r n st sts sq ms γs ph q st' qs γb
  wp_start as ⟨#Hrep, Hrun, Hclaim, #HsvC⟩
  ihave #Hrep' := Hrep
  iunfold isReplica at Hrep'
  iNamed Hrep'
  ihave #Hcl' := Hcl
  iunfold kdCluster at Hcl'
  icases Hcl' with ⟨-, -, -, -, -, #Hfiles⟩
  ihave #Hst' := Hstats
  iunfold isStats at Hst'
  ihave #Hfw := BigSepL.bigSepL_mem (x := go!"FileWrites") (by decide) $$ Hst'
  try wp_auto
  wp_apply (lc := 2) sync.Mutex.wp_Lock _ _ $$ [$Hdmu] as ⟨Hlocked, HR⟩
  iunfold kdDmuInv at HR
  iNamed HR
  try wp_auto
  cases crashed
  · -- not crashed: the image written, the batch's results to `run`
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Hlive with ⟨%S, %o, %pz, Hwr, %HMok, #Hcert, %Hfb, Hph⟩
    iunfold kdPhaseInv at Hph
    -- the new durable state, the file's, `M`'s; and the batch's results, as `run` saved them
    ihave Hstep : iprop(∃ S' : RaftState, ⌜StorageHolds S' (kdContents (some M)) ∧ S' = st'.durable⌝ ∗
        ghostVar ph.ph (1 : Qp).half (some γb, st'.durable) ∗
        ghostVar ph.ph (1 : Qp).half (some γb, st'.durable) ∗
        (∀ (E : CoPset), ⌜↑kdRaftN ⊆ E⌝ -∗ £ 1 -∗ raftState γ.r.cluster id S ={E}=∗
          raftState γ.r.cluster id S' ∗ nodeRunning n γ.r.cluster kdRaftN q ∗
          kdBatchRes γ id n st' qs)) $$ [Hph Hclaim Hrun]
    · cases pz with
      | idle =>
        icases Hph with ⟨Hph, -⟩
        ihave %Hag := ghostVar_agree ph.ph _ _ _ _ $$ Hph Hclaim
        obtain ⟨h, -⟩ := Prod.mk.inj Hag
        cases h
      | waiting st0 st0' ms0 γb0 =>
        icases Hph with ⟨Hph, #Hsv0, Henter, %Hst0⟩
        ihave %Hag := ghostVar_agree ph.ph _ _ _ _ $$ Hph Hclaim
        obtain ⟨h1, h2⟩ := Prod.mk.inj Hag
        obtain rfl := Option.some.inj h1
        iexists st'.durable
        ihave Hph : ghostVar ph.ph (1 : Qp).half (some γb0, st'.durable) $$ [Hph]
        · rw [← h2]; iexact Hph
        iframe Hph Hclaim
        isplitr
        · ipureintro; exact ⟨h2 ▸ Hst0.2, rfl⟩
        iintro %E %HE Hlc HrS
        iunfold readyEnter at Henter
        ihave HrS : raftState γ.r.cluster id st0.durable $$ [HrS]
        · rw [Hst0.1]; iexact HrS
        imod Henter $$ %E %q %HE [$HrS $Hrun] with ⟨HrS, Hrun, Hdrv, #Hmsgs⟩
        ihave #Heq := saved_prop_agree γb0 DFrac.discard DFrac.discard _ _ $$ Hsv0 HsvC
        ihave HA : ▷ kdBatchRes γ id n st' qs $$ [Hdrv]
        · inext
          ihave Hiff := internalEq_iff _ _ $$ Heq
          icases Hiff with ⟨Hiff, -⟩
          iapply Hiff
          iunfold kdBatchRes
          iframe Hdrv Hmsgs
        imod lc_fupd_elim_later $$ Hlc HA with HA
        imodintro
        ihave HrS : raftState γ.r.cluster id st'.durable $$ [HrS]
        · rw [← h2]; iexact HrS
        iframe HrS Hrun HA
      | fired γb0 =>
        icases Hph with ⟨Hph, ⟨%R, #HsvR, HRR⟩, %HSM⟩
        ihave %Hag := ghostVar_agree ph.ph _ _ _ _ $$ Hph Hclaim
        obtain ⟨h1, h2⟩ := Prod.mk.inj Hag
        obtain rfl := Option.some.inj h1
        iexists S
        rw [← h2]
        iframe Hph Hclaim
        isplitr
        · ipureintro; exact ⟨HSM, rfl⟩
        iintro %E %HE Hlc HrS
        ihave #Heq := saved_prop_agree γb0 DFrac.discard DFrac.discard _ _ $$ HsvR HsvC
        ihave HA : ▷ kdBatchRes γ id n st' qs $$ [HRR]
        · inext
          ihave Hiff := internalEq_iff _ _ $$ Heq
          icases Hiff with ⟨Hiff, -⟩
          iapply Hiff $$ HRR
        imod lc_fupd_elim_later $$ Hlc HA with HA
        imodintro
        iframe HrS Hrun HA
    icases Hstep with ⟨%S', ⟨%HSM, %HS'⟩, Hph, Hclaim, Hstep⟩
    subst HS'
    try wp_auto
    wp_apply wp_encode st ip M $$ [$Hpkg $Himg $Himage] as %sl ⟨Hsl, -, Himage⟩
    wp_apply wp_bytes_to_string sl (encStor M) (DFrac.own 1) $$ [$Hsl] as -
    try wp_auto
    wp_bind (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.durable.Write)) _) _)
    iapply github_com.mit_pdos.etcd_grove.examples.durable.Write.wp_file_au wp_Write γ.files kdFilesN
      _ _ _ $$ Hfiles
    iunfold kdFileInv at HfInv
    iinv HfInv with HI Hclose
    · exact kdRepN_files id
    imod lc_fupd_elim_later $$ Hlc1 HI with HI
    icases HI with ⟨%S0, %o0, HrS, Hdf, Hwv, %HSH, HcF⟩
    iunfold kdWriter at Hwr
    ihave %Hag := ghostVar_agree (γ.wr id) _ _ _ _ $$ Hwr Hwv
    obtain ⟨rfl, -⟩ := Prod.mk.inj Hag
    imod Hstep $$ %_ %(kdRaftN_sub id) Hlc2 HrS with ⟨HrS, Hrun, HA⟩
    imod ghostVar_update_halves (st'.durable, kdFileVal (some M)) (γ.wr id) _ _ $$ Hwr Hwv with ⟨Hwr, Hwv⟩
    imod ghostVar_update_halves ((none : Option GName), st'.durable) ph.ph _ _ $$ Hph Hclaim
      with ⟨Hph, Hclaim⟩
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    iexists kdFileVal o0
    iframe Hdf
    iintro Hdf
    imod Hmask with -
    imod Hclose $$ [HrS Hdf Hwv] with -
    · inext
      iexists st'.durable, some M
      iframe HrS Hwv
      simp only [kdFileVal, Option.map_some]
      iframe Hdf
      isplitl []
      · ipureintro; exact ⟨HSM, fun f hf => by cases hf; exact HMok⟩
      iintro %f %hf
      cases hf
      iexact Hcert
    imodintro
    try wp_auto
    wp_apply wp_add sts _ $$ [$Hpkg $Hfw]
    try wp_auto
    wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hdmu $Hlocked Hcr Himage Hmeta Hic His Hcm Hwr Hph]
    · inext
      iunfold kdDmuInv
      iexists false, ip, M, fz
      iframe Hcr Himg Himage Hmeta Hic Hfz His Hcm
      isplitr
      · ipureintro; exact Hfzc
      simp only [Bool.false_eq_true, ↓reduceIte]
      iexists st'.durable, some M, KdPhase.idle
      iunfold kdWriter
      iframe Hwr Hcert
      isplitr
      · ipureintro; exact HMok
      isplitr
      · ipureintro; intro f hf; cases hf; exact Nat.le_refl _
      simp only [kdPhaseInv]
      iframe Hph
      ipureintro; exact HSM
    try wp_auto
    iapply HΦ
    simp only [↓reduceIte]
    iframe Hrun Hclaim HA
  · -- crashed: nothing written, the claim kept
    try wp_auto
    wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hdmu $Hlocked Hcr Himage Hmeta Hic His Hcm Hlive]
    · inext
      iunfold kdDmuInv
      iexists true, ip, M, fz
      iframe Hcr Himg Himage Hmeta Hic Hfz His Hcm Hlive
      ipureintro; exact Hfzc
    try wp_auto
    iapply HΦ
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe Hrun Hclaim

end proof

end kvdurable
end EtcdGrove
end Perennial
