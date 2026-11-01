/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvdurable/Replica__persist.lean`, its first
spec (`persist.spec`). Lean-first (no Rocq counterpart).

Under `dmu`: crashed, nothing written; otherwise the image `M` encoded and written, the file's
invariant opened in `durable.Write`'s atomic update. With the caller's claim at `none` (the pending
phase's variable), `dmu`'s phase is idle (`kdPhaseInv .idle`: the others hold the claim at `some`),
so the file's durable state `S` is the one `M` holds: the file moves to `M`, `S` stays.
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

theorem Replica.persist.wp_proof
    (wp_encode : Storage.encode.spec (GF := GF) (hG := hG))
    (wp_Write : github_com.mit_pdos.etcd_grove.examples.durable.Write.spec (GF := GF) (hG := hG))
    (wp_add : Stats.add.spec (GF := GF) (hG := hG)) :
    Replica.persist.spec (GF := GF) (hG := hG) := by
  intro γ vs dir id r n st sts sq ms γs ph q
  wp_start as ⟨#Hrep, Hrun, Hclaim⟩
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
    icases Hlive with ⟨%S, %o, %pz, Hwr, %HMok, #Hcert, Hph⟩
    -- the phase is idle: the caller's claim is `none`
    cases pz with
    | waiting st0 st0' ms0 γb0 =>
      iunfold kdPhaseInv at Hph
      icases Hph with ⟨Hph, -⟩
      ihave %Hag := ghostVar_agree ph _ _ _ _ $$ Hph Hclaim
      cases Hag
    | fired γb0 =>
      iunfold kdPhaseInv at Hph
      icases Hph with ⟨Hph, -⟩
      ihave %Hag := ghostVar_agree ph _ _ _ _ $$ Hph Hclaim
      cases Hag
    | idle =>
    iunfold kdPhaseInv at Hph
    icases Hph with ⟨Hph, %HSM⟩
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
    imod ghostVar_update_halves (S, kdFileVal (some M)) (γ.wr id) _ _ $$ Hwr Hwv with ⟨Hwr, Hwv⟩
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    iexists kdFileVal o0
    iframe Hdf
    iintro Hdf
    imod Hmask with -
    imod Hclose $$ [HrS Hdf Hwv] with -
    · inext
      iexists S, some M
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
    wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hdmu $Hlocked Hcr Himage Hmeta Hwr Hph]
    · inext
      iunfold kdDmuInv
      iexists false, ip, M
      iframe Hcr Himg Himage Hmeta
      simp only [Bool.false_eq_true, ↓reduceIte]
      iexists S, some M, KdPhase.idle
      iunfold kdWriter
      iframe Hwr Hcert
      isplitr
      · ipureintro; exact HMok
      simp only [kdPhaseInv]
      iframe Hph
      ipureintro; exact HSM
    try wp_auto
    iapply HΦ
    iframe Hrun Hclaim
  · -- crashed: nothing written
    try wp_auto
    wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hdmu $Hlocked Hcr Himage Hmeta]
    · inext
      iunfold kdDmuInv
      iexists true, ip, M
      iframe Hcr Himg Himage Hmeta
      simp only [↓reduceIte]
      itrivial
    try wp_auto
    iapply HΦ
    iframe Hrun Hclaim

/-- raft's namespace is open inside the file's update. -/
theorem kdRaftN_sub (id : w64) :
    (↑kdRaftN : CoPset) ⊆ (⊤ \ ↑kdFilesN) \ ↑(kdRepN .@ uint.nat id) := by
  intro p hp
  rw [Std.LawfulSet.mem_diff, Std.LawfulSet.mem_diff]
  refine ⟨⟨CoPset.mem_full, fun h' => ndot_ne_disjoint nroot
    (show "kvdurable_raft" ≠ "kvdurable_files" by decide) p ⟨hp, h'⟩⟩, fun h' => ndot_ne_disjoint nroot
    (show "kvdurable_raft" ≠ "kvdurable_rep" by decide) p ⟨hp, nclose_subseteq _ _ p h'⟩⟩

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
    icases Hlive with ⟨%S, %o, %pz, Hwr, %HMok, #Hcert, Hph⟩
    iunfold kdPhaseInv at Hph
    -- the new durable state, the file's, `M`'s; and the batch's results, as `run` saved them
    ihave Hstep : iprop(∃ S' : RaftState, ⌜StorageHolds S' (kdContents (some M))⌝ ∗
        ghostVar ph (1 : Qp).half (some γb) ∗ ghostVar ph (1 : Qp).half (some γb) ∗
        (∀ (E : CoPset), ⌜↑kdRaftN ⊆ E⌝ -∗ £ 1 -∗ raftState γ.r.cluster id S ={E}=∗
          raftState γ.r.cluster id S' ∗ nodeRunning n γ.r.cluster kdRaftN q ∗
          kdBatchRes γ id n st' qs)) $$ [Hph Hclaim Hrun]
    · cases pz with
      | idle =>
        icases Hph with ⟨Hph, -⟩
        ihave %Hag := ghostVar_agree ph _ _ _ _ $$ Hph Hclaim
        cases Hag
      | waiting st0 st0' ms0 γb0 =>
        icases Hph with ⟨Hph, #Hsv0, Henter, %Hst0⟩
        ihave %Hag := ghostVar_agree ph _ _ _ _ $$ Hph Hclaim
        obtain rfl := Option.some.inj Hag
        iexists st0'.durable
        iframe Hph Hclaim
        isplitr
        · ipureintro; exact Hst0.2
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
        iframe HrS Hrun HA
      | fired γb0 =>
        icases Hph with ⟨Hph, ⟨%R, #HsvR, HRR⟩, %HSM⟩
        ihave %Hag := ghostVar_agree ph _ _ _ _ $$ Hph Hclaim
        obtain rfl := Option.some.inj Hag
        iexists S
        iframe Hph Hclaim
        isplitr
        · ipureintro; exact HSM
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
    icases Hstep with ⟨%S', %HSM, Hph, Hclaim, Hstep⟩
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
    imod ghostVar_update_halves (S', kdFileVal (some M)) (γ.wr id) _ _ $$ Hwr Hwv with ⟨Hwr, Hwv⟩
    imod ghostVar_update_halves (none : Option GName) ph _ _ $$ Hph Hclaim with ⟨Hph, Hclaim⟩
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
    wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hdmu $Hlocked Hcr Himage Hmeta Hwr Hph]
    · inext
      iunfold kdDmuInv
      iexists false, ip, M
      iframe Hcr Himg Himage Hmeta
      simp only [Bool.false_eq_true, ↓reduceIte]
      iexists S', some M, KdPhase.idle
      iunfold kdWriter
      iframe Hwr Hcert
      isplitr
      · ipureintro; exact HMok
      simp only [kdPhaseInv]
      iframe Hph
      ipureintro; exact HSM
    try wp_auto
    iapply HΦ
    simp only [↓reduceIte]
    iframe Hrun Hclaim HA
  · -- crashed: nothing written, the claim kept
    try wp_auto
    wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hdmu $Hlocked Hcr Himage Hmeta]
    · inext
      iunfold kdDmuInv
      iexists true, ip, M
      iframe Hcr Himg Himage Hmeta
      simp only [↓reduceIte]
      itrivial
    try wp_auto
    iapply HΦ
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe Hrun Hclaim

end proof

end kvdurable
end EtcdGrove
end Perennial
