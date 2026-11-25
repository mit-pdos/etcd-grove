/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvraft/Replica__persist.lean`. Lean-first (no Rocq
counterpart). Under `dmu`: the image `M` encoded and written with the bodied `durable.Write` (over fsExt),
whose atomic updates are `kd_writeAU`'s (`PersistLemmas.lean`): the pending batch of `dmu`'s phase, if any,
moves into the file's invariant at the rename and is entered at the sync. `persist.spec` leaves it
`fired` for `run`; `persist.specRun` (`run`'s own batch) takes its results back, by the saved
proposition's agreement, and leaves the phase `idle`.
-/
module

public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Replica__persist
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Storage__encode
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Stats__add
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.lib.durable.Write
public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.PersistLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]
variable [durable_sem : github_com.mit_pdos.etcd_grove.examples.lib.durable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [KdStor GF]
variable [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]

attribute [local instance] kdStorageModel

theorem Replica.persist.wp_proof
    (wp_encode : Storage.encode.spec (GF := GF) (hG := hG))
    (wp_Write : github_com.mit_pdos.etcd_grove.examples.lib.durable.Write.spec (GF := GF) (hG := hG))
    (wp_add : Stats.add.spec (GF := GF) (hG := hG)) :
    Replica.persist.spec (GF := GF) (hG := hG) := by
  intro γ vs dir id r n st sts sq ms γs ph q
  wp_start as ⟨#Hrep, Hrun⟩
  ihave #Hrep' := Hrep
  iunfold isReplica at Hrep'
  iNamed Hrep'
  ihave #Hdur : isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.durable
    $$ []
  · iPkgInit
  try wp_auto
  wp_apply (lc := 2) sync.Mutex.wp_Lock _ _ $$ [$Hdmu] as ⟨Hlocked, HR⟩
  iunfold kdDmuInv at HR
  iNamed HR
  icases Hlive with ⟨%S, %o, %pz, Hwr, %HMok, #Hcert, %Hfb, Hph⟩
  icases Hcpm with ⟨%qc, Hcpm⟩
  -- the pending batch: what the write takes, what it leaves, and the phase after it
  ihave Hpz : iprop(∃ pb : Option (GName × RaftState × Qp), kdRunKeep γ n q pb ∗ ⌜pbQ q pb = q⌝ ∗
      ⌜StorageHolds (pbTarget S pb) (kdContents (some M))⌝ ∗ kdPendIn γ id n S pb ∗
      (kdPendOut pb -∗ ∃ pz', kdPhaseInv γ id n ph.ph (pbTarget S pb) M pz')) $$ [Hph Hrun]
  · cases pz with
    | idle =>
      iunfold kdPhaseInv at Hph
      icases Hph with ⟨Hph, %HSM⟩
      iexists none
      isplitl [Hrun]
      · iunfold kdRunKeep; iexact Hrun
      isplitr
      · ipureintro; rfl
      isplitr
      · ipureintro; exact HSM
      isplitr
      · iunfold kdPendIn; iempintro
      iintro -
      iexists KdPhase.idle
      rw [show pbTarget S none = S from rfl]
      simp only [kdPhaseInv]
      iframe Hph
      ipureintro; exact HSM
    | waiting st0 st0' ms0 γb0 =>
      iunfold kdPhaseInv at Hph
      icases Hph with ⟨Hph, #Hsv0, Henter, %Hst0⟩
      iexists some (γb0, st0'.durable, q)
      isplitr
      · iunfold kdRunKeep; iempintro
      isplitr
      · ipureintro; rfl
      isplitr
      · ipureintro; exact Hst0.2
      isplitl [Henter Hrun]
      · iunfold kdPendIn
        iexists st0, st0', ms0
        iframe Henter Hrun Hsv0
        ipureintro; exact ⟨Hst0.1, rfl⟩
      iintro Hout
      iexists KdPhase.fired γb0
      rw [show pbTarget S (some (γb0, st0'.durable, q)) = st0'.durable from rfl]
      simp only [kdPhaseInv]
      rw [show kdPendOut (GF := GF) (some (γb0, st0'.durable, q)) =
        iprop(∃ R : IProp GF, savedPropOwn γb0 DFrac.discard R ∗ R) from rfl]
      iframe Hph
      isplitl [Hout]
      · iexact Hout
      ipureintro; exact Hst0.2
    | fired γb0 =>
      iunfold kdPhaseInv at Hph
      icases Hph with ⟨Hph, HR, %HSM⟩
      iexists none
      isplitl [Hrun]
      · iunfold kdRunKeep; iexact Hrun
      isplitr
      · ipureintro; rfl
      isplitr
      · ipureintro; exact HSM
      isplitr
      · iunfold kdPendIn; iempintro
      iintro -
      iexists KdPhase.fired γb0
      rw [show pbTarget S none = S from rfl]
      simp only [kdPhaseInv]
      iframe Hph
      isplitl [HR]
      · iexact HR
      ipureintro; exact HSM
  icases Hpz with ⟨%pb, Hkeep, %HpbQ, %HSM', Hpend, Hpost⟩
  try wp_auto
  wp_apply wp_encode st ip M $$ [$Hpkg $Himg $Himage] as %sl ⟨Hsl, -, Himage⟩
  ihave %Hsll := ownSlice_len $$ Hsl
  have Hdl : (encStor M).length < 2 ^ 63 := by obtain ⟨h1, -⟩ := Hsll; rw [h1]; word
  wp_apply wp_bytes_to_string sl (encStor M) (DFrac.own 1) $$ [$Hsl] as -
  try wp_auto
  rw [← Hdf.2]
  wp_apply (wp_Write ph.fl.γd ph.fl.df ph.fl.fR qc (encStor M) Hdf.1 Hdl) $$ Hdur Hos HosS Hdi Hdh Hcpm
    [r Hwr Hlc1 Hlc2 Hkeep Hpend Hpost Hlocked Himage Hmeta Hic His Hcm HΦ]
  iapply kd_writeAU γ id n ph q S o M pb _ HMok HSM' $$ HfInv Harm Hwr Hlc1 Hlc2 Hkeep Hcert Hpend
  iintro Hwr Hrun Hout Hdh Hcpm
  rw [HpbQ]
  ihave ⟨%pz', Hph⟩ := Hpost $$ Hout
  try wp_auto
  wp_apply wp_add sts _ (by decide) (by decide) $$ [$Hpkg $Hstats]
  try wp_auto
  wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hdmu $Hlocked Himage Hmeta Hic His Hcm Hdh Hcpm Hwr Hph]
  · inext
    iunfold kdDmuInv
    iexists ip, M, fz
    iframe Himg Himage Hmeta Hic Hfz His Hcm Hdh
    isplitr
    · ipureintro; exact Hfzc
    isplitl [Hcpm]
    · iexists qc; iexact Hcpm
    iexists pbTarget S pb, some M, pz'
    iframe Hwr Hcert Hph
    ipureintro; exact ⟨HMok, fun f hf => by cases hf; exact Nat.le_refl _⟩
  try wp_auto
  iapply HΦ
  iframe Hrun

/-- `persist.specRun`: `run`'s write of its pending batch (see the spec's header). The phase is `run`'s
batch, waiting (entered by this write) or already fired (by the snapshotter's); either way `run` takes
its results back (the saved proposition's agreement, with a later credit) and the phase is `idle`. -/
theorem Replica.persist.wp_proofRun
    (wp_encode : Storage.encode.spec (GF := GF) (hG := hG))
    (wp_Write : github_com.mit_pdos.etcd_grove.examples.lib.durable.Write.spec (GF := GF) (hG := hG))
    (wp_add : Stats.add.spec (GF := GF) (hG := hG)) :
    Replica.persist.specRun (GF := GF) (hG := hG) := by
  intro γ vs dir id r n st sts sq ms γs ph q st' qs γb
  wp_start as ⟨#Hrep, Hrun, Hclaim, #HsvC⟩
  ihave #Hrep' := Hrep
  iunfold isReplica at Hrep'
  iNamed Hrep'
  ihave #Hdur : isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.durable
    $$ []
  · iPkgInit
  try wp_auto
  wp_apply (lc := 3) sync.Mutex.wp_Lock _ _ $$ [$Hdmu] as ⟨Hlocked, HR⟩
  iunfold kdDmuInv at HR
  iNamed HR
  icases Hlive with ⟨%S, %o, %pz, Hwr, %HMok, #Hcert, %Hfb, Hph⟩
  icases Hcpm with ⟨%qc, Hcpm⟩
  -- `run`'s batch: what the write takes, and how `run` gets its results back after it
  ihave Hpz : iprop(∃ pb : Option (GName × RaftState × Qp), kdRunKeep γ n q pb ∗ ⌜pbQ q pb = q⌝ ∗
      ⌜StorageHolds (pbTarget S pb) (kdContents (some M)) ∧ pbTarget S pb = st'.durable⌝ ∗
      kdPendIn γ id n S pb ∗ ghostVar ph.ph (1 : Qp).half (some γb, st'.durable) ∗
      ghostVar ph.ph (1 : Qp).half (some γb, st'.durable) ∗
      (kdPendOut pb -∗ £ 1 ={⊤}=∗ kdBatchRes γ id n st' qs)) $$ [Hph Hclaim Hrun]
  · cases pz with
    | idle =>
      iunfold kdPhaseInv at Hph
      icases Hph with ⟨Hph, -⟩
      ihave %Hag := ghostVar_agree ph.ph _ _ _ _ $$ Hph Hclaim
      obtain ⟨h, -⟩ := Prod.mk.inj Hag
      cases h
    | waiting st0 st0' ms0 γb0 =>
      iunfold kdPhaseInv at Hph
      icases Hph with ⟨Hph, #Hsv0, Henter, %Hst0⟩
      ihave %Hag := ghostVar_agree ph.ph _ _ _ _ $$ Hph Hclaim
      obtain ⟨h1, h2⟩ := Prod.mk.inj Hag
      obtain rfl := Option.some.inj h1
      iexists some (γb0, st0'.durable, q)
      isplitr
      · iunfold kdRunKeep; iempintro
      isplitr
      · ipureintro; rfl
      isplitr
      · ipureintro; exact ⟨Hst0.2, h2⟩
      isplitl [Henter Hrun]
      · iunfold kdPendIn
        iexists st0, st0', ms0
        iframe Henter Hrun Hsv0
        ipureintro; exact ⟨Hst0.1, rfl⟩
      ihave Hph : ghostVar ph.ph (1 : Qp).half (some γb0, st'.durable) $$ [Hph]
      · rw [← h2]; iexact Hph
      iframe Hph Hclaim
      iintro Hout Hlc
      rw [show kdPendOut (GF := GF) (some (γb0, st0'.durable, q)) =
        iprop(∃ R : IProp GF, savedPropOwn γb0 DFrac.discard R ∗ R) from rfl]
      icases Hout with ⟨%R, #HsvR, HRR⟩
      ihave #Heq := saved_prop_agree γb0 DFrac.discard DFrac.discard _ _ $$ HsvR HsvC
      ihave HA : ▷ kdBatchRes γ id n st' qs $$ [HRR]
      · inext
        ihave Hiff := internalEq_iff _ _ $$ Heq
        icases Hiff with ⟨Hiff, -⟩
        iapply Hiff $$ HRR
      imod lc_fupd_elim_later $$ Hlc HA with HA
      imodintro
      iexact HA
    | fired γb0 =>
      iunfold kdPhaseInv at Hph
      icases Hph with ⟨Hph, ⟨%R, #HsvR, HRR⟩, %HSM⟩
      ihave %Hag := ghostVar_agree ph.ph _ _ _ _ $$ Hph Hclaim
      obtain ⟨h1, h2⟩ := Prod.mk.inj Hag
      obtain rfl := Option.some.inj h1
      iexists none
      isplitl [Hrun]
      · iunfold kdRunKeep; iexact Hrun
      isplitr
      · ipureintro; rfl
      isplitr
      · ipureintro; exact ⟨HSM, h2⟩
      isplitr
      · iunfold kdPendIn; iempintro
      ihave Hph : ghostVar ph.ph (1 : Qp).half (some γb0, st'.durable) $$ [Hph]
      · rw [← h2]; iexact Hph
      iframe Hph Hclaim
      iintro - Hlc
      ihave #Heq := saved_prop_agree γb0 DFrac.discard DFrac.discard _ _ $$ HsvR HsvC
      ihave HA : ▷ kdBatchRes γ id n st' qs $$ [HRR]
      · inext
        ihave Hiff := internalEq_iff _ _ $$ Heq
        icases Hiff with ⟨Hiff, -⟩
        iapply Hiff $$ HRR
      imod lc_fupd_elim_later $$ Hlc HA with HA
      imodintro
      iexact HA
  icases Hpz with ⟨%pb, Hkeep, %HpbQ, ⟨%HSM', %HS'⟩, Hpend, Hph, Hclaim, Hpost⟩
  try wp_auto
  wp_apply wp_encode st ip M $$ [$Hpkg $Himg $Himage] as %sl ⟨Hsl, -, Himage⟩
  ihave %Hsll := ownSlice_len $$ Hsl
  have Hdl : (encStor M).length < 2 ^ 63 := by obtain ⟨h1, -⟩ := Hsll; rw [h1]; word
  wp_apply wp_bytes_to_string sl (encStor M) (DFrac.own 1) $$ [$Hsl] as -
  try wp_auto
  rw [← Hdf.2]
  wp_apply (wp_Write ph.fl.γd ph.fl.df ph.fl.fR qc (encStor M) Hdf.1 Hdl) $$ Hdur Hos HosS Hdi Hdh Hcpm
    [r Hwr Hlc1 Hlc2 Hlc3 Hkeep Hpend Hpost Hph Hclaim Hlocked Himage Hmeta Hic His Hcm HΦ]
  iapply kd_writeAU γ id n ph q S o M pb _ HMok HSM' $$ HfInv Harm Hwr Hlc1 Hlc3 Hkeep Hcert Hpend
  iintro Hwr Hrun Hout Hdh Hcpm
  rw [HpbQ]
  imod Hpost $$ Hout Hlc2 with HA
  imod ghostVar_update_halves ((none : Option GName), st'.durable) ph.ph _ _ $$ Hph Hclaim
    with ⟨Hph, Hclaim⟩
  try wp_auto
  wp_apply wp_add sts _ (by decide) (by decide) $$ [$Hpkg $Hstats]
  try wp_auto
  rw [HS'] at HSM'
  rw [HS']
  wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hdmu $Hlocked Himage Hmeta Hic His Hcm Hdh Hcpm Hwr Hph]
  · inext
    iunfold kdDmuInv
    iexists ip, M, fz
    iframe Himg Himage Hmeta Hic Hfz His Hcm Hdh
    isplitr
    · ipureintro; exact Hfzc
    isplitl [Hcpm]
    · iexists qc; iexact Hcpm
    iexists st'.durable, some M, KdPhase.idle
    iframe Hwr Hcert
    isplitr
    · ipureintro; exact HMok
    isplitr
    · ipureintro; intro f hf; cases hf; exact Nat.le_refl _
    simp only [kdPhaseInv]
    iframe Hph
    ipureintro; exact HSM'
  try wp_auto
  iapply HΦ
  iframe Hrun Hclaim HA

end proof

end kvraft
end EtcdGrove
end Perennial
