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

end proof

end kvdurable
end EtcdGrove
end Perennial
