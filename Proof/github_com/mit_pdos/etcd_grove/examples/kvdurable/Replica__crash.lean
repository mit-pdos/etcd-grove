/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvdurable/Replica__crash.lean`.
Lean-first (no Rocq counterpart).

Under `dmu`, the crasher's token (`repStop`'s half of `crashed` at `false`) agrees with `dmu`'s half:
the incarnation has not crashed. The two halves make `crashed` whole; it is set, and `dmu` keeps half
of it (at `true`, so nothing writes the file any more), the writer's half staying. Then `stop`, on the
stopper's share, which gives back `run`'s claim; then under `dmu` again the writer's half comes out,
the claim left in its place (had it been taken already, the claim would be a third half of `ph.ph`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Replica__crash
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Replica__stop
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
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KdStor GF]

attribute [local instance] kdStorageModel

/-- Three halves of a ghost variable are refuted. -/
theorem ghostVar_three_halves {A : Type} [Pos.Countable A] (γv : GName) (a b c : A) :
    ghostVar (GF := GF) γv (1 : Qp).half a ∗ ghostVar γv (1 : Qp).half b ∗
      ghostVar γv (1 : Qp).half c ⊢ False := by
  iintro ⟨H1, H2, H3⟩
  ihave %Hab := ghostVar_agree γv _ _ _ _ $$ H1 H2
  subst Hab
  ihave H12 : ghostVar γv ((1 : Qp).half + (1 : Qp).half) a $$ [H1 H2]
  · iapply (ghostVar_fractional (GF := GF) γv a).fractional _ _ |>.2
    iframe H1 H2
  rw [Qp.half_add_half] at *
  ihave %Hv := ghostVar_valid_2 γv _ _ _ _ $$ H12 H3
  exfalso
  have h1 : (1 : Rat) + ((1 : Qp).half).val ≤ 1 := Hv.1
  have := ((1 : Qp).half).2
  grind

/-- The phase's half of the claim. -/
theorem kdPhaseInv_claim (γ : KdNames) (id : w64) (n : Loc) (g : GName) (S : RaftState)
    (M : StorFile) (pz : KdPhase) :
    kdPhaseInv γ id n g S M pz ⊢
      ∃ v : Option GName × RaftState, ghostVar g (1 : Qp).half v ∗
        (ghostVar g (1 : Qp).half v -∗ kdPhaseInv γ id n g S M pz) := by
  cases pz with
  | idle =>
    simp only [kdPhaseInv]
    iintro ⟨H, Hr⟩
    iexists _
    iframe H
    iintro H
    isplitl [H]
    · iexact H
    iexact Hr
  | waiting st st' ms γb =>
    simp only [kdPhaseInv]
    iintro ⟨H, Hr⟩
    iexists _
    iframe H
    iintro H
    isplitl [H]
    · iexact H
    iexact Hr
  | fired γb =>
    simp only [kdPhaseInv]
    iintro ⟨H, Hr⟩
    iexists _
    iframe H
    iintro H
    isplitl [H]
    · iexact H
    iexact Hr

theorem Replica.crash.wp_proof (wp_stop : Replica.stop.spec (GF := GF) (hG := hG)) :
    Replica.crash.spec (GF := GF) (hG := hG) := by
  intro γ vs dir id r
  wp_start as Hs
  iunfold repStop at Hs
  icases Hs with ⟨Hstopper, Htok⟩
  iunfold repStopper at Hstopper
  icases Hstopper with ⟨%n, %st, %sts, %sq, %ρ, #HR, Hpend, Hrd, Htd, Hsd⟩
  ihave #HR' := HR
  iunfold isReplicaR at HR'
  iNamed HR'
  ihave #Hrep' := Hrep
  iunfold isReplica at Hrep'
  iNamed Hrep'
  try wp_auto
  wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hdmu] as ⟨Hlocked, HI⟩
  iunfold kdDmuInv at HI
  iNamed HI
  ihave ⟨%Hc, Hcr⟩ := typedPointsto_half_combine _ _ _ (1 : Qp) $$ [$Hcr $Htok]
  subst Hc
  simp only [Bool.false_eq_true, ↓reduceIte]
  icases Hlive with ⟨%S, %o, %pz, Hwr, %HMok, #Hcert, Hph⟩
  try wp_auto
  ihave ⟨Hcr, Hcr2⟩ := (typedPointsto_half_split _ true (1 : Qp)).1 $$ Hcr
  wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hdmu $Hlocked Hcr Himage Hmeta Hic His Hph Hwr]
  · inext
    iunfold kdDmuInv
    iexists true, ip, M, fz
    iframe Hcr Himg Himage Hmeta Hic Hfz His
    isplitr
    · ipureintro; exact Hfzc
    iexists S, o, pz
    simp only [↓reduceIte]
    iframe Hcert Hph
    isplitl [Hwr]
    · ileft; iexact Hwr
    ipureintro; exact HMok
  try wp_auto
  wp_apply wp_stop γ vs dir id r $$ [Hpend Hrd Htd Hsd] as ⟨Hvac, %n2, %st2, %sts2, %sq2, %ρ2, #HR2, %v, Hclaim⟩
  · iunfold repStopper
    iexists n, st, sts, sq, ρ
    iframe HR Hpend Hrd Htd Hsd
  -- `dmu` once more (`run` and the snapshotter have returned): the writer out, `run`'s claim in
  iclear Hdmu Hrep HR Hfile Hid Hnode Hst Hsts Hsq Hstats Hseqs HisNode Hcl HfInv Hrec Hmu
  ihave #HR2' := HR2
  iunfold isReplicaR at HR2'
  iNamed HR2'
  ihave #Hrep2' := Hrep
  iunfold isReplica at Hrep2'
  iNamed Hrep2'
  try wp_auto
  wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hdmu] as ⟨Hlocked, HI⟩
  iunfold kdDmuInv at HI
  iNamed HI
  ihave ⟨%Hc, Hcr⟩ := typedPointsto_half_combine _ _ _ (1 : Qp) $$ [$Hcr $Hcr2]
  subst Hc
  ihave ⟨Hcr, -⟩ := (typedPointsto_half_split _ true (1 : Qp)).1 $$ Hcr
  simp only [↓reduceIte]
  icases Hlive with ⟨%S, %o, %pz, Hwr, %HMok, #Hcert, Hph⟩
  icases Hwr with (Hwr | ⟨%v', Hc'⟩)
  · try wp_auto
    wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hdmu $Hlocked Hcr Himage Hmeta Hic His Hph Hclaim]
    · inext
      iunfold kdDmuInv
      iexists true, ip, M, fz
      iframe Hcr Himg Himage Hmeta Hic Hfz His
      isplitr
      · ipureintro; exact Hfzc
      iexists S, o, pz
      simp only [↓reduceIte]
      iframe Hcert Hph
      isplitl [Hclaim]
      · iright; iexists v; iexact Hclaim
      ipureintro; exact HMok
    try wp_auto
    iapply HΦ
    iframe Hvac
    iexists S, o
    iexact Hwr
  · icases kdPhaseInv_claim _ _ _ _ _ _ _ $$ Hph with ⟨%v'', Hc'', -⟩
    iexfalso
    iapply ghostVar_three_halves ρ2.ph.ph v v' v''
    iframe Hclaim Hc' Hc''

end proof

end kvdurable
end EtcdGrove
end Perennial
