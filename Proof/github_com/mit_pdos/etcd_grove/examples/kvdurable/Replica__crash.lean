/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvdurable/Replica__crash.lean`.
Lean-first (no Rocq counterpart).

Under `dmu`, the crasher's token (`repStop`'s half of `crashed` at `false`) agrees with `dmu`'s half:
the incarnation has not crashed, so `dmu` holds the writer's half of the file's variable. The two
halves make `crashed` whole; it is set, and `dmu` keeps half of it (at `true`, so nothing writes the
file any more), the writer's half coming out. Then `stop`, on the stopper's share.
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
  ihave ⟨Hcr, -⟩ := (typedPointsto_half_split _ true (1 : Qp)).1 $$ Hcr
  wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hdmu $Hlocked Hcr Himage Hmeta Hph]
  · inext
    iunfold kdDmuInv
    iexists true, ip, M
    iframe Hcr Himg Himage Hmeta
    iexists S, o, pz
    simp only [↓reduceIte]
    iframe Hcert Hph
    ipureintro; exact HMok
  try wp_auto
  wp_apply wp_stop γ vs dir id r $$ [Hpend Hrd Htd Hsd] as Hvac
  · iunfold repStopper
    iexists n, st, sts, sq, ρ
    iframe HR Hpend Hrd Htd Hsd
  iapply HΦ
  iframe Hvac
  iexists S, o
  iexact Hwr

end proof

end kvdurable
end EtcdGrove
end Perennial
