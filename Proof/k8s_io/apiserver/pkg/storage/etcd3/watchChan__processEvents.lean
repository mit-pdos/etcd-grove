/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/etcd3/watchChan__processEvents.lean` (k8s 7f-5b): both
branches of the gate. Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.watchChan__processEvents
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.watchChan__concurrentProcessEvents
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.watchChan__serialProcessEvents
public import Perennial.Spec.sync.WaitGroup__Add
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

theorem watchChan.processEvents.wp_proof
    (wp_concurrent : watchChan.concurrentProcessEvents.spec (GF := GF) (hG := hG))
    (wp_serial : watchChan.serialProcessEvents.spec (GF := GF) (hG := hG))
    (wp_Add : sync.WaitGroup.Add.spec (GF := GF) (hG := hG)) :
    watchChan.processEvents.spec (GF := GF) (hG := hG) := by
  intro _ Obj _ _ wc sp c W γk γ cd sel emp inS m Q procd alive ctx kp recur q wg n P HQok Hhist hn
  wp_start as ⟨#Hcons, Hproc, Had⟩
  ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Pft : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.features $$ []
  · iPkgInit
  ihave #Hft : (k8s_io.apiserver.pkg.storage.etcd3.featuresInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Pft
  icases Hft with ⟨%g, #Hg, #Hgate⟩
  iunfold EtcdGrove.k8sfeature.featureGateOk at Hgate
  icases Hgate with ⟨#Hen, -⟩
  wp_auto
  wp_apply Hen as %b -
  · ipureintro; decide
  cases b
  · (try wp_auto)
    wp_apply (rwg.wp_Add_top wp_Add (kResAlive alive q) rwgN 3 wg n P (by omega)) $$ [$Had]
      as ⟨Had, Hdone⟩
    (try wp_auto)
    wp_apply wp_fork_tok
    iintro Htok
    isplitl [Hproc Hdone Htok]
    · wp_apply (wp_serial Obj wc sp c W γk γ cd sel emp inS m Q procd alive ctx kp recur q wg
        HQok Hhist) $$ [$Hproc $Hdone $Htok] as Htok
      · iframe #
      iframe Htok
      ipureintro; exact isPanic_intoVal ()
    (try wp_auto)
    iapply HΦ
    iexists n + 1
    iexact Had
  · (try wp_auto)
    wp_apply (wp_concurrent Obj wc sp c W γk γ cd sel emp inS m Q procd alive ctx kp recur q wg n P
      HQok Hhist hn) $$ [$Hproc $Had] as Had
    · iframe #
    (try wp_auto)
    iapply HΦ
    iexists n + 2
    iexact Had

end proof

end k8s
end EtcdGrove
end Perennial
