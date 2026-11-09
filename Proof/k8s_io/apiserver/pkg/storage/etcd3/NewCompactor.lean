/-
Lean-first (no Rocq counterpart).

The proof of `NewCompactor`: the compactor's struct, its `stop` channel (a broadcast channel), its
lock invariant (revision `0`, its counter at `0`), its wait group (`sync.join`'s, one `Add`) and
`stopOnce` (holding the channel's closing right and the wait group's adder); then, at the nonzero
interval, the loop goroutine (`runCompactLoop.spec`, given the client's resources and `casOk`),
and the feature gate's answer either way (`featureInit`): on, the watch loop in a second goroutine,
its `Add(1)` before `stopOnce` is set up with the adder.
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.NewCompactor
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.compactor__runCompactLoop
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.compactor__runWatchLoop
public import Perennial.Proof.sync.Results
public import Perennial.Proof.sync.Link
import all Proof.k8s_io.apiserver.pkg.storage.etcd3.CompactorDefs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [sync_sem : sync.Assumptions]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

/-- `NewCompactor`'s proof. The `if` binds the constant `features.ListFromCacheSnapshot` before
calling `Enabled`: translated (`features.toml`), a value, not a panic. -/
theorem NewCompactor.wp_proof
    (wp_runCompactLoop : compactor.runCompactLoop.spec (GF := GF) (hG := hG))
    (wp_runWatchLoop : compactor.runWatchLoop.spec (GF := GF) (hG := hG)) :
    NewCompactor.spec (GF := GF) (hG := hG) := by
  intro _ _ cl ms V γk Seen recorded _ _ iv ck f hsame hcmp hcret hiv
  wp_start as ⟨#Hcl, Hone, Hregs, #Hko, #Hwo, #Hcas, #Hkr, #Hclose⟩
  ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Pft : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.features $$ []
  · iPkgInit
  -- (sweep repairs 1, B5) the default gate's specs, `features`' fact
  ihave #Hft : (k8s_io.apiserver.pkg.storage.etcd3.featuresInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Pft
  icases Hft with ⟨%g, #Hg, #Hgate⟩
  iunfold EtcdGrove.k8sfeature.featureGateOk at Hgate
  icases Hgate with ⟨#Hen, -⟩
  wp_auto
  wp_apply chan.wp_make1 (V := Unit) as %sc %γs ⟨#Hsch, %_, Hsoc⟩
  (try wp_auto)
  generalize «$r0_ptr» = c
  iStructNamed «$r0»
  ipersist client
  ipersist interval
  ipersist «clock»
  ipersist onClose
  ipersist stop
  ipersist «c»
  -- the stop channel
  imod alloc_broadcast_chan (E := ⊤) (iprop(True) : IProp GF) γs sc $$ Hsch Hsoc with Hpend
  ihave #Hunk := ownBroadcastChan_Unknown _ _ _ _ $$ Hpend
  -- the lock invariant
  imod mono_nat_own_alloc (GF := GF) 0 with ⟨%γlb, Hauth, #Hlb0⟩
  let γc : CompactorNames := ⟨γlb⟩
  imod sync.init_Mutex (compactorLockInv c γk recorded γc) ⊤
    (structFieldRef k8s_io.apiserver.pkg.storage.etcd3.compactor go!"mux" c)
    $$ mux [compactRevision Hauth] with #Hmux
  · inext
    iunfold compactorLockInv
    iexists W64 0
    simp only [γc]
    iframe
    unfold recRevOk
    ileft; ipureintro; rfl
  ihave #Hch : compactorChanOk c sc γs $$ []
  · unfold compactorChanOk
    iframe #
  ihave #Hcore : compactorCore c cl γk recorded γc $$ []
  · unfold compactorCore
    isplitr
    · ipureintro; intro r; infer_instance
    iframe #
    isplitr
    · ipureintro; exact hiv
    iexists ck
    itrivial
  -- the wait group
  imod sync.init_WaitGroup (sync.join.wgjN.@"wg")
    (structFieldRef k8s_io.apiserver.pkg.storage.etcd3.compactor go!"wg" c) $$ wg
    with ⟨%γwg, #Hwg, Hctr, Hwaiters⟩
  imod sync.join.init _ γwg $$ [Hctr Hwaiters] with Hadd
  · iframe #; iframe
  wp_if_destruct
  · exact absurd rfl hiv
  (try wp_auto)
  wp_apply sync.join.WaitGroup.wp_Add iprop(True) _ iprop(True) (W32 0) $$ [Hadd] as ⟨Hadd, Hdone⟩
  · iframe #; iframe
    ipureintro; decide
  ihave Hadd := sync.join.ownAdder_wand iprop(True) _ _ _ $$ [] Hadd
  · iintro _; itrivial
  (try wp_auto)
  wp_apply wp_fork $$ [Hone Hregs Hdone]
  · (try wp_auto)
    wp_apply wp_with_defer as %defer defer
    (try wp_auto)
    wp_apply (wp_runCompactLoop c cl ms V γk Seen recorded γc sc γs hsame hcmp hcret)
      $$ [Hone Hregs]
    · iframe #
      iframe
    (try wp_auto)
    wp_apply sync.join.WaitGroup.wp_Done iprop(True) _ $$ [Hdone]
    · iframe #; iframe
    (try wp_auto)
    (try itrivial)
  (try wp_auto)
  have hnp : k8s_io.apiserver.pkg.features.ListFromCacheSnapshot.isPanic = false := by
    simp [k8s_io.apiserver.pkg.features.ListFromCacheSnapshot]
  (try wp_auto)
  wp_apply Hen as %b -
  · ipureintro; decide
  (try wp_auto)
  -- the stop machinery, once the wait group's last `Add` is done
  ihave Hfin : (∀ n : w32, sync.join.ownAdder
      (structFieldRef k8s_io.apiserver.pkg.storage.etcd3.compactor go!"wg" c) n iprop(True) -∗
      ownBroadcastChan sc γs iprop(True) .Pending -∗
      structFieldRef k8s_io.apiserver.pkg.storage.etcd3.compactor go!"stopOnce" c ↦ zero_val sync.Once -∗
      |={⊤}=> isCompactor c cl γk recorded γc) $$ []
  · iintro %n Hadd Hpend Honce
    imod sync.init_Once (structFieldRef k8s_io.apiserver.pkg.storage.etcd3.compactor go!"stopOnce" c)
      (iprop(ownBroadcastChan sc γs iprop(True) .Pending ∗
        ∃ n : w32, sync.join.ownAdder
          (structFieldRef k8s_io.apiserver.pkg.storage.etcd3.compactor go!"wg" c) n iprop(True)))
      iprop(True) ⊤
      $$ [Honce Hpend Hadd] with #Honce
    · iframe
    imodintro
    unfold isCompactor
    iframe Hcore
    iexists sc, γs
    unfold compactorStopOk
    iframe #
  cases b
  · imod Hfin $$ Hadd Hpend stopOnce with #Hc
    (try wp_auto)
    iapply HΦ
    iframe #
    unfold compactRevLb
    iExactEq Hlb0
    simp [γc]
  · (try wp_auto)
    wp_apply sync.join.WaitGroup.wp_Add iprop(True) _ iprop(True) (W32 1) $$ [Hadd]
      as ⟨Hadd, Hdone⟩
    · iframe #; iframe
      ipureintro; decide
    ihave Hadd := sync.join.ownAdder_wand iprop(True) _ _ _ $$ [] Hadd
    · iintro _; itrivial
    imod Hfin $$ Hadd Hpend stopOnce with #Hc
    (try wp_auto)
    wp_apply wp_fork $$ [Hdone]
    · (try wp_auto)
      wp_apply wp_with_defer as %defer defer
      (try wp_auto)
      wp_apply (wp_runWatchLoop c cl (ms.map client.SrvAt.addr) V γk recorded γc sc γs) $$ []
      · iframe #
      (try wp_auto)
      wp_apply sync.join.WaitGroup.wp_Done iprop(True) _ $$ [Hdone]
      · iframe #; iframe
      (try wp_auto)
      (try itrivial)
    (try wp_auto)
    iapply HΦ
    iframe #
    unfold compactRevLb
    iExactEq Hlb0
    simp [γc]

end proof

end k8s
end EtcdGrove
end Perennial
