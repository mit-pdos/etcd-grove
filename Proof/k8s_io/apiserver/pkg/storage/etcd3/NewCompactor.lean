/-
Lean-first (no Rocq counterpart).

The proof of `NewCompactor`: the compactor's struct, its `stop` channel (a broadcast channel), its
lock invariant (revision `0`, its counter at `0`), its wait group (`sync.join`'s, one `Add`) and
`stopOnce` (holding the channel's closing right and the wait group's adder); then, at the nonzero
interval, the loop goroutine (`runCompactLoop.spec`, given the client's resources and `casOk`),
and the feature gate's answer `false` (`gateOff`): no watch loop.
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.NewCompactor
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.compactor__runCompactLoop
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
variable [sync_sem : sync.Assumptions]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

/-- `NewCompactor`'s proof, given that the constant `features.ListFromCacheSnapshot` (axiomatized:
`features` is translated names-only) is a value, not a panic, as `store.Delete`'s proof is given
`AllowUnsafeMalformedObjectDeletion`'s (`Proof/k8s_io/apiserver/pkg/features/Values.lean`): the
`if` binds it before calling `Enabled`. -/
theorem NewCompactor.wp_proof
    (hlfcs : k8s_io.apiserver.pkg.features.ListFromCacheSnapshot.isPanic = false)
    (wp_runCompactLoop : compactor.runCompactLoop.spec (GF := GF) (hG := hG)) :
    NewCompactor.spec (GF := GF) (hG := hG) := by
  intro _ _ cl ms V γk Seen recorded _ _ iv ck hsame hcmp hcret hiv
  wp_start as ⟨Htok, #Hgate, #Hcl, Hone, Hregs, #Hcas⟩
  ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
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
  imod sync.init_Once (structFieldRef k8s_io.apiserver.pkg.storage.etcd3.compactor go!"stopOnce" c)
    (iprop(ownBroadcastChan sc γs iprop(True) .Pending ∗
      sync.join.ownAdder (structFieldRef k8s_io.apiserver.pkg.storage.etcd3.compactor go!"wg" c)
        (W32 1) iprop(True))) iprop(True) ⊤
    $$ [stopOnce Hpend Hadd] with #Honce
  · iframe
  ihave #Hstop : compactorStopOk c sc γs $$ []
  · unfold compactorStopOk
    iframe #
  ihave #Hc : isCompactor c cl γk recorded γc $$ []
  · unfold isCompactor
    isplitr
    · ipureintro; intro r; infer_instance
    iframe #
    isplitr
    · ipureintro; exact hiv
    iexists ck
    itrivial
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
  iunfold gateOff at Hgate
  icases Hgate with ⟨%g, #Hg, #Hen⟩
  have hnp := hlfcs
  (try wp_auto)
  wp_apply Hen
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
