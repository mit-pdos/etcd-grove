/-
Lean-first (no Rocq counterpart).

The proof of `New`: the server's condition variable is made over its `RWMutex` (and its field is
then fixed: persistent); the lock guards `rdR` (the state `""` and half of a fresh ghost
variable at `""`, with `γb`'s half at `false`), with its reader tokens in a thread pool, and the
writer's part (`wrR`: an empty log, nothing applied, a fresh request list) goes to `wInv` with
`γb`'s other half; the other half of the ghost variable is the register's state returned. The apply
goroutine needs only the server (`applyLoop.spec`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lintest.logkvrw.New
public import Spec.github_com.mit_pdos.etcd_grove.examples.lintest.logkvrw.Server__applyLoop
public import Perennial.Spec.sync.NewCond
public import Perennial.Proof.sync.Link
public import Perennial.Proof.sync.RWMutexThreads

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lintest
namespace logkvrw

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lintest.logkvrw.Assumptions]

theorem New.wp_proof (wp_applyLoop : Server.applyLoop.spec (GF := GF) (hG := hG)) :
    New.spec (GF := GF) (hG := hG) := by
  intro Htb
  wp_start
  wp_alloc s as Hs
  iStructNamed Hs
  wp_auto
  wp_apply sync.wp_NewCond (muLocker s) as %c #Hcond
  ipersist cond
  imod ghostVar_alloc (GF := GF) (go!"" : GoString) with ⟨%γst, Hv⟩
  icases ghostVar_split γst (go!"" : GoString) (1 : Qp).half (1 : Qp).half $$ [Hv] with ⟨Hv1, Hv2⟩
  · rw [Qp.half_add_half]; iexact Hv
  imod mono_list_own_alloc (GF := GF) ([] : List Req) with ⟨%γreq, Hrs, -⟩
  imod ghostVar_alloc (GF := GF) false with ⟨%γb, Hb⟩
  icases ghostVar_split γb false (1 : Qp).half (1 : Qp).half $$ [Hb] with ⟨Hb1, Hb2⟩
  · rw [Qp.half_add_half]; iexact Hb
  imod inv_alloc wN ⊤ (wInv γst γreq γb s) $$ [log applied Hrs Hb2] with #Hinv
  · inext
    iunfold wInv
    iright
    iframe
    iunfold wrR
    iexists slice.nil, [], W64 0
    simp only [List.map_nil, List.take_nil, List.drop_nil]
    iframe
    isplitl []
    · iapply ownSlice_nil
    isplitl []
    · iapply ownSliceCap_nil
    isplitl []
    · ipureintro; simp
    isplitl []
    · iapply BigSepL.bigSepL_nil.2; itrivial
    iapply BigSepL.bigSepL_nil.2; itrivial
  imod sync.init_RWMutex_threadPool (rdR γst γb s) poolN (muAddr s) Htb $$ [state Hv1 Hb1] mu
    with ⟨%γp, #Hg, #Hpool⟩
  · inext
    iunfold rdR
    iexists go!""
    iframe
  ihave #Hsrv : isServer γst s $$ []
  · iunfold isServer
    iexists γreq, γb, γp, c
    iframe #
    iunfold wLock
    iframe #
  wp_apply wp_fork $$ []
  · wp_apply wp_applyLoop γst s $$ [$Hsrv] as Hf
    iexfalso; iexact Hf
  iapply HΦ
  iexists γst
  iframe Hsrv
  iunfold regState
  iexact Hv2

end proof

end logkvrw
end lintest
end EtcdGrove
end Perennial
