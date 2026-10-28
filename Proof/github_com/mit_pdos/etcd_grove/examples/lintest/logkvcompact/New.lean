/-
Lean-first (no Rocq counterpart).

The proof of `New`: the server's condition variable is made over its mutex (and its field is
then fixed: persistent); the mutex gets its lock invariant (`logkvcompactR`), with an empty log,
nothing applied, the state `""`, half of a fresh ghost variable at `""` and a fresh request
list (and no time receipt: no write yet), `start` at 0; the other half of the ghost variable is the register's state returned. The apply
goroutine needs only the server (`applyLoop.spec`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lintest.logkvcompact.New
public import Spec.github_com.mit_pdos.etcd_grove.examples.lintest.logkvcompact.Server__applyLoop
public import Perennial.Spec.sync.NewCond
public import Perennial.Proof.sync.Link

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lintest
namespace logkvcompact

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lintest.logkvcompact.Assumptions]

theorem New.wp_proof (wp_applyLoop : Server.applyLoop.spec (GF := GF) (hG := hG)) :
    New.spec (GF := GF) (hG := hG) := by
  intro Hbound
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
  imod receipt_zero (GF := GF) with H0
  imod sync.init_Mutex (logkvcompactR γst γreq s) ⊤ (muAddr s) $$ mu [log start applied state Hv1 Hrs H0] with #Hmu
  · inext
    iunfold logkvcompactR
    iexists slice.nil, [], W64 0, W64 0, go!""
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
  ihave #Hsrv : isServer γst s $$ []
  · iunfold isServer
    iexists γreq, c
    iframe #
    ipureintro; exact Hbound
  wp_apply wp_fork $$ []
  · wp_apply wp_applyLoop γst s $$ [$Hsrv] as Hf
    iexfalso; iexact Hf
  iapply HΦ
  iexists γst
  iframe Hsrv
  iunfold regState
  iexact Hv2

end proof

end logkvcompact
end lintest
end EtcdGrove
end Perennial
