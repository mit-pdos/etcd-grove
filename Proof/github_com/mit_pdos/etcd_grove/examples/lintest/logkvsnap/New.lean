/-
Lean-first (no Rocq counterpart).

The proof of `New`: the server's condition variable is made over its mutex (and its field is
then fixed: persistent); the mutex gets its lock invariant (`logkvsnapR`), with an empty log,
the initial snapshot (`snapshot{}`, read-only: nothing applied, the state `""`), half of a fresh
ghost variable at `""` and a fresh request list; the other half of the ghost variable is the
register's state returned. The apply goroutine needs only the server (`applyLoop.spec`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lintest.logkvsnap.New
public import Spec.github_com.mit_pdos.etcd_grove.examples.lintest.logkvsnap.Server__applyLoop
public import Perennial.Spec.sync.NewCond
public import Perennial.Proof.sync.Link

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lintest
namespace logkvsnap

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lintest.logkvsnap.Assumptions]

theorem New.wp_proof (wp_applyLoop : Server.applyLoop.spec (GF := GF) (hG := hG)) :
    New.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_alloc sn as Hsn
  wp_pures
  wp_alloc s as Hs
  iStructNamed Hs
  wp_auto
  wp_apply sync.wp_NewCond (muLocker s) as %c #Hcond
  ipersist cond
  ipersist Hsn
  rw [show zero_val Snap = (⟨go!"", W64 0⟩ : Snap) from rfl] at *
  imod ghostVar_alloc (GF := GF) (go!"" : GoString) with ⟨%γst, Hv⟩
  icases ghostVar_split γst (go!"" : GoString) (1 : Qp).half (1 : Qp).half $$ [Hv] with ⟨Hv1, Hv2⟩
  · rw [Qp.half_add_half]; iexact Hv
  imod mono_list_own_alloc (GF := GF) ([] : List Req) with ⟨%γreq, Hrs, -⟩
  imod sync.init_Mutex (logkvsnapR γst γreq s) ⊤ (muAddr s) $$ mu [log snap Hv1 Hrs] with #Hmu
  · inext
    iunfold logkvsnapR
    iexists slice.nil, [], W64 0, go!"", sn
    simp only [List.map_nil, List.take_nil, List.drop_nil]
    iframe
    isplitl []
    · iapply ownSlice_nil
    isplitl []
    · iapply ownSliceCap_nil
    isplitl []
    · iexact Hsn
    isplitl []
    · ipureintro; simp
    isplitl []
    · iapply BigSepL.bigSepL_nil.2; itrivial
    iapply BigSepL.bigSepL_nil.2; itrivial
  ihave #Hsrv : isServer γst s $$ []
  · iunfold isServer
    iexists γreq, c
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

end logkvsnap
end lintest
end EtcdGrove
end Perennial
