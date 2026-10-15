/-
Lean-first (no Rocq counterpart).

The proof of `New`: the counter's mutex gets its lock invariant (`counterR`), with `c.n = 0`
and half of a fresh ghost variable at `0`; the other half is the abstract state returned.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lintest.counter.New

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lintest
namespace counter

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lintest.counter.Assumptions]

theorem New.wp_proof : New.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_alloc c as Hc
  iStructNamed Hc
  imod ghostVar_alloc (GF := GF) (W64 0) with ⟨%γ, Hv⟩
  icases ghostVar_split γ (W64 0) (1 : Qp).half (1 : Qp).half $$ [Hv] with ⟨Hv1, Hv2⟩
  · rw [Qp.half_add_half]; iexact Hv
  imod sync.init_Mutex (counterR γ c) ⊤ (muAddr c) $$ mu [n Hv1] with #Hmu
  · inext
    iexists W64 0
    iframe
  wp_auto
  iapply HΦ
  iexists γ
  iframe Hv2
  unfold isCounter
  iexact Hmu

end proof

end counter
end lintest
end EtcdGrove
end Perennial
