/- Lean-first (no Rocq counterpart).

The proof of `KV.Get`: the caller's ghost step runs while the mutex is held, on the lock's half
of the abstract state, with the map's answer.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.prophkv.KV__Get

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace prophkv

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.prophkv

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.prophkv.Assumptions]

theorem KV__Get.wp_proof : KV__Get.spec (GF := GF) := by
  intro kv γ k R
  wp_start as ⟨#Hkv, Hstep⟩
  iunfold isKV at Hkv
  icases Hkv with ⟨%mu, %mref, #Hkvp, #Hmu⟩
  iStructNamed Hkvp
  wp_auto
  wp_apply github_com.goose_lang.primitive.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HR⟩
  iunfold kvLockInv at HR
  icases HR with ⟨%m, Hm, Hst⟩
  wp_apply wp_map_lookup1 $$ Hm as Hm
  imod Hstep $$ %m Hst with ⟨Hst, HR⟩
  wp_apply github_com.goose_lang.primitive.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hm Hst]
  · iunfold kvLockInv; iexists _; iframe
  iapply HΦ $$ HR

end proof

end prophkv
end EtcdGrove
end Perennial
