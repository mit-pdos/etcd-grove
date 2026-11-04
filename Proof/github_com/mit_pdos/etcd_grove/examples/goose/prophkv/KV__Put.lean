/- Lean-first (no Rocq counterpart).

The proof of `KV.Put`: the caller's ghost step runs while the mutex is held, on the lock's half
of the abstract state.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.goose.prophkv.KV__Put

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace goose_prophkv

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.goose.prophkv

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.goose.prophkv.Assumptions]

theorem KV__Put.wp_proof : KV__Put.spec (GF := GF) := by
  intro kv γ k v R
  wp_start as ⟨#Hkv, Hstep⟩
  iunfold isKV at Hkv
  icases Hkv with ⟨%mu, %mref, #Hkvp, #Hmu⟩
  iStructNamed Hkvp
  wp_auto
  wp_apply github_com.goose_lang.primitive.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HR⟩
  iunfold kvLockInv at HR
  icases HR with ⟨%m, Hm, Hst⟩
  wp_apply wp_mapInsert $$ Hm as Hm
  imod Hstep $$ %m Hst with ⟨Hst, HR⟩
  wp_apply github_com.goose_lang.primitive.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hm Hst]
  · iunfold kvLockInv; iexists _; iframe
  iapply HΦ $$ HR

end proof

end goose_prophkv
end EtcdGrove
end Perennial
