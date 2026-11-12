module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.cache__put

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item mstore mcfg state)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem cache.put.wp_proof :
    cache.put.spec (GF := GF) (hG := hG) := by
  intro c tbl id o
  wp_start as ⟨#Hc, #Ho⟩
  ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold isCache at Hc
  (try wp_auto)
  wp_apply (sync.Mutex.wp_Lock _ (cacheInv c tbl)) $$ [] as ⟨Hlocked, HR⟩
  · iframe #
  iunfold cacheInv at HR
  icases HR with ⟨%mp, %m, Hobjs, Hm, #Hall⟩
  (try wp_auto)
  wp_apply wp_mapInsert $$ Hm as Hm
  (try wp_auto)
  wp_apply (sync.Mutex.wp_Unlock _ (cacheInv c tbl)) $$ [Hlocked Hobjs Hm]
  · iframe #
    iframe Hlocked
    inext
    iunfold cacheInv
    iexists mp, _
    iframe
    iapply (BigSepM.bigSepM_insert_elim (Φ := fun _ ob => cachedObjOk c ob)) $$ Ho Hall
  (try wp_auto)
  iapply HΦ
  itrivial

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
