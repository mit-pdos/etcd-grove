module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.cache__get

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

theorem cache.get.wp_proof :
    cache.get.spec (GF := GF) (hG := hG) := by
  intro c tbl id
  wp_start as #Hc
  ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold isCache at Hc
  (try wp_auto)
  wp_apply (sync.Mutex.wp_Lock _ (cacheInv c tbl)) $$ [] as ⟨Hlocked, HR⟩
  · iframe #
  iunfold cacheInv at HR
  icases HR with ⟨%mp, %m, Hobjs, Hm, #Hall⟩
  (try wp_auto)
  wp_apply wp_map_lookup2 $$ Hm as Hm
  (try wp_auto)
  wp_apply (sync.Mutex.wp_Unlock _ (cacheInv c tbl)) $$ [Hlocked Hobjs Hm]
  · iframe #
    iframe Hlocked
    inext
    iunfold cacheInv
    iexists mp, m
    iframe
    iframe #
  (try wp_auto)
  iapply HΦ
  cases h : m !! id with
  | none =>
    simp only [Option.isSome_none, Bool.false_eq_true, decide_false, ↓reduceIte]
    itrivial
  | some ob =>
    simp only [Option.isSome_some, _root_.decide_true, ↓reduceIte, Option.getD_some]
    iapply (BigSepM.bigSepM_lookup (Φ := fun _ ob => cachedObjOk c ob) h) $$ Hall

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
