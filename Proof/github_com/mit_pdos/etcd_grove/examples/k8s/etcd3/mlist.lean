module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.mlist
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.parseRV
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.pastRead
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.histAt
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.predicate
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.storeKey
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.keyInScope
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.listOptions
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.encodeItems
public import Spec.k8s_io.apiserver.pkg.storage.SelectionPredicate__Matches
public import Spec.k8s_io.apiserver.pkg.storage.PrepareKey
public import Spec.k8s_io.apiserver.pkg.storage.PrepareContinueToken

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item mstore mcfg hnode state labelSel fieldSel)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem mlist.wp_proof
    (wp_parseRV : parseRV.spec (GF := GF) (hG := hG))
    (wp_pastRead : pastRead.spec (GF := GF) (hG := hG))
    (wp_histAt : histAt.spec (GF := GF) (hG := hG))
    (wp_predicate : predicate.spec (GF := GF) (hG := hG))
    (wp_storeKey : storeKey.spec (GF := GF) (hG := hG))
    (wp_keyInScope : keyInScope.spec (GF := GF) (hG := hG))
    (wp_listOptions : listOptions.spec (GF := GF) (hG := hG))
    (wp_encodeItems : encodeItems.spec (GF := GF) (hG := hG))
    (wp_Matches : storage.SelectionPredicate.Matches.spec (GF := GF) (hG := hG))
    (wp_PrepareKey : storage.PrepareKey.spec (GF := GF) (hG := hG))
    (wp_PrepareContinueToken : storage.PrepareContinueToken.spec (GF := GF) (hG := hG)) :
    mlist.spec (GF := GF) (hG := hG) := by
  intro x c g
  wp_start as ⟨#Hc, %Hb⟩
  wp_auto
  sorry

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
