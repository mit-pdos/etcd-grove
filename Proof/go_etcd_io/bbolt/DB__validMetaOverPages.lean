/-
The proof of `Spec/go_etcd_io/bbolt/DB__validMetaOverPages.lean` (W6; the fork's 2c660ee): the meta
of page `i` read in place (`pageInBuffer`, `Page.Meta`), validated, its freelist page's and root
page's headers read in place; every `false` exit refutes one conjunct of `metaOverPages`.
-/
module

public import Spec.go_etcd_io.bbolt.DB__validMetaOverPages
public import Spec.go_etcd_io.bbolt.DB__pageInBuffer
public import Spec.go_etcd_io.bbolt.internal.common.Page__Meta
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Validate
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Freelist
public import Spec.go_etcd_io.bbolt.internal.common.Meta__RootBucket
public import Spec.go_etcd_io.bbolt.internal.common.InBucket__RootPage
public import Spec.go_etcd_io.bbolt.internal.common.Page__IsFreelistPage
public import Spec.go_etcd_io.bbolt.internal.common.Page__Id
public import Spec.go_etcd_io.bbolt.internal.common.Page__IsLeafPage
public import Spec.go_etcd_io.bbolt.internal.common.Page__IsBranchPage
public import Proof.go_etcd_io.bbolt.internal.common.Lemmas.Layout

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem DB.validMetaOverPages.wp_proof
    (hPIB : DB.pageInBuffer.spec_own (GF := GF) (hG := hG))
    (hMeta : internal.common.Page.Meta.spec (GF := GF) (hG := hG))
    (hValidate : internal.common.Meta.Validate.spec (GF := GF) (hG := hG))
    (hFreelist : internal.common.Meta.Freelist.spec (GF := GF) (hG := hG))
    (hRootBucket : internal.common.Meta.RootBucket.spec (GF := GF) (hG := hG))
    (hRootPage : internal.common.InBucket.RootPage.spec (GF := GF) (hG := hG))
    (hIsFl : internal.common.Page.IsFreelistPage.spec (GF := GF) (hG := hG))
    (hId : internal.common.Page.Id.spec (GF := GF) (hG := hG))
    (hIsLeaf : internal.common.Page.IsLeafPage.spec (GF := GF) (hG := hG))
    (hIsBranch : internal.common.Page.IsBranchPage.spec (GF := GF) (hG := hG)) :
    DB.validMetaOverPages.spec (GF := GF) (hG := hG) := by
  intro db sl B dqp i hi hBl
  wp_start as ⟨#Hpkg, Hps, #Hsl⟩
  ihave #Hcom : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
  wp_auto
  done

end proof

end bbolt
end EtcdGrove
end Perennial
