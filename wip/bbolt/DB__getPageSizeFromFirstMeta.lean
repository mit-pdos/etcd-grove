module
public import Spec.go_etcd_io.bbolt.DB__getPageSizeFromFirstMeta
public import Spec.go_etcd_io.bbolt.DB__pageInBuffer
public import Spec.go_etcd_io.bbolt.internal.common.Page__Meta
public import Spec.go_etcd_io.bbolt.internal.common.Meta__PageSize
public import Spec.os.File__ReadAt

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]

theorem DB.getPageSizeFromFirstMeta.wp_proof (hReadAt : os.File.ReadAt.spec (GF := GF) (hG := hG))
    (hpib : DB.pageInBuffer.spec (GF := GF) (hG := hG))
    (hMeta : Page.Meta.spec (GF := GF) (hG := hG))
    (hValidate : Meta.Validate.spec (GF := GF) (hG := hG))
    (hPageSize : Meta.PageSize.spec (GF := GF) (hG := hG)) :
    DB.getPageSizeFromFirstMeta.spec (GF := GF) (hG := hG) := by
  intro dbl f fd bs ps dq
  wp_start as ⟨Hf, Hps, #Hof, Hfb⟩
  ihave #Hei : (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.errors) $$ []
  · iPkgInit
  icases bboltError_access errors.ErrInvalid (by simp [bboltErrorNames]) $$ Hei
    with ⟨%e, #He, %Hne⟩
  wp_auto
  done

end proof

end bbolt
end EtcdGrove
end Perennial
