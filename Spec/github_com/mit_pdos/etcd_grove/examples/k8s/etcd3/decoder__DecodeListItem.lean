/- Lean-first (no Rocq counterpart).

`decoder{}.DecodeListItem(ctx, data, rev, newItemFunc)` (k8setcd3.go): a fresh object from
`newItemFunc` (`newItemOk`), the data decoded into it at the resource version `rev` (`objAtD`, as
the store's list contract asks); else `errBadData`. Proved (stage 7e-2, `notes/k8s-7e-2-draft.md`
§6; the Draft's `decodeObjL`/`rvString` are `decodeObjD`/`rvStr`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ObjSpec
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.ListDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI k8s

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev decoder.DecodeListItem.spec : Prop :=
  ∀ (ctx : GoInterface) (dsl : GoSlice) (d : GoString) (rev : w64) (nf : GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗
      dsl ↦*□ d ∗ newItemOk (driverSpec (GF := GF)) nf }}
    (App (App (App (App (Val #(methods github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.decoder.ty
      go!"DecodeListItem" #(github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.decoder.mk)))
      (Val #ctx)) (Val #dsl)) (Val #rev)) (Val #nf))
  {{ (x err : GoInterface), RET (PairV #x #err);
      match decodeObjD d with
      | some o => ⌜err = GoInterface.nil⌝ ∗ objAtD x o (rvStr rev)
      | none => ⌜err ≠ GoInterface.nil⌝ ∗ go_etcd_io.etcd.cache.v3.errStrOk err }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
