/-
`(*exactReadCloser).Close()` (`pkg/ioutil/readcloser.go`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.ioutil.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.pkg.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `e.Close()`, `e` over a closer `rc` (`closerSpec`), `br` bytes read of `total`: closes `rc`;
returns its error if non-nil, else `ErrShortRead` if `br < total`, else `nil`. -/
abbrev ioutil.exactReadCloser.Close.spec : Prop :=
  ∀ (e : Loc) (rc : GoInterfaceOk) (C : IProp GF) (br total : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.ioutil ∗
      e ↦ (ioutil.exactReadCloser.mk (GoInterface.ok rc) br total) ∗ closerSpec rc C ∗ C }}
    (App (Val (e @!! go.GoType.PointerType ioutil.exactReadCloser.ty @!! go!"Close")) (Val #()))
  {{ (err' : GoInterface), RET #err';
      e ↦ (ioutil.exactReadCloser.mk (GoInterface.ok rc) br total) ∗
      ((⌜err' ≠ GoInterface.nil⌝) ∨
       (⌜sint.Z br < sint.Z total⌝ ∗ globalAddr ioutil.ErrShortRead ↦□ err') ∨
       ⌜¬ sint.Z br < sint.Z total ∧ err' = GoInterface.nil⌝) }}

end spec

end EtcdGrove
end Perennial
