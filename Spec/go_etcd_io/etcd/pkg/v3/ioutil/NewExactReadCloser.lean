/-
`ioutil.NewExactReadCloser(rc, totalBytes)` (`pkg/ioutil/readcloser.go`): a new exact reader over
`rc`, nothing read yet. Lean-first (no Rocq counterpart).
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

/-- `NewExactReadCloser(rc, total)` returns an `io.ReadCloser` holding a new `*exactReadCloser`
over `rc`, with `0` bytes read of `total`. -/
abbrev ioutil.NewExactReadCloser.spec : Prop :=
  ∀ (rc : GoInterface) (total : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.ioutil }}
    (App (App (Val (@! ioutil.NewExactReadCloser)) (Val #rc)) (Val #total))
  {{ (x : GoInterface), RET #x; ∃ e : Loc,
      ⌜x = interface.mkOk (go.GoType.PointerType ioutil.exactReadCloser.ty) #e⌝ ∗
      e ↦ (ioutil.exactReadCloser.mk rc 0 total) }}

end spec

end EtcdGrove
end Perennial
