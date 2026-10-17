/-
`(*exactReadCloser).Read(p)` (`pkg/ioutil/readcloser.go`). Lean-first (no Rocq counterpart).
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

/-- `e.Read(p)`, `e` over a reader `rc` (`readerSpec`) that has delivered `k` bytes, `br` of
them counted by `e`, of `total`: one underlying read of `n` bytes (`0 ≤ n ≤ len(p)`) with error
`err`; `e` now counts `br + n`, and the result is `exactReadResult` (`ioutil/Defs.lean`):
`(0, ErrExpectEOF)` past the total, `(0, ErrShortRead)` short of it on an empty read, else
`(n, err)`. -/
abbrev ioutil.exactReadCloser.Read.spec : Prop :=
  ∀ (e : Loc) (rc : GoInterfaceOk) (R : Nat → IProp GF) (Buf : GoSlice → IProp GF) (k : Nat)
    (br total : w64) (p : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.ioutil ∗
      e ↦ (ioutil.exactReadCloser.mk (GoInterface.ok rc) br total) ∗ readerSpec rc R Buf ∗
      R k ∗ Buf p }}
    (App (Val (e @!! go.GoType.PointerType ioutil.exactReadCloser.ty @!! go!"Read")) (Val #p))
  {{ (n' : w64) (err' : GoInterface), RET (PairV #n' #err');
      ∃ (n : w64) (err : GoInterface),
      e ↦ (ioutil.exactReadCloser.mk (GoInterface.ok rc) (br + n) total) ∗ R (k + sint.nat n) ∗
      Buf p ∗ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z p.len⌝ ∗
      exactReadResult (br + n) total n n' err err' }}

end spec

end EtcdGrove
end Perennial
