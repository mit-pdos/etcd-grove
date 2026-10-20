/- Lean-first (no Rocq counterpart).

`pick(n, m)` (linkvtxn.go): `n mod m` and `n / m`, for `m` not zero.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkvtxn.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkvtxn

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.linkvtxn


section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkvtxn.Assumptions]

/-- See the file header. -/
abbrev pick.spec : Prop :=
  ∀ (n m : w64), m ≠ W64 0 →
  {{ (True : IProp GF) }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.linkvtxn.pick)) (Val #n)) (Val #m))
  {{ RET (PairV #(n % m) #(n / m)); True }}

end spec

end linkvtxn
end EtcdGrove
end Perennial
