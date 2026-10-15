/- Lean-first (no Rocq counterpart).

`decode(b)` (register.go:38): what `encode` wrote (`decodeOp`), or `ok = false` for fewer than
17 bytes.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.register.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace register

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.register.Assumptions]
variable [RegStor GF]

/-- `decode`'s results for the data `d`. -/
def decodeRet (d : List w8) : val :=
  match decodeOp d with
  | some (r, s, k, v) => PairV (PairV (PairV (PairV #r #s) #k) #v) #true
  | none => PairV (PairV (PairV (PairV #(W64 0) #(W64 0)) #(W8 0)) #([] : List w8)) #false

/-- See the file header. -/
abbrev decode.spec : Prop :=
  ∀ (b : GoSlice) (d : List w8) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.register ∗ b ↦*{dq} d }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.register.decode)) (Val #b))
  {{ RET (decodeRet d); b ↦*{dq} d }}

end spec

end register
end EtcdGrove
end Perennial
