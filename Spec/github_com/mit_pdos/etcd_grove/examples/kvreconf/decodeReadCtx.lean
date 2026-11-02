/- Lean-first (no Rocq counterpart).

`decodeReadCtx(b)` (kv.go): what `readCtx` wrote (`decodeReadCtxB`), or `ok = false`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]

/-- `decodeReadCtx`'s results on `d`. -/
def decodeReadCtxRet (d : List w8) : val :=
  match decodeReadCtxB d with
  | some (r, s, key) => PairV (PairV (PairV #r #s) #key) #true
  | none => PairV (PairV (PairV #(W64 0) #(W64 0)) #([] : List w8)) #false

/-- See the file header. -/
abbrev decodeReadCtx.spec : Prop :=
  ∀ (b : GoSlice) (d : List w8) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvreconf ∗ b ↦*{dq} d }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.kvreconf.decodeReadCtx)) (Val #b))
  {{ RET (decodeReadCtxRet d); b ↦*{dq} d }}

end spec

end kvreconf
end EtcdGrove
end Perennial
