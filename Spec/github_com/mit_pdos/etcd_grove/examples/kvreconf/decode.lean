/- Lean-first (no Rocq counterpart).

`decode(b)` (kv.go): what `encode` wrote (`decodeOp`), or `ok = false` for fewer than 17 bytes
or a key length past the end.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI go_etcd_io.raft.v3
open github_com.anishathalye.porcupine

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]

/-- `decode`'s results on `d`. -/
def decodeRet (d : List w8) : val :=
  match decodeOp d with
  | some (i, k, key, v) => PairV (PairV (PairV (PairV #i #k) #key) #v) #true
  | none => PairV (PairV (PairV (PairV #(W64 0) #(W8 0)) #([] : List w8))
      #([] : List w8)) #false

/-- See the file header. -/
abbrev decode.spec : Prop :=
  ∀ (b : GoSlice) (d : List w8) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvreconf ∗ b ↦*{dq} d }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.kvreconf.decode)) (Val #b))
  {{ RET (decodeRet d); b ↦*{dq} d }}

end spec

end kvreconf
end EtcdGrove
end Perennial
