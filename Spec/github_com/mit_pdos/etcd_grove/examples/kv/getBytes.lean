/- Lean-first (no Rocq counterpart).

`getBytes(b)` (kv.go, D22 S-r): what `putBytes` wrote at the start of `b` (`putB x`), and the
rest, both slices of `b`, and `ok`. Stated of bytes `putBytes` wrote (what `decodeState` reads):
the two parts are `b`'s (`ownSlice_slice`), and give it back.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kv

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]

/-- See the file header. -/
abbrev getBytes.spec : Prop :=
  ∀ (b : GoSlice) (dq : DFrac) (x r : List w8),
  (x.length : Int) < 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kv ∗
      b ↦*{dq} (putB x ++ r) }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.kv.getBytes)) (Val #b))
  {{ (v rest : GoSlice), RET (PairV (PairV #v #rest) #true);
      v ↦*{dq} x ∗ rest ↦*{dq} r ∗ (v ↦*{dq} x -∗ rest ↦*{dq} r -∗ b ↦*{dq} (putB x ++ r)) }}

end spec

end kv
end EtcdGrove
end Perennial
