/-
`NewBytesAffinePoint` (`interval_tree.go`). Lean-first (no Rocq counterpart); see
`Proof/go_etcd_io/etcd/pkg/v3/adt/BytesIvl.lean`.
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.adt.BytesIvl

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.pkg.v3.adt

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.adt.Assumptions]

/-- `NewBytesAffinePoint(b)`: the interval `[b, b ++ [0])`, its end a fresh copy of `b` with a
zero byte appended (`make([]byte, len(b)+1)`: `len(b) + 1` must not overflow, which no slice in
memory reaches but the model's `make` does not assume: the premise). -/
abbrev adt.NewBytesAffinePoint.spec : Prop :=
  ∀ (b : GoSlice) (bs : List w8) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗ b ↦*{dq} bs ∗
      ⌜sint.Z b.len < 2 ^ 63 - 1⌝ }}
    (App (Val (@! go_etcd_io.etcd.pkg.v3.adt.NewBytesAffinePoint)) (Val #b))
  {{ (e : GoSlice), RET #(adt.bytesIvl b e); b ↦*{dq} bs ∗ e ↦* (bs ++ [W8 0]) }}

end spec

end EtcdGrove
end Perennial
