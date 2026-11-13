/-
`d.Sum32()` on a `*digest` (`pkg/v3/crc`, translated with its body): its CRC, at any fraction.
Proved in `LinuxFs/Proof/go_etcd_io/etcd/pkg/v3/crc/digest__Sum32.lean`. Lean-first.
-/
module

public import LinuxFs.GeneratedProof.go_etcd_io.etcd.pkg.v3.crc
public import LinuxFs.Spec.hash.crc32.Model

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.pkg.v3.crc.Assumptions]

/-- See the file header. -/
abbrev go_etcd_io.etcd.pkg.v3.crc.digest.Sum32.spec : Prop :=
  ∀ (l : Loc) (c : w32) (tab : Loc) (dq : DFrac),
  {{ (l ↦{dq} go_etcd_io.etcd.pkg.v3.crc.digest.mk c tab : IProp GF) }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.pkg.v3.crc.digest.ty @!! go!"Sum32")) (Val #()))
  {{ RET #c; l ↦{dq} go_etcd_io.etcd.pkg.v3.crc.digest.mk c tab }}

end spec

end EtcdGrove
end Perennial
