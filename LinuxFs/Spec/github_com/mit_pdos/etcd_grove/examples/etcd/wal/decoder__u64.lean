/- Lean-first (no Rocq counterpart).

`d.u64()` (`examples/etcd/wal/oracle.go`): at an offset where the bytes left start with `tU64 x`,
returns `x` and moves the offset past them.
-/
module

public import LinuxFs.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.DecRep

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.etcd.wal

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions]

/-- See the file header. -/
abbrev decoder.u64.spec : Prop :=
  ∀ (d : Loc) (bs : List w8) (k : Nat) (x : w64) (r : List w8), bs.drop k = tU64 x ++ r →
  {{ decRep (GF := GF) d bs k }}
    (App (Val (d @!! go.GoType.PointerType decoder.ty @!! go!"u64")) (Val #()))
  {{ RET #x; decRep d bs (k + 8) }}

end spec

end etcd_wal
end EtcdGrove
end Perennial
