/- Lean-first (no Rocq counterpart). `m.sum64()` (`examples/osfs/bboltfs/page.go`): FNV-64a over the bytes of `*m` before its checksum (`metaSum`), read through any fraction of `*m` (a mapped meta page). -/
module

public import LinuxFs.Proof.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.Meta

@[expose] public section

noncomputable section

namespace Perennial

open Fs
namespace EtcdGrove
namespace osfs_bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.Assumptions]

/-- See the file header. -/
abbrev Meta.sum64.spec : Prop :=
  ∀ (m : Loc) (v : Meta) (dq : DFrac),
    {{ (m ↦{dq} v ∗ ⌜0 < m.addr⌝ : IProp GF) }}
      (App (Val (m @!! go.GoType.PointerType Meta.ty @!! go!"sum64")) (Val #()))
    {{ RET #(metaSum v); m ↦{dq} v }}

end spec

end osfs_bboltfs
end EtcdGrove
end Perennial
