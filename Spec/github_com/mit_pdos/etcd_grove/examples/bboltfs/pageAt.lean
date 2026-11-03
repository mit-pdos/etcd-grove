/- Lean-first (no Rocq counterpart). `pageAt(b, off)` (`examples/bboltfs/page.go`): the address of byte `off` of `b`, where a page is viewed (`Pages.lean`, `pageMeta_view`). -/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.Meta

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.bboltfs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.bboltfs.Assumptions]

/-- See the file header. `b`'s bytes are not needed: only its address and length. -/
abbrev pageAt.spec : Prop :=
  ∀ (b : GoSlice) (off : w64),
    {{ (⌜0 < b.ptr.addr ∧ 0 ≤ sint.Z off ∧ sint.Z off < sint.Z b.len⌝ : IProp GF) }}
      (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.bboltfs.pageAt)) (Val #b)) (Val #off))
    {{ RET #(b.ptr +ₗ sint.Z off); True }}

end spec

end bboltfs
end EtcdGrove
end Perennial
