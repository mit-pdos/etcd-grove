/- Lean-first (no Rocq counterpart). `initPages(buf, pageSize)` (`examples/bboltfs/page.go`), as `init` calls it: over a zeroed buffer of four 4096-byte pages, it lays out `initBytes` (`Pages.lean`): two valid metas (`initMeta_valid`) with txids 0 and 1, root 3, freelist 2 and high water mark 4, the empty freelist page 2 and the empty leaf page 3. -/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.Pages

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

/-- See the file header. -/
abbrev initPages.spec : Prop :=
  ∀ (buf : GoSlice),
    {{ (buf ↦* zeroBytes (4 * pageBytes) : IProp GF) }}
      (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.bboltfs.initPages)) (Val #buf))
        (Val #(W64 4096)))
    {{ RET #(); buf ↦* initBytes }}

end spec

end bboltfs
end EtcdGrove
end Perennial
