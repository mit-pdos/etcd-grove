/- Lean-first (no Rocq counterpart). `initPages(buf, pageSize)` (`examples/osfs/bboltfs/page.go`), as `init` calls it: over a zeroed buffer of four 4096-byte pages, it lays out `initBytes` (`Pages.lean`): two valid metas (`initMeta_valid`) with txids 0 and 1, root 3, freelist 2 and high water mark 4, the empty freelist page 2 and the empty leaf page 3. -/
module

public import LinuxFs.Proof.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.Pages

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
abbrev initPages.spec : Prop :=
  ∀ (buf : GoSlice),
    {{ (buf ↦* zeroBytes (4 * pageBytes) : IProp GF) }}
      (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.initPages)) (Val #buf))
        (Val #(W64 4096)))
    {{ RET #(); buf ↦* initBytes }}

end spec

end osfs_bboltfs
end EtcdGrove
end Perennial
