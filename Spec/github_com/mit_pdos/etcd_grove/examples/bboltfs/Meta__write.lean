/- Lean-first (no Rocq counterpart). `m.write(p)` (`examples/bboltfs/page.go`): sets `m`'s checksum (`metaSum`), the page header's id (`txid % 2`) and flags (`metaPageFlag`), and copies `*m` into the page's meta, 16 bytes past `p`. The page's bytes then encode a valid meta if `m`'s magic and version are right (`metaValid_withSum`; as bytes, `pageMeta_view`). -/
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

/-- See the file header. -/
abbrev Meta.write.spec : Prop :=
  ∀ (m p : Loc) (v : Meta) (hdr : Page) (old : Meta),
    {{ (m ↦ v ∗ p ↦ hdr ∗ (p +ₗ 16) ↦ old ∗ ⌜0 < m.addr ∧ 0 < p.addr⌝ : IProp GF) }}
      (App (Val (m @!! go.GoType.PointerType Meta.ty @!! go!"write")) (Val #p))
    {{ RET #();
        m ↦ { v with checksum' := metaSum v } ∗
        p ↦ { hdr with id' := v.txid' % W64 2, flags' := W16 4 } ∗
        (p +ₗ 16) ↦ { v with checksum' := metaSum v } }}

end spec

end bboltfs
end EtcdGrove
end Perennial
