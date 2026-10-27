/-
`types.ID.String`: the trust boundary (`client/pkg/v3/types` is names-only). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Base
public import Proof.unicode.utf8.Valid
public import Proof.go_etcd_io.etcd.client.pkg.v3.types.IDStr

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

/-- `id.String()` returns its hexadecimal rendering (`strconv.FormatUint(uint64(id), 16)`,
`types.idStr`; 2026-10-23, rafthttp stage 5d: until then an ASCII string, D19l (iii), and before
2026-10-18 some string). -/
abbrev types.ID.String.spec : Prop :=
  ∀ (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.types }}
    (App (Val (id @!! go_etcd_io.etcd.client.pkg.v3.types.ID.ty @!! go!"String")) (Val #()))
  {{ (s : GoString), RET #s; ⌜s = types.idStr id⌝ }}

end spec

end EtcdGrove
end Perennial
