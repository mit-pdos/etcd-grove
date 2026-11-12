/-
`etcdserverpb.CompactionRequest.GetPhysical()` (`api/etcdserverpb/rpc.pb.go`, translated for the server's
`Compact`: its trace attributes; the spec-first pilot, 2026-10-27). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `p.GetPhysical()` on a non-nil `*CompactionRequest` returns its `Physical` field. -/
abbrev CompactionRequest.GetPhysical.spec : Prop :=
  ∀ (p : Loc) (v : Bool) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗ ⌜p ≠ null⌝ ∗
      structFieldRef etcdserverpb.CompactionRequest go!"Physical" p ↦{dq} v }}
    (App (Val (p @!! go.GoType.PointerType etcdserverpb.CompactionRequest.ty @!! go!"GetPhysical")) (Val #()))
  {{ RET #v; structFieldRef etcdserverpb.CompactionRequest go!"Physical" p ↦{dq} v }}

end spec

end EtcdGrove
end Perennial
