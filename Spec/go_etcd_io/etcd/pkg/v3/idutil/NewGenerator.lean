/-
`idutil.NewGenerator(memberID, now)` (`id.go`): a new request id generator. Lean-first (no Rocq
counterpart).
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.idutil.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.pkg.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `NewGenerator(memberID, now)` returns a generator (`idGen`, fresh ghost names) with its
`2 ^ 48 - 1` id credits: its prefix `memberID << 48`, its suffix the 40 low bits of `now`'s
milliseconds, shifted by 8. -/
abbrev idutil.NewGenerator.spec : Prop :=
  ∀ (memberID : w16) (now : time.Time),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.idutil }}
    (App (App (Val (@! idutil.NewGenerator)) (Val #memberID)) (Val #now))
  {{ (g : Loc), RET #g; ∃ γi : IdNames, idGen γi g ∗ idCred γi (2 ^ 48 - 1) }}

end spec

end EtcdGrove
end Perennial
