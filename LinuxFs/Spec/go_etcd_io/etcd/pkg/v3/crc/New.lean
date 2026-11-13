/-
`crc.New(prev, tab)` (`pkg/v3/crc`, translated with its body): a fresh `*digest` holding `prev` and
`tab`, returned as a `hash.Hash32`. Proved in `LinuxFs/Proof/go_etcd_io/etcd/pkg/v3/crc/New.lean`.
Lean-first.
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
abbrev go_etcd_io.etcd.pkg.v3.crc.New.spec : Prop :=
  ∀ (prev : w32) (tab : Loc),
  {{ (True : IProp GF) }}
    (App (App (Val (@! go_etcd_io.etcd.pkg.v3.crc.New)) (Val #prev)) (Val #tab))
  {{ (l : Loc), RET #(interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.pkg.v3.crc.digest.ty) #l);
      l ↦ go_etcd_io.etcd.pkg.v3.crc.digest.mk prev tab }}

end spec

end EtcdGrove
end Perennial
