/-
Lean-first (no Rocq counterpart).

# The driver's model: its Go values (stage 6a)

`storeOwn s g`, `cfgOwn c g`: the Go store `s`'s items hold `g`'s, the configuration `c`'s store
and pending inputs hold `g`'s, read-only (configurations share slices: `step` returns `c.st` in a
new configuration), as linkvtxn's `Defs.lean`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8setcd3.KSteps
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8setcd3.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8setcd3

open Iris Iris.BI
open github_com.mit_pdos.etcd_grove.examples.k8setcd3 (mstore mcfg item Input)

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions]

/-- A Go store holds `g` (see the file header). -/
def storeOwn (s : mstore) (g : GSt) : IProp GF :=
  iprop(s.items' ↦*□ g.items ∗ ⌜s.rv' = g.rv⌝)

instance storeOwn_persistent (s : mstore) (g : GSt) : Persistent (storeOwn (GF := GF) s g) := by
  unfold storeOwn; infer_instance

/-- A Go configuration holds `g` (see the file header). -/
def cfgOwn (c : mcfg) (g : GCfg) : IProp GF := iprop(storeOwn c.st' g.st ∗ c.pend' ↦*□ g.pend)

instance cfgOwn_persistent (c : mcfg) (g : GCfg) : Persistent (cfgOwn (GF := GF) c g) := by
  unfold cfgOwn; infer_instance

end defs

end k8setcd3
end EtcdGrove
end Perennial
