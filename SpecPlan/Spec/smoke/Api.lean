module

public import GeneratedProof.go_etcd_io.etcd.client.v3
public import SpecPlan.Spec.PkgInit.go_etcd_io.etcd.client.v3

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace SmokeApi

open Iris Iris.BI

/-- Ghost names: opaque. -/
opaque Names : Type := Unit

/-- A pure model: transparent. -/
structure KV where
  rev : Nat
  store : List (String × String)

section
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]

/-- Opaque resource. -/
opaque etcdKV (γ : Names) (σ : KV) : IProp GF := iprop(True)

opaque kvHandle (l : Loc) (γ : Names) : IProp GF := iprop(True)

/-- A law, as an obligation. -/
def etcdKV_excl.spec : Prop := ∀ (γ : Names) (σ σ' : KV),
  etcdKV (GF := GF) γ σ ∗ etcdKV γ σ' ⊢ iprop(False)
end

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

def kv.Put.spec : Prop :=
  ∀ (kv : Loc) (γ : Names) (ctx : GoInterface) (key val : GoString) (opts_sl : GoSlice)
    (Q : KV → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ kvHandle kv γ ∗
      (AU <{ ∃∃ (σ : KV), etcdKV γ σ }> @ ⊤, ∅
        <{ etcdKV γ σ, COMM Q σ }>) }}
    (App (App (App (App (Val (kv @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
        go!"Put")) (Val #ctx)) (Val #key)) (Val #val)) (Val #opts_sl))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      ⌜err = GoInterface.nil⌝ ∗ ∃ σ, Q σ }}
end spec
end SmokeApi
end EtcdGrove
end Perennial
