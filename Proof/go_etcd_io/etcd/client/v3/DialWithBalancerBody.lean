/-
**`(*Client).dialWithBalancer`'s body and grpc `resolver.Builder`'s underlying type, from the
translation** (`client/v3/client.go:311`). Lean-first (no Rocq counterpart).

The method is translated with its body (`Code/go_etcd_io/etcd/client/v3.toml`), so both facts are
fields of `clientv3`'s generated `Assumptions`: the method's unfolding is `Client.TypeAssumptions`'s
`ptr_dialWithBalancer_unfold`, and `resolver.Builder.TypeAssumptions` is reached through the
assumptions of the client's `internal/resolver`, which imports grpc's `resolver`. The class
`DialWithBalancerBody` states the two over the generated body, and `ofAssumptions` proves it from
`clientv3`'s `Assumptions`. No proof takes it: it remains only as an instance binder of top-level
statements, which the proved instance discharges, until their binders are deleted.
-/
module

public import Code.go_etcd_io.etcd.client.v3
public import Code.google_golang_org.grpc.resolver

@[expose] public section

namespace Perennial
noncomputable section

namespace go_etcd_io.etcd.client.v3

/-- **`(*Client).dialWithBalancer`'s body, and grpc `resolver.Builder`'s underlying type**, as the
translation states them (see the file header). -/
class DialWithBalancerBody [GooseExts] [GoGlobalContext] [GoLocalContext]
    [GoSemanticsFunctions] : Prop where
  /-- The method's body is the translation's (`Client.TypeAssumptions.ptr_dialWithBalancer_unfold`). -/
  unfold : MethodUnfold (go.GoType.PointerType Client.ty) go!"dialWithBalancer"
    Client.dialWithBalancer.impl
  /-- grpc's `resolver.Builder` is the interface type the translation says (grpc `resolver`'s
  `Builder.TypeAssumptions`). -/
  builderType : _root_.Perennial.google_golang_org.grpc.resolver.Builder.TypeAssumptions

/-- **`DialWithBalancerBody` holds** at every semantics satisfying `clientv3`'s `Assumptions`. -/
instance DialWithBalancerBody.ofAssumptions [GooseExts] [GoGlobalContext] [GoLocalContext]
    [GoSemanticsFunctions] [Assumptions] : DialWithBalancerBody :=
  ⟨inferInstance, inferInstance⟩

end go_etcd_io.etcd.client.v3

end
end Perennial
