/-
**The body of `(*Client).dialWithBalancerForKey`** (`client/v3/client.go:335`; item 5, client
construction, 2026-10-17; branch `construct`; updated for PR #21765): a trusted unfolding.
Lean-first (no Rocq counterpart).

```go
func (c *Client) dialWithBalancerForKey(ctx context.Context, key string, r *resolver.EtcdManualResolver, endpoints []string, dopts ...grpc.DialOption) (*grpc.ClientConn, error) {
	if len(endpoints) == 0 {
		return nil, ErrNoAvailableEndpoints
	}
	creds := c.credentialsForEndpoint(endpoints[0])
	opts := append(dopts, grpc.WithResolvers(r))
	return c.dialWithContext(ctx, key, endpoints[0], creds, opts...)
}
```

The pinned translator cannot translate it (`Code/go_etcd_io/etcd/client/v3.toml`): the argument of
`grpc.WithResolvers` is converted to grpc's `resolver.Builder`, a package no file of `clientv3`
imports, and the translator's `pkgRef` then names the type after the imported package of the same
name, the client's `internal/resolver` (`_root_.Perennial.go_etcd_io.etcd.client.v3.internal.
resolver.Builder.ty`, which does not exist); the translation does not elaborate. The method is
translated names only, and `trustedImpl` below is the pinned translator's output for it,
verbatim but for that type, corrected to `google_golang_org.grpc.resolver.Builder.ty`
(three occurrences: the conversion, the variadic slice's type and its element's).
The hypothesis class `DialWithBalancerBody` says the method's body is it (`unfold`: the generated
packages' `MethodUnfold` facts, for this one method), and grpc `resolver`'s
`Builder.TypeAssumptions` (`builderType`: the underlying type of `resolver.Builder`, which the
conversion needs, and which `clientv3`'s assumptions do not include).
-/
module

public import Code.go_etcd_io.etcd.client.v3
public import Code.google_golang_org.grpc.resolver

@[expose] public section

set_option maxRecDepth 100000
set_option linter.unusedVariables false

namespace Perennial
noncomputable section

namespace go_etcd_io.etcd.client.v3

/-- The pinned translator's output for `(*Client).dialWithBalancerForKey`, with grpc's
`resolver.Builder` for the type it misnames (see the file header). -/
noncomputable def Client.dialWithBalancerForKey.trustedImpl [FfiSyntax] [GoGlobalContext] : val :=
  (LamV "c"
  (Lam "ctx"
  (Lam "key"
  (Lam "r"
  (Lam "endpoints"
  (Lam "dopts"
  (App (Val exceptionDo)
  (Let "c" (App (Val (GoInstruction (GoAlloc (go.GoType.PointerType Client.ty)))) (Var "c"))
  (Let "dopts" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType _root_.Perennial.google_golang_org.grpc.DialOption.ty)))) (Var "dopts"))
  (Let "endpoints" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.string)))) (Var "endpoints"))
  (Let "r" (App (Val (GoInstruction (GoAlloc (go.GoType.PointerType _root_.Perennial.go_etcd_io.etcd.client.v3.internal.resolver.EtcdManualResolver.ty)))) (Var "r"))
  (Let "key" (App (Val (GoInstruction (GoAlloc go.string))) (Var "key"))
  (Let "ctx" (App (Val (GoInstruction (GoAlloc _root_.Perennial.context.Context.ty))) (Var "ctx"))
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (App (Val (GoInstruction (IndexRef (go.GoType.SliceType go.string)))) (Pair (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.string)))) (Var "endpoints")) (Val #(W64 0)))))
  (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType Client.ty) go!"credentialsForEndpoint"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType Client.ty)))) (Var "c"))) (Var "$a0")))
  (Let "creds" (App (Val (GoInstruction (GoAlloc _root_.Perennial.google_golang_org.grpc.credentials.TransportCredentials.ty))) (App (Val (GoInstruction (GoZeroVal _root_.Perennial.google_golang_org.grpc.credentials.TransportCredentials.ty))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType _root_.Perennial.google_golang_org.grpc.DialOption.ty)))) (Var "dopts"))
  (Let "$a1" (Let "$sl0" (Let "$a0" (Let "$sl0" (App (Val (GoInstruction (Convert (go.GoType.PointerType _root_.Perennial.go_etcd_io.etcd.client.v3.internal.resolver.EtcdManualResolver.ty) _root_.Perennial.google_golang_org.grpc.resolver.Builder.ty))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.go_etcd_io.etcd.client.v3.internal.resolver.EtcdManualResolver.ty)))) (Var "r")))
  (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType _root_.Perennial.google_golang_org.grpc.resolver.Builder.ty)))) (LiteralValue [(KeyedElement none (ElementExpression _root_.Perennial.google_golang_org.grpc.resolver.Builder.ty (Var "$sl0")))])))
  (App (App (Val (GoInstruction (FuncResolve _root_.Perennial.google_golang_org.grpc.WithResolvers []))) (Val #())) (Var "$a0")))
  (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType _root_.Perennial.google_golang_org.grpc.DialOption.ty)))) (LiteralValue [(KeyedElement none (ElementExpression _root_.Perennial.google_golang_org.grpc.DialOption.ty (Var "$sl0")))])))
  (App (App (App (Val (GoInstruction (FuncResolve go.append [(go.GoType.SliceType _root_.Perennial.google_golang_org.grpc.DialOption.ty)]))) (Val #())) (Var "$a0")) (Var "$a1"))))
  (Let "opts" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType _root_.Perennial.google_golang_org.grpc.DialOption.ty)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.SliceType _root_.Perennial.google_golang_org.grpc.DialOption.ty)))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad _root_.Perennial.context.Context.ty))) (Var "ctx"))
  (Let "$a1" (App (Val (GoInstruction (GoLoad go.string))) (Var "key"))
  (Let "$a2" (App (Val (GoInstruction (GoLoad go.string))) (App (Val (GoInstruction (IndexRef (go.GoType.SliceType go.string)))) (Pair (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.string)))) (Var "endpoints")) (Val #(W64 0)))))
  (Let "$a3" (App (Val (GoInstruction (GoLoad _root_.Perennial.google_golang_org.grpc.credentials.TransportCredentials.ty))) (Var "creds"))
  (Let "$a4" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType _root_.Perennial.google_golang_org.grpc.DialOption.ty)))) (Var "opts"))
  (App (App (App (App (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType Client.ty) go!"dialWithContext"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType Client.ty)))) (Var "c"))) (Var "$a0")) (Var "$a1")) (Var "$a2")) (Var "$a3")) (Var "$a4")))))))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (App (Val doReturn)
  (Pair (Var "$ret0") (Var "$ret1"))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.SliceType _root_.Perennial.google_golang_org.grpc.DialOption.ty)))) (Pair (Var "opts") (Var "$r0")))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore _root_.Perennial.google_golang_org.grpc.credentials.TransportCredentials.ty))) (Pair (Var "creds") (Var "$r0")))))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.int))) (Pair (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.string)))) (Var "endpoints"))
  (App (App (Val (GoInstruction (FuncResolve go.len [(go.GoType.SliceType go.string)]))) (Val #())) (Var "$a0"))) (Val #(W64 0)))))
  (App (Val doReturn)
  (Pair (App (Val (GoInstruction (Convert go.untypedNil (go.GoType.PointerType _root_.Perennial.google_golang_org.grpc.ClientConn.ty)))) (Val UntypedNil)) (App (Val (GoInstruction (GoLoad go.error))) (App (Val (GoInstruction (GlobalVarAddr ErrNoAvailableEndpoints))) (Val #())))))
  (App (Val doExecute)
  (Val #())))))))))))))))))

/-- **`(*Client).dialWithBalancerForKey`'s body, and grpc `resolver.Builder`'s underlying type** (a
hypothesis on the semantics in use; see the file header). -/
class DialWithBalancerBody [FfiSyntax] [GoGlobalContext] [GoLocalContext]
    [GoSemanticsFunctions] : Prop where
  /-- The method's body is `trustedImpl`: what the generated `Client.TypeAssumptions` would hold
  as `ptr_dialWithBalancerForKey_unfold`. -/
  unfold : MethodUnfold (go.GoType.PointerType Client.ty) go!"dialWithBalancerForKey"
    Client.dialWithBalancerForKey.trustedImpl
  /-- grpc's `resolver.Builder` is the interface type the translation says: grpc `resolver`'s
  `Builder.TypeAssumptions`, which `clientv3`'s assumptions do not include (`clientv3` does not
  import it). -/
  builderType : _root_.Perennial.google_golang_org.grpc.resolver.Builder.TypeAssumptions

attribute [instance] DialWithBalancerBody.unfold DialWithBalancerBody.builderType

end go_etcd_io.etcd.client.v3

end
end Perennial
