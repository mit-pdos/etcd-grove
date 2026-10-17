/-
**The body of `(*Client).dialWithBalancer`** (`client/v3/client.go:311`; item 5, client
construction, 2026-10-17; branch `construct`): a trusted unfolding. Lean-first (no Rocq
counterpart).

```go
func (c *Client) dialWithBalancer(dopts ...grpc.DialOption) (*grpc.ClientConn, error) {
	creds := c.credentialsForEndpoint(c.Endpoints()[0])
	opts := append(dopts, grpc.WithResolvers(c.resolver))
	return c.dial(creds, opts...)
}
```

The pinned translator cannot translate it (`Code/go_etcd_io/etcd/client/v3.toml`): the argument of
`grpc.WithResolvers` is converted to grpc's `resolver.Builder`, a package no file of `clientv3`
imports, and the translator's `pkgRef` then names the type after the imported package of the same
name, the client's `internal/resolver` (`_root_.Perennial.go_etcd_io.etcd.client.v3.internal.
resolver.Builder.ty`, which does not exist); the translation does not elaborate. The method is
translated names only, and `trustedImpl` below is the pinned translator's output for it
(Perennial `a54e1999f`, etcd `09669450f`), verbatim but for that type, corrected to
`google_golang_org.grpc.resolver.Builder.ty` (three occurrences: the conversion, the variadic
slice's type and its element's). The axiom `Client.dialWithBalancer.unfold` says the method's body
is it: the generated packages' `MethodUnfold` facts, for this one method; and
`Client.dialWithBalancer.builderType`, grpc `resolver`'s `Builder.TypeAssumptions` (the
underlying type of `resolver.Builder`, which the conversion needs, and which `clientv3`'s
assumptions do not include). A translator limitation,
to be fixed in Goose (a type of a package the file does not import, named after its own path, when
the package is imported in the configuration), not here: `notes/STATUS.md`, item 5.
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

/-- The pinned translator's output for `(*Client).dialWithBalancer`, with grpc's
`resolver.Builder` for the type it misnames (see the file header). -/
noncomputable def Client.dialWithBalancer.trustedImpl [FfiSyntax] [GoGlobalContext] : val :=
  (LamV "c"
  (Lam "dopts"
  (App (Val exceptionDo)
  (Let "c" (App (Val (GoInstruction (GoAlloc (go.GoType.PointerType Client.ty)))) (Var "c"))
  (Let "dopts" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType _root_.Perennial.google_golang_org.grpc.DialOption.ty)))) (Var "dopts"))
  (Let "$r0" (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (App (Val (GoInstruction (IndexRef (go.GoType.SliceType go.string)))) (Pair (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType Client.ty) go!"Endpoints"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType Client.ty)))) (Var "c"))) (Val #())) (Val #(W64 0)))))
  (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType Client.ty) go!"credentialsForEndpoint"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType Client.ty)))) (Var "c"))) (Var "$a0")))
  (Let "creds" (App (Val (GoInstruction (GoAlloc _root_.Perennial.google_golang_org.grpc.credentials.TransportCredentials.ty))) (App (Val (GoInstruction (GoZeroVal _root_.Perennial.google_golang_org.grpc.credentials.TransportCredentials.ty))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType _root_.Perennial.google_golang_org.grpc.DialOption.ty)))) (Var "dopts"))
  (Let "$a1" (Let "$sl0" (Let "$a0" (Let "$sl0" (App (Val (GoInstruction (Convert (go.GoType.PointerType _root_.Perennial.go_etcd_io.etcd.client.v3.internal.resolver.EtcdManualResolver.ty) _root_.Perennial.google_golang_org.grpc.resolver.Builder.ty))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.go_etcd_io.etcd.client.v3.internal.resolver.EtcdManualResolver.ty)))) (App (Val (GoInstruction (StructFieldRef Client.ty go!"resolver"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType Client.ty)))) (Var "c")))))
  (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType _root_.Perennial.google_golang_org.grpc.resolver.Builder.ty)))) (LiteralValue [(KeyedElement none (ElementExpression _root_.Perennial.google_golang_org.grpc.resolver.Builder.ty (Var "$sl0")))])))
  (App (App (Val (GoInstruction (FuncResolve _root_.Perennial.google_golang_org.grpc.WithResolvers []))) (Val #())) (Var "$a0")))
  (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType _root_.Perennial.google_golang_org.grpc.DialOption.ty)))) (LiteralValue [(KeyedElement none (ElementExpression _root_.Perennial.google_golang_org.grpc.DialOption.ty (Var "$sl0")))])))
  (App (App (App (Val (GoInstruction (FuncResolve go.append [(go.GoType.SliceType _root_.Perennial.google_golang_org.grpc.DialOption.ty)]))) (Val #())) (Var "$a0")) (Var "$a1"))))
  (Let "opts" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType _root_.Perennial.google_golang_org.grpc.DialOption.ty)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.SliceType _root_.Perennial.google_golang_org.grpc.DialOption.ty)))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad _root_.Perennial.google_golang_org.grpc.credentials.TransportCredentials.ty))) (Var "creds"))
  (Let "$a1" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType _root_.Perennial.google_golang_org.grpc.DialOption.ty)))) (Var "opts"))
  (App (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType Client.ty) go!"dial"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType Client.ty)))) (Var "c"))) (Var "$a0")) (Var "$a1"))))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (App (Val doReturn)
  (Pair (Var "$ret0") (Var "$ret1"))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.SliceType _root_.Perennial.google_golang_org.grpc.DialOption.ty)))) (Pair (Var "opts") (Var "$r0")))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore _root_.Perennial.google_golang_org.grpc.credentials.TransportCredentials.ty))) (Pair (Var "creds") (Var "$r0"))))))))))))

/-- **The body of `(*Client).dialWithBalancer`** (a trusted unfolding; see the file header): what
the generated `Client.TypeAssumptions` would hold as `ptr_dialWithBalancer_unfold`. -/
axiom Client.dialWithBalancer.unfold [FfiSyntax] [GoGlobalContext] [GoLocalContext]
    [GoSemanticsFunctions] :
  MethodUnfold (go.GoType.PointerType Client.ty) go!"dialWithBalancer"
    Client.dialWithBalancer.trustedImpl

attribute [instance] Client.dialWithBalancer.unfold

/-- **grpc's `resolver.Builder` is the interface type the translation says** (a trusted fact
about the semantics; see the file header): the body converts to it, and `clientv3`'s
assumptions do not include grpc `resolver`'s (`clientv3` does not import it), whose
`Builder.TypeAssumptions` this is. -/
axiom Client.dialWithBalancer.builderType [FfiSyntax] [GoGlobalContext] [GoLocalContext]
    [GoSemanticsFunctions] :
  _root_.Perennial.google_golang_org.grpc.resolver.Builder.TypeAssumptions

attribute [instance] Client.dialWithBalancer.builderType

end go_etcd_io.etcd.client.v3

end
end Perennial
