/-
`grpclog.Component`'s spec (phase7-inits batch 2, 2026-11-25, `notes/phase7-endstate.md` §4).

Go (grpc-go v1.84.0, `grpclog/component.go:108-116`, the model's unchanged):
```go
func Component(componentName string) DepthLoggerV2 {
	if cData, ok := cache[componentName]; ok {
		return cData
	}
	c := &componentData{componentName}
	cache[componentName] = c
	return c
}
```
It returns a `*componentData` (the cached one or a new one), as a `DepthLoggerV2`. `cache` is a plain
map: `Component` is not thread-safe, and grpc calls it only from package variable initializers (the
`logger`s of grpc, `credentials`, `health`, `connectivity`, ...). The spec takes a package initializer's
state (`EtcdGrove.ownInitLb`), through which `grpclog`'s fact (`grpclogInit`, `cache/v3/Base.lean`) lends
the map; a call outside initialization has no proof. The returned value's dynamic type is what
`grpclog.SetLoggerV2`'s premise excludes (`Spec/google_golang_org/grpc/grpclog/SetLoggerV2.lean`).
-/
module

public import GeneratedProof.google_golang_org.grpc.grpclog
public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Proof.runtime.PkgInit

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- See the file header. -/
abbrev grpclog.Component.spec : Prop :=
  ∀ (name : GoString) (g : GoString → IProp GF) (σ0 : GMap GoString Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.grpclog ∗ EtcdGrove.ownInitLb g σ0 }}
    (App (Val (@! google_golang_org.grpc.grpclog.Component)) (Val #name))
  {{ (l : GoInterface), RET #l; EtcdGrove.ownInitLb g σ0 ∗
      ⌜∃ p : Loc, l = interface.mkOk
        (go.GoType.PointerType google_golang_org.grpc.grpclog.componentData.ty) #p⌝ }}

end spec

end EtcdGrove
end Perennial
