/-
**The reflector's typed lists' `ListMeta` accessors: a pending hypothesis** (k8s 7g follow-up (B'),
`notes/k8s-7g-listaccessor-bprime.md` step 4; approved by the user, 2026-11-20; not a Go function's
spec: a fact named for what it states, linked as a `?` entry of `etc/link-lean-first-k8scache.txt`).

The reflector's lists (`resListTy r`: `*v1.PodList`, `*v1.NodeList`, `*appsv1.DaemonSetList`,
`*appsv1.ControllerRevisionList`) reach `meta.ListAccessor` in `ListPager.list`, whose result the
pager and the reflector then ask for its version and continue token. What that needs of the typed
lists, and what `meta.ListAccessor`'s spec said of them until (B'):

1. `*L` is in `meta.List`'s type set (so the type switch's first case returns it unchanged,
   `ListAccessor.spec`): `L` embeds `metav1.ListMeta`, whose pointer methods `*L` promotes;
2. `GetResourceVersion()` on `*L` returns the list's version (`ListMeta.ResourceVersion`);
3. `GetContinue()` on `*L` returns its continue token, `""` (`typedListAt`'s lists have none).

Each is a fact about `k8s.io/api/{core,apps}/v1`: (1) of those packages' method sets
(`PodList.TypeAssumptions.ptr_method_set`, ...), (2) and (3) of their promoted methods
(`ptr_unfold'GetResourceVersion`, ..., translated since (B')) and of `metav1.ListMeta`'s two getters
(translated with bodies). So it is provable under `k8s.io/api/core/v1`'s and `apps/v1`'s
`Assumptions`, which client-go cache's Link does not take: there it stays a hypothesis
(`h_typedListMeta`, `section links_pending`) of the results that reach the pager (all of which are
pending for other reasons already), to be discharged by a Link that takes those instances. Go evidence:
`examples/k8s/daemonset/apimodel/typedlistmeta_test.go` `TestTypedListMeta`.
-/
module

public import Proof.k8s_io.client_go.tools.cache.RefWatchDefs
public import Code.k8s_io.apimachinery.pkg.api.«meta»

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI apimodel

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The typed list `*resListTy r`** is a `meta.List`, and its `GetResourceVersion()` and
`GetContinue()` read the list's metadata, the list's ownership kept. -/
abbrev typedListMeta.spec : Prop :=
  ∀ (r : Res),
    go.typeSetContains (go.GoType.PointerType (resListTy r))
      k8s_io.apimachinery.pkg.api.«meta».List''.ty = true ∧
    (∀ (q : Loc) (os : List Obj) (rv : GoString),
      {{ typedListAt (GF := GF) r q os rv }}
        (App (Val #(methods (go.GoType.PointerType (resListTy r)) go!"GetResourceVersion" #q))
          (Val #()))
      {{ RET #rv; typedListAt r q os rv }}) ∧
    (∀ (q : Loc) (os : List Obj) (rv : GoString),
      {{ typedListAt (GF := GF) r q os rv }}
        (App (Val #(methods (go.GoType.PointerType (resListTy r)) go!"GetContinue" #q))
          (Val #()))
      {{ RET #(go!""); typedListAt r q os rv }})

end spec

end cache
end EtcdGrove
end Perennial
