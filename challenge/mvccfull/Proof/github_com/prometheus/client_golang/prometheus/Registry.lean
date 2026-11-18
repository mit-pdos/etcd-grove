/-
prometheus's default registry as the read package's initializer uses it (item 8, 2026-10-17):
the trust boundary of `prometheus.NewCounter` and `prometheus.MustRegister` (names only in the
translation). `notes/decisions.md`, "D16: prometheus's default registry".

**The model.** `MustRegister(c)` (`registry.go`) calls `DefaultRegisterer.MustRegister`, which
panics if `Registry.Register(c)` fails: a descriptor of `c` invalid, or one with the
fully-qualified name of a registered descriptor but other labels or help, or `c`'s descriptor
IDs (hashes of the name and const label values) already registered, or its collector ID (their
XOR) already a registered collector's. So whether it panics depends on what was registered
before, by any package of the program: a resource. `nameFree n` is the exclusive right to
register `n`; the Hoare triple of `MustRegister` of a counter named `n` takes it. Program start
(the adequacy theorem, item 9) owns the rights of the names no default collector has, and gives
each to the one package that registers it (`readRegPerm`, the read package's); since every right
exists once, two packages registering one name would show up there, as two packages needing
one right.

**What is axiomatized** (each true of prometheus's Go code, client_golang v1.24.1, the version
etcd's `server/go.mod` pins):
- `counterOpts o ns sub name help`: `o` is the `CounterOpts` value with those four fields and
  the others zero (`Opts` is an axiomatized type, so its values are opaque);
- `collectorName c n`: the collector `c` describes exactly one descriptor, valid, named `n`,
  without labels (what `NewCounter` makes);
- `nameFree n` (abstract resource): the right to register a collector whose one descriptor is
  `n`'s, without labels, in the default registry: no collector registered there (now, or
  later by anyone but the holder) has a descriptor named `n`, nor one whose ID is that
  descriptor's ID (`xxhash(n + "\xff")`), nor a collector ID equal to it;
- `wp_counterOptsLit`: the composite literal `prometheus.CounterOpts{Namespace: ns, Subsystem:
  sub, Name: name, Help: help}` returns such a value.

Each is about uninterpreted constants (`Opts`, `CompositeLiteral` of its type, the names-only
functions), so a model in which they diverge satisfies them: they cannot make the logic
inconsistent. The specs of `NewCounter` and `MustRegister` are in
`Spec/github_com/prometheus/client_golang/prometheus/`.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Golang.Theory
public import Code.github_com.prometheus.client_golang.prometheus

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace prometheus

open Iris Iris.BI

section preds
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The right to register the name `n`** with prometheus's default registry (exclusive):
no collector registered there, now or later by anyone but the holder, has a descriptor named
`n`, or whose ID (or collector ID) is the ID of `n`'s label-free descriptor. Given at program
start, once per name. -/
axiom nameFree {GF : BundledGFunctors} (n : GoString) : IProp GF

end preds

end prometheus
end EtcdGrove
end Perennial
