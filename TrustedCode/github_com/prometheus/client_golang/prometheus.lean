/-
Trusted code for prometheus's client_golang v1.24.1 (`github.com/prometheus/client_golang/prometheus`,
names only but for these; `Code/github_com/prometheus/client_golang/prometheus.toml`): the default
registry, as the Go model `examples/lib/promreg` (translated with its bodies, verified), which these
definitions run in place of client_golang's (notes/prom-registry.md; the user's decision,
mit-pdos/etcd-grove#15, 2026-11-22).

* **`defaultRegistry.init`** (`registry.go`: `defaultRegistry = NewRegistry()`): allocates the
  variable and stores a new, empty `promreg.Registry` (`promreg.NewRegistry`, client_golang's
  `NewRegistry`), after initializing the model's package. Its type is the model's, not
  `*prometheus.Registry` (a names-only type whose methods are names-only): nothing translated reads
  the variable but these definitions. `DefaultRegisterer` and `DefaultGatherer`, which hold it in Go,
  keep their names-only initializers (`opaqueInitsOk`): code that calls through them is not modeled.
* **`init.«0»`** (`registry.go`'s `func init()`: `MustRegister(NewProcessCollector(
  ProcessCollectorOpts{}))`, `MustRegister(NewGoCollector())`): `promreg.(*Registry).SeedBuiltins`,
  the state those two registrations leave in the empty registry on configuration C (Linux, amd64,
  Go 1.27.3), checked against the real default registry by `model_test.go`'s `TestBuiltins`.
* **`Register(c)`** (`registry.go:162`, `DefaultRegisterer.Register(c)`, which is
  `(*Registry).Register`, `registry.go:283-376`): `promreg.(*Registry).Register` of `c`'s descriptors
  (`collectorDescs c`); a non-nil error (a zero `AlreadyRegisteredError`) when the model refuses.
  `TestDecisions` and `TestRandom` check that the model refuses exactly when client_golang does and
  keeps its state.
* **`MustRegister(cs...)`** (`registry.go:170`, `(*Registry).MustRegister`, `registry.go:416-422`):
  `Register` of each collector in order, panicking on the first error, as client_golang does.
* **`collectorDescs c`** (the model's one opaque operation): the descriptors `c.Describe` sends, in
  order, each as `promreg.Desc{ID: d.id, FQName: d.fqName, DimHash: d.dimHash, Invalid: d.err !=
  nil}` (`desc.go`'s fields), in a new slice. client_golang's `Register` reads exactly these fields of
  each descriptor (`registry.go:303-341`). It is not defined: what it returns for a collector is
  what the collector's constructor's spec says (`prometheus.collectorName`, `Registry.lean`), and
  `model_test.go`'s `DescsOf` is it, in Go, for the tests.

Deviations from client_golang, outside what any proof here uses:
- the error values: client_golang returns an `AlreadyRegisteredError` naming the registered collector,
  or an `fmt.Errorf` error; the model a zero `AlreadyRegisteredError` for every refusal. Code that
  inspects a registration error beyond `!= nil` is outside the model's faithful range (etcd's callers
  log it or test `!= nil`: `v3rpc/grpc.go:107`, `v2store/metrics.go:98`);
- `Unregister`, `Gather` and the registry's other methods are not modeled (names only): code that
  calls them is not provable;
- the registry the model allocates is the model's `Registry`, not client_golang's: code reading the
  variable `defaultRegistry` or `DefaultRegisterer`/`DefaultGatherer` other than through `Register`
  and `MustRegister` is not modeled.
-/
module

public import Perennial.Golang.Defn
public import Code.github_com.mit_pdos.etcd_grove.examples.lib.promreg

@[expose] public section

set_option linter.all false

namespace Perennial
namespace github_com.prometheus.client_golang.prometheus

noncomputable section
variable [GooseExts] [GoGlobalContext]

/-- The model's registry type, `*promreg.Registry`. -/
@[reducible] def model.registryPtr : go.GoType :=
  go.GoType.PointerType _root_.Perennial.github_com.mit_pdos.etcd_grove.examples.lib.promreg.Registry.ty

/-- The name of the variable `defaultRegistry` (the translation's). -/
@[reducible] def model.defaultRegistry : GoString :=
  go!"github.com/prometheus/client_golang/prometheus.defaultRegistry"

/-- The name of `Register` (the translation's). -/
@[reducible] def model.Register : GoString :=
  go!"github.com/prometheus/client_golang/prometheus.Register"

/-- The type `Collector` (the translation's `Collector.ty`). -/
@[reducible] def model.Collector : go.GoType :=
  go.GoType.Named go!"github.com/prometheus/client_golang/prometheus.Collector" []

/-- The type `AlreadyRegisteredError` (the translation's). -/
@[reducible] def model.AlreadyRegisteredError : go.GoType :=
  go.GoType.Named go!"github.com/prometheus/client_golang/prometheus.AlreadyRegisteredError" []

/-- **The descriptors of a collector, as `Register` reads them** (see the file header): not defined. -/
opaque collectorDescs.impl : val

/-- See the file header. -/
def defaultRegistry.init : val :=
  (LamV BAnon
  (App (Val exceptionDo)
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (App (Val (GoInstruction (FuncResolve _root_.Perennial.github_com.mit_pdos.etcd_grove.examples.lib.promreg.NewRegistry []))) (Val #())) (Val #()))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore model.registryPtr))) (Pair (App (Val (GoInstruction (GlobalVarAddr model.defaultRegistry))) (Val #())) (Var "$r0")))))))
  (App (Val doExecute)
  (App (Val _root_.Perennial.github_com.mit_pdos.etcd_grove.examples.lib.promreg.initialize') (Val #()))))))
  (App (Val doExecute)
  (App (Val (go.GlobalAlloc model.defaultRegistry model.registryPtr)) (Val #()))))))

/-- See the file header. -/
def init.«0».impl : val :=
  (LamV BAnon
  (Seq (App (Val exceptionDo)
  (App (Val doExecute)
  (App (App (Val (GoInstruction (MethodResolve model.registryPtr go!"SeedBuiltins"))) (App (Val (GoInstruction (GoLoad model.registryPtr))) (App (Val (GoInstruction (GlobalVarAddr model.defaultRegistry))) (Val #())))) (Val #()))))
  (Val #())))

/-- See the file header. -/
def Register.impl : val :=
  (LamV "c"
  (Let "$res0" (App (Val (GoInstruction (GoAlloc go.error))) (App (Val (GoInstruction (GoZeroVal go.error))) (Val #())))
  (Seq (App (Val exceptionDo)
  (Let "c" (App (Val (GoInstruction (GoAlloc model.Collector))) (Var "c"))
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (Val (GoInstruction (Convert go.untypedNil go.error))) (Val UntypedNil))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.error))) (Pair (Var "$res0") (Var "$r0"))))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.uint64))) (Pair (Let "$a0" (Let "$a0" (App (Val (GoInstruction (GoLoad model.Collector))) (Var "c"))
  (App (Val collectorDescs.impl) (Var "$a0")))
  (App (App (Val (GoInstruction (MethodResolve model.registryPtr go!"Register"))) (App (Val (GoInstruction (GoLoad model.registryPtr))) (App (Val (GoInstruction (GlobalVarAddr model.defaultRegistry))) (Val #())))) (Var "$a0"))) (Val #(W64 0))))))
  (Let "$r0" (App (Val (GoInstruction (Convert model.AlreadyRegisteredError go.error))) (App (Val (GoInstruction (GoZeroVal model.AlreadyRegisteredError))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.error))) (Pair (Var "$res0") (Var "$r0"))))))
  (App (Val doExecute)
  (Val #()))))))
  (App (Val (GoInstruction (GoLoad go.error))) (Var "$res0")))))

/-- See the file header. -/
def MustRegister.impl : val :=
  (LamV "cs"
  (Seq (App (Val exceptionDo)
  (Let "cs" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType model.Collector)))) (Var "cs"))
  (Let "$range" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType model.Collector)))) (Var "cs"))
  (Let "c" (App (Val (GoInstruction (GoAlloc model.Collector))) (App (Val (GoInstruction (GoZeroVal model.Collector))) (Val #())))
  (App (App (Val (slice.forRange model.Collector)) (Var "$range"))
  (Lam "$key"
  (Lam "$value"
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (Let "$a0" (App (Val (GoInstruction (GoLoad model.Collector))) (Var "c"))
  (App (App (Val (GoInstruction (FuncResolve model.Register []))) (Val #())) (Var "$a0")))
  (Let "err" (App (Val (GoInstruction (GoAlloc go.error))) (App (Val (GoInstruction (GoZeroVal go.error))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.error))) (Pair (App (Val (GoInstruction (GoLoad go.error))) (Var "err")) (App (Val (GoInstruction (Convert go.untypedNil go.error))) (Val UntypedNil))))))
  (App (Val doExecute)
  (Let "$a0" (App (Val (GoInstruction (Convert go.error (go.GoType.InterfaceType [])))) (App (Val (GoInstruction (GoLoad go.error))) (Var "err")))
  (App (App (Val (GoInstruction (FuncResolve go.panic []))) (Val #())) (Var "$a0"))))
  (App (Val doExecute)
  (Val #())))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.error))) (Pair (Var "err") (Var "$r0")))))))))
  (App (Val doExecute)
  (Var "$key")))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore model.Collector))) (Pair (Var "c") (Var "$value"))))))))))))
  (Val #())))

end

end github_com.prometheus.client_golang.prometheus
end Perennial
