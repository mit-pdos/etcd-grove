/-
Program start's rights (decision D19d, 2026-10-18): the right to register each of some metric
names with prometheus's default registry (`prometheus.nameFree`, D16) and to listen on each of
some network addresses (`netAddrFree`, item 4). Both are abstract exclusive resources the
program's specs consume (`MustRegister.spec`, `Listen.spec`) and that nothing in the logic
produces: in Go they hold because the program starts with an empty registry (but for what its
unverified code registers) and owns its addresses, a fact of the initial world. Perennial's
adequacy theorem gives a proof only the FFI's start resources, the package-state map and the main
thread's token, and no FFI here models the registry or the network, so the rights cannot be
allocated in the logic. A hypothesis `⊢ |==> nameFree n` of a closed theorem could be used twice
(and two registrations of one name would then not panic: false of Go, the theorem vacuous,
D19a).

**The trust boundary: `goose_adequacy_start`.** Perennial's `goose_adequacy`, whose WP proof
also receives, once, `nameFree n` for each name of `Ns` and `netAddrFree a` for each address of
`As` (distinct), for a program `e` of which `namesUnclaimed e Ns` and `addrsUnclaimed e As` hold.
Why it is true of Go: in a run of `e`, every registration of a name of `Ns` and every listen on
an address of `As` is made by code whose spec consumes the right (`namesUnclaimed`,
`addrsUnclaimed`: nothing else registers or binds them), each right exists once in the proof (the
premise receives one of each), and each consumption is one registration (one listen); so no name
of `Ns` is registered twice and no address of `As` bound twice, which is what `MustRegister`'s and
`Listen`'s specs need. The rest is `goose_adequacy`.

(D39a, 2026-10-23) It also receives `httpProtoFree a` for each address of `As`: a purely ghost
right, the only source of an address's HTTP protocol (`http.reserve`), so each address's protocol
is fixed once in a run (the model of `http.register`'s D38c: a global ghost map from addresses to
saved protocols, now set by `reserve`). No Go operation is involved: nothing to check of `e`.
Why it is once only: nothing else produces `nameFree`, `netAddrFree` or `httpProtoFree` (axiomatized
predicates, `Registry.lean`, `InvNet.lean`; no axiom or definition gives one), so the rights exist
only where this axiom's premise hands them out: once, to the one WP proof of one execution, under
the ghost state `goose_init` allocates for it. The axiom is about executions (its conclusion is
`goose_adequacy`'s), not an entailment: it cannot be applied inside a proof to obtain rights.

Satisfiable whatever the semantics: with `nameFree`, `netAddrFree` and `httpProtoFree` read as `True` (no axiom
says either is exclusive) and the names-only `MustRegister` and `Listen` as diverging functions,
the premise is `goose_adequacy`'s premise and the conclusion its conclusion.

`namesUnclaimed` and `addrsUnclaimed` are axiomatized propositions (facts of the Go program and of
its environment that the model cannot state, hypotheses of a closed theorem: pure, D19a); the
adequacy example's are checked from the Go source (`notes/decisions.md`, D19d).

A design choice D19d leaves to the user: the alternative is an FFI whose initial world holds the
free addresses and the empty registry (`ffiGlobalStart` the rights, `nameFree`/`netAddrFree` its
ghost state, `MustRegister`/`Listen` its operations), a Perennial change proposed in
`notes/decisions.md`, D19d; with it this axiom goes.
-/
module

public import Perennial.GooseLang.Adequacy
public import Proof.github_com.prometheus.client_golang.prometheus.Registry
public import Proof.net.InvNet

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Language.Notation

/-- **The names `Ns` are the verified code's to register** (a fact of the Go program `e`
translates, checked from its source): no collector the default registry holds at start
(client_golang's `go_*` and `process_*`), and no code of the program whose behaviour this
repository does not verify (an untranslated initializer, a names-only function, the runtime),
registers with prometheus's default registry a collector with a descriptor named `n ∈ Ns`, or
with `n`'s label-free descriptor's ID, or with that collector ID. -/
axiom prometheus.namesUnclaimed [FfiSyntax] (e : Expr) (Ns : List GoString) : Prop

/-- **The addresses `As` are the program's** (a fact of the environment a run of `e` is in, and
of `e`'s unverified code): while `e` runs, no other process binds an address of `As`, and no code
of `e` whose behaviour this repository does not verify binds one. -/
axiom addrsUnclaimed [FfiSyntax] (e : Expr) (As : List GoString) : Prop

/-- The rights program start gives: the right to register each name of `Ns` and to listen on
each address of `As`, and (D39a, 2026-10-23) to fix each address's HTTP protocol
(`httpProtoFree`). -/
def startRights {GF : BundledGFunctors} [FfiSyntax] (Ns As : List GoString) : IProp GF :=
  iprop(([∗list] n ∈ Ns, prometheus.nameFree n) ∗ ([∗list] a ∈ As, netAddrFree a) ∗
    ([∗list] a ∈ As, httpProtoFree a))

section adequacy
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiInterpAdequacy ffi]
variable [FfiSemantics ext ffi] [GoGlobalContext]
variable {GF : BundledGFunctors}

/-- **The trust boundary: program start owns the free names and addresses, once** (see the file
header). `goose_adequacy`, with the WP proof also given `startRights Ns As`. -/
axiom goose_adequacy_start [hPre : GooseGpreS ffi GF] (N T : Nat)
    (e : Expr) (σ : state) (g : GlobalState) (φ : val → Prop) (hφ : ∀ p, ¬ φ (PanicV p))
    (Hinitg : ffi_initgP g.globalWorld) (Hinit : ffi_initP σ.world g.globalWorld)
    (Ns As : List GoString) (hNs : Ns.Nodup) (hAs : As.Nodup)
    (hNsFree : prometheus.namesUnclaimed e Ns) (hAsFree : addrsUnclaimed e As)
    (Hwp : ∀ [hG : HeapGS .hasLC GF],
      receiptBound GF = N →
      threadBound GF = T →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ ffiGlobalStart (gooseFfiGlobalGS (ffi := ffi) (GF := GF)) g.globalWorld -∗
        ffiLocalStart (gooseFfiLocalGS (ffi := ffi) (GF := GF)) σ.world -∗
        ownGoState σ.goState.packageState -∗ threadTok -∗ startRights (GF := GF) Ns As ={⊤}=∗
        WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }})
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([e], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hbound : n < N) (Hthreads : g.threads = 1)
    (Hlive : RealThreadsBelow T n ([e], ((σ, g) : CfgState))) :
    (∀ v t2', t2 = Val v :: t2' → φ v) ∧ (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2)

end adequacy

end EtcdGrove
end Perennial
