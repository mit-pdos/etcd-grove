/-
**Test only** (the NON-VACUITY rule, 2026-11-24; kitgen's `NonVacuityLinked.lean` name): every
hypothesis-class premise of craq's statement
(`Dsverify/Spec/github_com/despreston/go_craq/examples/craqnet/TopLevelRobustness.lean`) has an
instance, built as a `theorem` (no `instance` of an `InitHyp` anywhere: etc/dsv/README.md), at every
machine's heap and with one `RpcHttpServe` (`local_rpcHttpServe`) for the boot premises:
* `net.rpc.InitHyp`, `net.http.InitHyp`: **local axioms** (`local_rpc_wp_init`, `local_http_wp_init`):
  the packages' initializers run and establish their facts (`True`) and their imports' facts. Net has
  no initializer proof for them (net/http's closure reaches untranslated initializers), and
  etc/dsv/tools/inithyp-instances.py (math-rand-isinit) walks only a kit's own packages;
* `LogHyp`: **local axioms** for its three fields (`log.Default`, `*Logger.Printf`/`Println`: names
  only in Perennial's trusted `log` model), each the class's own statement, argued of Go's `log` in
  `Craq/LogHyp.lean`;
* `RpcHttpServe` (net/http's `DefaultServeMux`, `rpc.HandleHTTP`, `http.ListenAndServe`): the mux
  predicates are **local opaque constants** (`local_muxOwner`, `local_muxHas`, the latter persistent
  by a local axiom), the two specs **local axioms**, argued of Go's net/http in `Craq/HttpRpc.lean`;
  `rpc.RegisterName` is no longer a field (Net's `net.rpc.RegisterName.wp`);
* the eleven `RpcBoot`s: **local axioms**, one per command, each the premise's own statement for
  `local_rpcHttpServe`.
No field is unsatisfiable: each axiom is a Go library behaviour (or Go's initialization), stated as
the premise states it. No statement or proof imports this module: its local axioms are in no trust
base.
-/
module

public import Dsverify.Spec.github_com.despreston.go_craq.examples.craqnet.TopLevelRobustness

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace github_com.despreston.go_craq.examples.craqnet.instances

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.despreston.go_craq github_com.despreston.go_craq.examples.craqnet

/-! ### The initializers and `log` -/

section inits
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [sem : go.Semantics]

/-- **Local axiom (test-only)**: net/rpc's initializer runs (Go runs it at program start; it
allocates `DefaultServer` and the codec registry, after its imports') and establishes its fact. -/
axiom local_rpc_wp_init : ∀ (get_is_pkg_init : GoString → IProp GF),
  GetIsPkgInitProp pkg_id.net.rpc get_is_pkg_init →
  {{ ownInitializing get_is_pkg_init }} (App (Val net.rpc.initialize') (Val #()))
  {{ RET #(); ownInitializing get_is_pkg_init ∗ isPkgInit (PROP := IProp GF) pkg_id.net.rpc }}

theorem rpcInitHyp_holds : net.rpc.InitHyp GF := ⟨local_rpc_wp_init⟩

/-- **Local axiom (test-only)**: net/http's initializer runs (Go runs it at program start) and
establishes its fact. -/
axiom local_http_wp_init : ∀ (get_is_pkg_init : GoString → IProp GF),
  GetIsPkgInitProp pkg_id.net.http get_is_pkg_init →
  {{ ownInitializing get_is_pkg_init }} (App (Val net.http.initialize') (Val #()))
  {{ RET #(); ownInitializing get_is_pkg_init ∗ isPkgInit (PROP := IProp GF) pkg_id.net.http }}

theorem httpInitHyp_holds : net.http.InitHyp GF := ⟨local_http_wp_init⟩

variable [log.Assumptions]

/-- **Local axiom (test-only)**: `log.Default()` returns the standard logger (`std`, allocated by
`log`'s initializer; never nil). -/
axiom local_log_Default :
  {{ isPkgInit (PROP := IProp GF) pkg_id.log }}
    (App (Val (@! log.Default)) (Val #()))
  {{ (l : Loc), RET #l; ⌜l ≠ null⌝ }}

/-- **Local axiom (test-only)**: `l.Printf(format, args...)` on a non-nil `*Logger` returns
(`Logger` is safe for concurrent use; `fmt` formats `argOk` arguments, recovering a panicking
`Error()`), the argument slice kept. -/
axiom local_log_Printf : ∀ (l : Loc) (msg : GoString) (arg : GoSlice) (xs : List GoInterface)
    (dq : DFrac), l ≠ null →
  {{ isPkgInit (PROP := IProp GF) pkg_id.log ∗ arg ↦*{dq} xs ∗ [∗list] x ∈ xs, argOk x }}
    (App (App (Val (l @!! go.GoType.PointerType log.Logger.ty @!! go!"Printf")) (Val #msg))
      (Val #arg))
  {{ RET #(); arg ↦*{dq} xs }}

/-- **Local axiom (test-only)**: `l.Println(args...)` on a non-nil `*Logger` returns, as
`Printf`. -/
axiom local_log_Println : ∀ (l : Loc) (arg : GoSlice) (xs : List GoInterface) (dq : DFrac),
    l ≠ null →
  {{ isPkgInit (PROP := IProp GF) pkg_id.log ∗ arg ↦*{dq} xs ∗ [∗list] x ∈ xs, argOk x }}
    (App (Val (l @!! go.GoType.PointerType log.Logger.ty @!! go!"Println")) (Val #arg))
  {{ RET #(); arg ↦*{dq} xs }}

theorem logHyp_holds : LogHyp GF := ⟨local_log_Default, local_log_Printf, local_log_Println⟩

end inits

/-! ### net/rpc over HTTP's server side -/

section serve
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]

/-- **Local opaque constant (test-only)**: the right to register paths at `DefaultServeMux`, those
registered `R` (its `m` map's keys, exclusively owned). -/
axiom local_muxOwner : List GoString → IProp GF

/-- **Local opaque constant (test-only)**: `DefaultServeMux` routes `path` to a handler serving `W`
at the addresses `A` (persistent: a registered path is never removed). -/
axiom local_muxHas : net.rpc.RpcWorld GF → (GoString → Prop) → GoString → IProp GF

/-- **Local axiom (test-only)**: the routing fact is persistent. -/
axiom local_muxHas_persistent : ∀ W A path, Persistent (local_muxHas (GF := GF) W A path)

/-- **Local axiom (test-only)**: `rpc.HandleHTTP()` (`HttpRpc.lean`'s `RpcHttpServe.HandleHTTP`). -/
axiom local_HandleHTTP : ∀ (γs : GName) (C : net.rpc.CodecSpec GF) (W : net.rpc.RpcWorld GF)
    (A : GoString → Prop) (R : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗ ⌜threadBound GF ≤ 2 ^ 31⌝ ∗
      local_muxOwner R ∗ ⌜net.rpc.defaultRPCPath ∉ R ∧ go!"/debug/rpc" ∉ R⌝ ∗
      net.rpc.defaultServer γs ∗ (□ ∀ a, ⌜A a⌝ → net.rpc.srvServes γs C W a) ∗ net.rpc.srvEnv ∗
      net.rpc.codecSet C ∗ globalAddr net.rpc.connected ↦□ net.rpc.connectedStatus }}
    (App (Val (@! net.rpc.HandleHTTP)) (Val #()))
  {{ RET #(); local_muxOwner (go!"/debug/rpc" :: net.rpc.defaultRPCPath :: R) ∗
      local_muxHas W A net.rpc.defaultRPCPath }}

/-- **Local axiom (test-only)**: `http.ListenAndServe(a, nil)` (`HttpRpc.lean`'s
`RpcHttpServe.ListenAndServe`). -/
axiom local_ListenAndServe : ∀ (W : net.rpc.RpcWorld GF) (A : GoString → Prop) (a : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.http ∗ ⌜threadBound GF ≤ 2 ^ 31⌝ ∗
      ⌜addrOk a = true ∧ A a⌝ ∗ httpRpcAddr W a ∗ local_muxHas W A net.rpc.defaultRPCPath }}
    (App (App (Val (@! net.http.ListenAndServe)) (Val #a)) (Val #interface.nil))
  {{ (err : GoInterface), RET #err; True }}

/-- **The instance** (a `def`: `RpcHttpServe` carries data, the mux predicates). -/
def local_rpcHttpServe : RpcHttpServe GF :=
  ⟨local_muxOwner, local_muxHas, local_muxHas_persistent, local_HandleHTTP, local_ListenAndServe⟩

end serve

/-! ### The machines' boots -/

section boots
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem' : github_com.despreston.go_craq.examples.craqnet.Assumptions]
variable [store.Assumptions] [store.kv.Assumptions] [transport.Assumptions]
variable [transport.netrpc.Assumptions] [node.Assumptions] [coordinator.Assumptions]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]
variable [cmd.client0.Assumptions] [cmd.client1.Assumptions] [cmd.client2.Assumptions]
variable [cmd.client3.Assumptions] [cmd.client4.Assumptions] [cmd.server1.Assumptions]
variable [cmd.server2.Assumptions] [cmd.server3.Assumptions] [cmd.server4.Assumptions]
variable [cmd.server5.Assumptions] [cmd.server6.Assumptions]

/-- **Local axiom (test-only)**: command `client0`'s initializer, run once from the machine's empty
package state, initializes the program and leaves net/rpc's and net/http's initial state
(`rpcBootRes`). -/
axiom local_boot_client0 [rs : RpcHttpServe GF] :
  RpcBoot (GF := GF) cmd.client0.initialize' pkg_id.github_com.despreston.go_craq.examples.craqnet.cmd.client0
/-- **Local axiom (test-only)**: command `client1`'s initializer, run once from the machine's empty
package state, initializes the program and leaves net/rpc's and net/http's initial state
(`rpcBootRes`). -/
axiom local_boot_client1 [rs : RpcHttpServe GF] :
  RpcBoot (GF := GF) cmd.client1.initialize' pkg_id.github_com.despreston.go_craq.examples.craqnet.cmd.client1
/-- **Local axiom (test-only)**: command `client2`'s initializer, run once from the machine's empty
package state, initializes the program and leaves net/rpc's and net/http's initial state
(`rpcBootRes`). -/
axiom local_boot_client2 [rs : RpcHttpServe GF] :
  RpcBoot (GF := GF) cmd.client2.initialize' pkg_id.github_com.despreston.go_craq.examples.craqnet.cmd.client2
/-- **Local axiom (test-only)**: command `client3`'s initializer, run once from the machine's empty
package state, initializes the program and leaves net/rpc's and net/http's initial state
(`rpcBootRes`). -/
axiom local_boot_client3 [rs : RpcHttpServe GF] :
  RpcBoot (GF := GF) cmd.client3.initialize' pkg_id.github_com.despreston.go_craq.examples.craqnet.cmd.client3
/-- **Local axiom (test-only)**: command `client4`'s initializer, run once from the machine's empty
package state, initializes the program and leaves net/rpc's and net/http's initial state
(`rpcBootRes`). -/
axiom local_boot_client4 [rs : RpcHttpServe GF] :
  RpcBoot (GF := GF) cmd.client4.initialize' pkg_id.github_com.despreston.go_craq.examples.craqnet.cmd.client4
/-- **Local axiom (test-only)**: command `server1`'s initializer, run once from the machine's empty
package state, initializes the program and leaves net/rpc's and net/http's initial state
(`rpcBootRes`). -/
axiom local_boot_server1 [rs : RpcHttpServe GF] :
  RpcBoot (GF := GF) cmd.server1.initialize' pkg_id.github_com.despreston.go_craq.examples.craqnet.cmd.server1
/-- **Local axiom (test-only)**: command `server2`'s initializer, run once from the machine's empty
package state, initializes the program and leaves net/rpc's and net/http's initial state
(`rpcBootRes`). -/
axiom local_boot_server2 [rs : RpcHttpServe GF] :
  RpcBoot (GF := GF) cmd.server2.initialize' pkg_id.github_com.despreston.go_craq.examples.craqnet.cmd.server2
/-- **Local axiom (test-only)**: command `server3`'s initializer, run once from the machine's empty
package state, initializes the program and leaves net/rpc's and net/http's initial state
(`rpcBootRes`). -/
axiom local_boot_server3 [rs : RpcHttpServe GF] :
  RpcBoot (GF := GF) cmd.server3.initialize' pkg_id.github_com.despreston.go_craq.examples.craqnet.cmd.server3
/-- **Local axiom (test-only)**: command `server4`'s initializer, run once from the machine's empty
package state, initializes the program and leaves net/rpc's and net/http's initial state
(`rpcBootRes`). -/
axiom local_boot_server4 [rs : RpcHttpServe GF] :
  RpcBoot (GF := GF) cmd.server4.initialize' pkg_id.github_com.despreston.go_craq.examples.craqnet.cmd.server4
/-- **Local axiom (test-only)**: command `server5`'s initializer, run once from the machine's empty
package state, initializes the program and leaves net/rpc's and net/http's initial state
(`rpcBootRes`). -/
axiom local_boot_server5 [rs : RpcHttpServe GF] :
  RpcBoot (GF := GF) cmd.server5.initialize' pkg_id.github_com.despreston.go_craq.examples.craqnet.cmd.server5
/-- **Local axiom (test-only)**: command `server6`'s initializer, run once from the machine's empty
package state, initializes the program and leaves net/rpc's and net/http's initial state
(`rpcBootRes`). -/
axiom local_boot_server6 [rs : RpcHttpServe GF] :
  RpcBoot (GF := GF) cmd.server6.initialize' pkg_id.github_com.despreston.go_craq.examples.craqnet.cmd.server6

end boots

/-! ### At the statement's heaps -/

section statement
open github_com.mit_pdos.etcd_grove.examples.lib.remote.counter (remoteGF)
attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet

/-- **The non-vacuity instance** (the NON-VACUITY rule): craq's hypothesis-class premises, in the
statement's own form (`craq_remote_robust.spec`), with `local_rpcHttpServe` for the boots. -/
theorem nonvacuous_premises :
  ∀ [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
    [orch_sem : cmd.orch.Assumptions]
    [client0_sem : cmd.client0.Assumptions]
    [client1_sem : cmd.client1.Assumptions]
    [client2_sem : cmd.client2.Assumptions]
    [client3_sem : cmd.client3.Assumptions]
    [client4_sem : cmd.client4.Assumptions]
    [server1_sem : cmd.server1.Assumptions]
    [server2_sem : cmd.server2.Assumptions]
    [server3_sem : cmd.server3.Assumptions]
    [server4_sem : cmd.server4.Assumptions]
    [server5_sem : cmd.server5.Assumptions]
    [server6_sem : cmd.server6.Assumptions]
    [field_sem : net.FieldAssumptions] [go.BasicIntoValInj],
    (∀ G L, letI := heapAt G L; net.rpc.InitHyp remoteGF) ∧
    (∀ G L, letI := heapAt G L; net.http.InitHyp remoteGF) ∧
    (∀ G L, letI := heapAt G L; LogHyp remoteGF) ∧
    ∃ (rs : ∀ G L, letI := heapAt G L; ∀ π : NetProtoGS, RpcHttpServe remoteGF),
      (∀ G L, letI := heapAt G L; ∀ π : NetProtoGS, letI := rs G L π;
        RpcBoot (GF := remoteGF) cmd.client0.initialize'
          pkg_id.github_com.despreston.go_craq.examples.craqnet.cmd.client0) ∧
      (∀ G L, letI := heapAt G L; ∀ π : NetProtoGS, letI := rs G L π;
        RpcBoot (GF := remoteGF) cmd.client1.initialize'
          pkg_id.github_com.despreston.go_craq.examples.craqnet.cmd.client1) ∧
      (∀ G L, letI := heapAt G L; ∀ π : NetProtoGS, letI := rs G L π;
        RpcBoot (GF := remoteGF) cmd.client2.initialize'
          pkg_id.github_com.despreston.go_craq.examples.craqnet.cmd.client2) ∧
      (∀ G L, letI := heapAt G L; ∀ π : NetProtoGS, letI := rs G L π;
        RpcBoot (GF := remoteGF) cmd.client3.initialize'
          pkg_id.github_com.despreston.go_craq.examples.craqnet.cmd.client3) ∧
      (∀ G L, letI := heapAt G L; ∀ π : NetProtoGS, letI := rs G L π;
        RpcBoot (GF := remoteGF) cmd.client4.initialize'
          pkg_id.github_com.despreston.go_craq.examples.craqnet.cmd.client4) ∧
      (∀ G L, letI := heapAt G L; ∀ π : NetProtoGS, letI := rs G L π;
        RpcBoot (GF := remoteGF) cmd.server1.initialize'
          pkg_id.github_com.despreston.go_craq.examples.craqnet.cmd.server1) ∧
      (∀ G L, letI := heapAt G L; ∀ π : NetProtoGS, letI := rs G L π;
        RpcBoot (GF := remoteGF) cmd.server2.initialize'
          pkg_id.github_com.despreston.go_craq.examples.craqnet.cmd.server2) ∧
      (∀ G L, letI := heapAt G L; ∀ π : NetProtoGS, letI := rs G L π;
        RpcBoot (GF := remoteGF) cmd.server3.initialize'
          pkg_id.github_com.despreston.go_craq.examples.craqnet.cmd.server3) ∧
      (∀ G L, letI := heapAt G L; ∀ π : NetProtoGS, letI := rs G L π;
        RpcBoot (GF := remoteGF) cmd.server4.initialize'
          pkg_id.github_com.despreston.go_craq.examples.craqnet.cmd.server4) ∧
      (∀ G L, letI := heapAt G L; ∀ π : NetProtoGS, letI := rs G L π;
        RpcBoot (GF := remoteGF) cmd.server5.initialize'
          pkg_id.github_com.despreston.go_craq.examples.craqnet.cmd.server5) ∧
      (∀ G L, letI := heapAt G L; ∀ π : NetProtoGS, letI := rs G L π;
        RpcBoot (GF := remoteGF) cmd.server6.initialize'
          pkg_id.github_com.despreston.go_craq.examples.craqnet.cmd.server6) := by
  intro gctx lctx sem s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 fsem bvi
  refine ⟨fun G L => rpcInitHyp_holds (hG := heapAt G L), fun G L => httpInitHyp_holds (hG := heapAt G L),
    fun G L => logHyp_holds (hG := heapAt G L),
    fun G L π => local_rpcHttpServe (hG := heapAt G L) (π := π),
    fun G L π => local_boot_client0 (hG := heapAt G L) (rs := local_rpcHttpServe),
      fun G L π => local_boot_client1 (hG := heapAt G L) (rs := local_rpcHttpServe),
      fun G L π => local_boot_client2 (hG := heapAt G L) (rs := local_rpcHttpServe),
      fun G L π => local_boot_client3 (hG := heapAt G L) (rs := local_rpcHttpServe),
      fun G L π => local_boot_client4 (hG := heapAt G L) (rs := local_rpcHttpServe),
      fun G L π => local_boot_server1 (hG := heapAt G L) (rs := local_rpcHttpServe),
      fun G L π => local_boot_server2 (hG := heapAt G L) (rs := local_rpcHttpServe),
      fun G L π => local_boot_server3 (hG := heapAt G L) (rs := local_rpcHttpServe),
      fun G L π => local_boot_server4 (hG := heapAt G L) (rs := local_rpcHttpServe),
      fun G L π => local_boot_server5 (hG := heapAt G L) (rs := local_rpcHttpServe),
      fun G L π => local_boot_server6 (hG := heapAt G L) (rs := local_rpcHttpServe)⟩

end statement

end github_com.despreston.go_craq.examples.craqnet.instances
end Perennial
