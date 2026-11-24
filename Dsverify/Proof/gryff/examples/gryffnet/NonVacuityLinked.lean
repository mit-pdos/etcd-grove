/-
**Test only** (the NON-VACUITY rule; dsv-gryff, 2026-11-24; the convention of `etc/dsv/README.md`,
the examples of math-rand-isinit's rabia and QuePaxa modules): every hypothesis-class premise of
`gryff_remote_robust.spec` (`Dsverify/Spec/gryff/examples/gryffnet/TopLevelRobustness.lean`) has an
instance, built as a `theorem` or a `def` (no `instance` of an `InitHyp` anywhere):
* `net.rpc.InitHyp`, `net.http.InitHyp`: their initializers' walks
  (`Dsverify/Proof/net/{rpc,http}/InitInstancesLinked.lean`, over the walks of the packages their
  initializers reach that the kit's part has no `Init` of: `go/token`, `mime/multipart`,
  `net/http/internal/ascii`, `net/textproto`, `net/url`, `crypto/tls`, httpguts, `runtime`,
  `internal/runtime/{atomic,sys}`), over **local axioms** for their names-only variable initializers
  and `init` functions (`localOpaqueInitsOk`, `localInitFuncsOk`), and Net's proved `NewServer`;
* `math.rand.InitHyp`: proved here, the main tree's walk (`Proof/math/rand/Init.lean`, over Perennial's
  `sync`/`sync/atomic` initializers) restated on `Net/`'s `PkgInitExt`. No axiom. (Not discharged
  in the statement: the shared class `Dsverify/Proof/math/rand/Init.lean` is being replaced by
  math-rand-isinit, which makes `math/rand` Perennial's; gryff drops the premise when that lands.)
* `wire.BinaryVarintHyps`: `errOverflowVar` proved (Perennial's `encoding.binary.errOverflow_of_init`);
  the four varint functions **local axioms** (each the class's field). Perennial b3f2fc485 translates
  and proves them (`Perennial/Proof/encoding/binary/{Read,Put}{U,}varint.lean`, perennial#689) over
  an `io.ByteReader` contract; deriving the fields over dsv-bufio's reader is the remaining step.
* `netN.StringsIndexHyp`, `replica2.SortSliceHyp`, `lib.RandSeedHyp`: **local axioms** (`strings.Index`,
  `sort.Slice`, `math/rand.Seed` are names only at the pin).
* `lib.MathPowHyp`: the main tree's interim axiom `EtcdGrove.math.Pow.wp_proof`.
* `RpcHttpHyp` (data: a `def`, `rpcHttpHyp`, over `netRpcHttpAddr`): its predicates opaque
  (`handlerOk`, `muxHas` persistent by a `□`; `muxFree`, `srvFresh` exclusive), its specs **local
  axioms** (net/http's server and net/rpc's `HandleHTTP` are not proved in Net yet), `DialHTTP_spec`
  Net's `net.rpc.DialHTTP.wp` over **local axioms** for Perennial's names-only `strings.Cut` and
  `strings.TrimLeft` (the main tree's specs; their bodies come with Perennial ed1955557).
* `RpcBootHyp`: **local axioms** (net/rpc's and net/http's owned initializations: no proof yet).
Each local axiom states the class's field as it is (its truth argument: the field's docstring in
the class's file, and notes/dsv-gryff.md, "Non-vacuity"). No statement or proof imports this
module: its local axioms are in no trust base.
-/
module

public import Dsverify.Spec.gryff.examples.gryffnet.TopLevelRobustness
public import Dsverify.Proof.net.rpc.InitInstancesLinked
public import Dsverify.Proof.net.http.InitInstancesLinked
public import Perennial.Proof.sync.Link
public import Perennial.Proof.sync.atomic.Link
public import Perennial.Proof.encoding.binary.Base
public import Proof.math.Pow
public import Net.Proof.net.rpc.Results

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace gryff.examples.gryffnet.instances

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Perennial.gryff Perennial.net.rpc

attribute [local instance] GooseGlobalGS.gooseInvGS

/-! ### `math.rand.InitHyp`: the main tree's walk, on `Net/`'s `PkgInitExt` -/

section mrand
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [_root_.Perennial.math.rand.Assumptions]

theorem mrand_wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.math.rand get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val math.rand.initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.math.rand }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := _) math.rand.globalRandGenerator _ as HglobalRandGenerator
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.sync.atomic _root_.Perennial.sync.atomic.initialize'
      EtcdGrove.ExternalInit.sync_atomic _root_.Perennial.sync.atomic.wp_initialize' _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.sync _root_.Perennial.sync.initialize'
      EtcdGrove.ExternalInit.sync _root_.Perennial.sync.wp_initialize' _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  iframe Hown
  is_pkg_init_finish

theorem mrand_initHyp_holds : math.rand.InitHyp GF :=
  ⟨fun g Hinit => EtcdGrove.wp_init_of_lb _ _ _ (mrand_wp_initialize'_lb g Hinit)⟩

end mrand

/-! ### The library hypotheses: local axioms (and the main tree's `math.Pow`) -/

section libs
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

open Perennial.gryff.wire in
/-- **Local axiom (test-only)**: `binary.ReadUvarint` on a `*bufio.Reader` (`BinaryVarintHyps.readUvarint`). -/
axiom local_readUvarint : ∀ (br : Loc) (rd : RSt GF) (I : List w8 → IProp GF) (R : List w8),
    {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.binary ∗
          isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
          readerOk rd I ∗ readNext br rd I R vok ∗ ownReader br rd I R }}
        (App (Val (@! encoding.binary.ReadUvarint))
          (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
      {{ (x : w64) (err : GoInterface), RET (PairV #x #err); ∃ V : List w8,
          ownReader br rd I (R ++ V) ∗
          ((⌜err = interface.nil ∧ V = uvarintEnc (uint.nat x)⌝) ∨
           rdErr rd err) }}

open Perennial.gryff.wire in
/-- **Local axiom (test-only)**: `binary.ReadVarint` (`BinaryVarintHyps.readVarint`). -/
axiom local_readVarint : ∀ (br : Loc) (rd : RSt GF) (I : List w8 → IProp GF) (R : List w8),
    {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.binary ∗
          isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
          readerOk rd I ∗ readNext br rd I R vok ∗ ownReader br rd I R }}
        (App (Val (@! encoding.binary.ReadVarint))
          (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
      {{ (x : w64) (err : GoInterface), RET (PairV #x #err); ∃ V : List w8,
          ownReader br rd I (R ++ V) ∗
          ((⌜err = interface.nil ∧ ∃ ux : w64, V = uvarintEnc (uint.nat ux) ∧
              x = (if ux &&& W64 1 = W64 0 then ux >>> W64 1 else ~~~ (ux >>> W64 1))⌝) ∨
           rdErr rd err) }}

open Perennial.gryff.wire in
/-- **Local axiom (test-only)**: `binary.PutUvarint` (`BinaryVarintHyps.putUvarint`). -/
axiom local_putUvarint : ∀ (p : Loc) (n : w64) (vs : List w8) (x : w64)
    (hn : (uvarintEnc (uint.nat x)).length ≤ sint.nat n),
    {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.binary ∗
          typedPointsto p (array.mk (sint.Z n) vs) (DFrac.own 1) }}
        (App (App (Val (@! encoding.binary.PutUvarint)) (Val #(slice.mk p n n))) (Val #x))
      {{ RET #(W64 (uvarintEnc (uint.nat x)).length);
          typedPointsto p (array.mk (sint.Z n)
            (uvarintEnc (uint.nat x) ++ vs.drop (uvarintEnc (uint.nat x)).length)) (DFrac.own 1) }}

open Perennial.gryff.wire in
/-- **Local axiom (test-only)**: `binary.PutVarint` (`BinaryVarintHyps.putVarint`). -/
axiom local_putVarint : ∀ (p : Loc) (n : w64) (nI : Int) (vs : List w8) (x : w64) (hnI : sint.Z n = nI)
    (hx : 0 ≤ sint.Z x) (hn : (varintEnc (sint.Z x)).length ≤ sint.nat n),
    {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.binary ∗
          typedPointsto p (array.mk nI vs) (DFrac.own 1) }}
        (App (App (Val (@! encoding.binary.PutVarint)) (Val #(slice.mk p n n))) (Val #x))
      {{ RET #(W64 (varintEnc (sint.Z x)).length);
          typedPointsto p (array.mk nI
            (varintEnc (sint.Z x) ++ vs.drop (varintEnc (sint.Z x)).length)) (DFrac.own 1) }}

theorem binaryVarint_holds : wire.BinaryVarintHyps GF :=
  ⟨local_readUvarint, local_readVarint, local_putUvarint, local_putVarint,
    encoding.binary.errOverflow_of_init⟩

/-- **Local axiom (test-only)**: `strings.Index(s, string(c))` is the index of `c`'s first
occurrence in `s`, or `-1` (`StringsIndexHyp.index`). -/
axiom local_strings_Index : ∀ (s : GoString) (c : w8),
    {{ (True : IProp GF) }}
      (App (App (Val (@! _root_.Perennial.strings.Index')) (Val #s)) (Val #([c] : GoString)))
    {{ RET #(W64 (netN.indexOfByte s c)); True }}

theorem stringsIndex_holds : netN.StringsIndexHyp GF := ⟨local_strings_Index⟩

/-- **Local axiom (test-only)**: `sort.Slice` on a `[]int32` with a `<` comparison sorts it
(`SortSliceHyp.slice`). -/
axiom local_sort_Slice : ∀ (sl : GoSlice) (xs : List w32) (less : GoFunc) (F : IProp GF),
    {{ sl ↦* xs ∗ F ∗ replica2.lessOk sl F less }}
      (App (App (Val (@! sort.Slice')) (Val #(interface.mkOk (go.SliceType go.int32) #sl)))
        (Val #less))
    {{ RET #(); sl ↦* xs.mergeSort (fun a b => Perennial.gryff.model.sle a b) ∗ F }}

theorem sortSlice_holds : replica2.SortSliceHyp GF := ⟨local_sort_Slice⟩

theorem mathPow_holds : lib.MathPowHyp GF := ⟨EtcdGrove.math.Pow.wp_proof⟩

/-- **Local axiom (test-only)**: `rand.Seed(seed)` returns (`RandSeedHyp.seed`). -/
axiom local_rand_Seed : _root_.Perennial.math.rand.Seed.spec (GF := GF) (hG := hG)

theorem randSeed_holds : lib.RandSeedHyp GF := ⟨local_rand_Seed⟩

/-- **Local axiom (test-only)**: Perennial's `strings.Cut` (names only at b3f2fc485; the main
tree's spec). -/
axiom local_strings_Cut : EtcdGrove.strings.Cut.spec (GF := GF) (hG := hG)

/-- **Local axiom (test-only)**: Perennial's `strings.TrimLeft` on an ASCII cut set (names only at
b3f2fc485; the main tree's spec). -/
axiom local_strings_TrimLeft : EtcdGrove.strings.TrimLeft.spec (GF := GF) (hG := hG)

end libs

/-! ### `RpcHttpHyp` and `RpcBootHyp` -/

section rpc
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]

/-- Real net/http's handler predicate (opaque). -/
opaque handlerOk0 : RpcWorld GF → (GoString → Prop) → GoString → GoInterface → IProp GF :=
  fun _ _ _ _ => iprop(True)
/-- Real `DefaultServeMux`'s routes (opaque). -/
opaque muxHas0 : RpcWorld GF → (GoString → Prop) → GoString → IProp GF := fun _ _ _ => iprop(True)
/-- No handler at a path of `DefaultServeMux` yet (opaque; exclusive). -/
opaque muxFree0 : GoString → IProp GF := fun _ => iprop(True)
/-- A server's empty service map (opaque; exclusive). -/
opaque srvFresh0 : GName → IProp GF := fun _ => iprop(True)

/-- A handler of `path` serving `W` at `A` (persistent). -/
def handlerOk' (W : RpcWorld GF) (A : GoString → Prop) (path : GoString) (h : GoInterface) :
    IProp GF := iprop(□ handlerOk0 W A path h)
/-- `DefaultServeMux` routes `path` (persistent). -/
def muxHas' (W : RpcWorld GF) (A : GoString → Prop) (path : GoString) : IProp GF :=
  iprop(□ muxHas0 W A path)

/-- **Local axiom (test-only)**: `RpcHttpHyp.Server_ServeHTTP_spec`. -/
axiom local_Server_ServeHTTP : ∀ (s : Loc) (γs : GName) (C : CodecSpec GF) (W : RpcWorld GF)
    (A : GoString → Prop) (path : GoString),
  ⌜threadBound GF ≤ 2 ^ 31⌝ ∗ isServer s γs ∗ (□ ∀ a, ⌜A a⌝ → srvServes γs C W a) ∗ srvEnv ∗
      codecSet C ⊢
    handlerOk' W A path (interface.mkOk (go.GoType.PointerType net.rpc.Server.ty) #s)

/-- **Local axiom (test-only)**: `RpcHttpHyp.Server_HandleHTTP_spec`. -/
axiom local_Server_HandleHTTP : ∀ (s : Loc) (γs : GName) (C : CodecSpec GF) (W : RpcWorld GF)
    (A : GoString → Prop) (debugPath : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗ ⌜threadBound GF ≤ 2 ^ 31⌝ ∗
      muxFree0 defaultRPCPath ∗
      isServer s γs ∗ (□ ∀ a, ⌜A a⌝ → srvServes γs C W a) ∗ srvEnv ∗ codecSet C }}
    (App (App (Val (s @!! go.GoType.PointerType net.rpc.Server.ty @!! go!"HandleHTTP"))
      (Val #defaultRPCPath)) (Val #debugPath))
  {{ RET #(); muxHas' W A defaultRPCPath }}

/-- **Local axiom (test-only)**: `RpcHttpHyp.HandleHTTP_spec`. -/
axiom local_HandleHTTP : ∀ (γs : GName) (C : CodecSpec GF) (W : RpcWorld GF) (A : GoString → Prop),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗ ⌜threadBound GF ≤ 2 ^ 31⌝ ∗
      muxFree0 defaultRPCPath ∗
      defaultServer γs ∗ (□ ∀ a, ⌜A a⌝ → srvServes γs C W a) ∗ srvEnv ∗ codecSet C }}
    (App (Val (@! net.rpc.HandleHTTP)) (Val #()))
  {{ RET #(); muxHas' W A defaultRPCPath }}

/-- **Local axiom (test-only)**: `RpcHttpHyp.NewServer_fresh_spec`. -/
axiom local_NewServer_fresh :
  {{ isPkgInit (PROP := IProp GF) pkg_id.sync }}
    (App (Val (@! net.rpc.NewServer)) (Val #()))
  {{ (s : Loc), RET #s; ∃ γ : GName, isServer s γ ∗ srvFresh0 γ }}

/-- **Local axiom (test-only)**: `RpcHttpHyp.Server_Register_fresh_spec`. -/
axiom local_Server_Register_fresh : ∀ (s : Loc) (γ : GName) (C : CodecSpec GF) (rcvr : GoInterface)
    (S : MethodSpec GF) (nm : GoString) (c : w8) (rest : GoString),
  nm = c :: rest → uint.Z (W8 0x41) ≤ uint.Z c ∧ uint.Z c ≤ uint.Z (W8 0x5A) →
  {{ isServer s γ ∗ srvFresh0 γ ∗ codecSet C ∗ C.rcv rcvr (rcvrIs C rcvr S nm false) }}
    (App (Val (s @!! go.GoType.PointerType net.rpc.Server.ty @!! go!"Register")) (Val #rcvr))
  {{ (err : GoInterface), RET #err; ⌜err = interface.nil⌝ ∗ svcReg γ C nm S }}

/-- **Local axiom (test-only)**: `RpcHttpHyp.ServeMux_ServeHTTP_spec`. -/
axiom local_ServeMux_ServeHTTP : ∀ (W : RpcWorld GF) (A : GoString → Prop) (path : GoString),
  muxHas' W A path ⊢
    handlerOk' W A path (interface.mkOk (go.GoType.PointerType net.http.ServeMux.ty)
      #(globalAddr net.http.DefaultServeMux))

/-- **Local axiom (test-only)**: `RpcHttpHyp.Serve_spec`, over Net's listener protocols. -/
axiom local_Serve : ∀ (W : RpcWorld GF) (la path : GoString) (lis : GoInterface) (l : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.http ∗ ⌜threadBound GF ≤ 2 ^ 31⌝ ∗
      net.rpc.rpcLisP (Gg := hG.goose_globalGS) W la (connectReq path) connectAns ∗
      muxHas' W (lisAccepts la) path ∗
      net.isListener (GF := GF) lis l ∗ netLisOn (extLocalGS netExt (L := hG.goose_localGS)) l la ∗
      lisInv (Gg := hG.goose_globalGS) (extLocalGS netExt (L := hG.goose_localGS)) l la }}
    (App (App (Val (@! net.http.Serve)) (Val #lis)) (Val #interface.nil))
  {{ (err : GoInterface), RET #err; True }}

variable [net.Assumptions] [go.BasicIntoValInj] [sync.Assumptions] [errors.Assumptions]
  [_root_.Perennial.bufio.Assumptions]

/-- **`RpcHttpHyp`'s instance** (a `def`: the class carries data), over Net's listener protocols. -/
def rpcHttpHyp : RpcHttpHyp GF (π := π) (RA := netRpcHttpAddr GF (Gg := hG.goose_globalGS)) where
  handlerOk := handlerOk'
  handlerOk_persistent := fun _ _ _ _ => by unfold handlerOk'; infer_instance
  muxHas := muxHas'
  muxHas_persistent := fun _ _ _ => by unfold muxHas'; infer_instance
  Server_ServeHTTP_spec := local_Server_ServeHTTP
  muxFree := muxFree0
  Server_HandleHTTP_spec := local_Server_HandleHTTP
  HandleHTTP_spec := local_HandleHTTP
  DialHTTP_spec := net.rpc.DialHTTP.wp local_strings_Cut local_strings_TrimLeft
  srvFresh := srvFresh0
  NewServer_fresh_spec := local_NewServer_fresh
  Server_Register_fresh_spec := local_Server_Register_fresh
  ServeMux_ServeHTTP_spec := local_ServeMux_ServeHTTP
  Serve_spec := local_Serve

/-- **Local axiom (test-only)**: `RpcBootHyp.wp_init_own` (net/rpc's owned initialization). -/
axiom local_rpc_init_own : ∀ (g : GoString → IProp GF), GetIsPkgInitProp pkg_id.net.rpc g →
  {{ ownInitializing (gNoPkg pkg_id.net.rpc g) }} (App (Val net.rpc.initialize') (Val #()))
  {{ RET #(); ownInitializing g ∗ isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗
      rpcInitRes (GF := GF) (RA := netRpcHttpAddr GF (Gg := hG.goose_globalGS)) }}

/-- **Local axiom (test-only)**: `RpcBootHyp.wp_http_own` (net/http's owned initialization). -/
axiom local_http_init_own : ∀ (g : GoString → IProp GF), GetIsPkgInitProp pkg_id.net.http g →
  {{ ownInitializing (gNoPkg pkg_id.net.http g) }} (App (Val net.http.initialize') (Val #()))
  {{ RET #(); ownInitializing g ∗ isPkgInit (PROP := IProp GF) pkg_id.net.http ∗
      muxFree0 defaultRPCPath ∗ net.http.httpEnv }}

theorem rpcBootHyp_holds :
    RpcBootHyp GF (π := π) (RA := netRpcHttpAddr GF (Gg := hG.goose_globalGS)) (H := rpcHttpHyp) :=
  ⟨local_rpc_init_own, local_http_init_own⟩

end rpc

/-! ### At the statement's heaps -/

section statement
open github_com.mit_pdos.etcd_grove.examples.lib.remote.counter (remoteGF)
attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet
variable [GoGlobalContext] [lctx : GoLocalContext] [go.Semantics]
variable [cmd.server1.Assumptions]
variable [net.FieldAssumptions] [go.BasicIntoValInj] [net.rpc.Assumptions]

/-- **The non-vacuity instance** (the NON-VACUITY rule): `gryff_remote_robust.spec`'s
hypothesis-class premises, in the statement's own form (each at `remoteGF` and every machine's
heap `heapAt G L`; `RpcHttpHyp` and `RpcBootHyp` also at every `NetProtoGS`), hold together. -/
theorem nonvacuous_premises :
    (∀ G L, letI := heapAt G L; net.rpc.InitHyp remoteGF) ∧
    (∀ G L, letI := heapAt G L; net.http.InitHyp remoteGF) ∧
    (∀ G L, letI := heapAt G L; math.rand.InitHyp remoteGF) ∧
    (∀ G L, letI := heapAt G L; wire.BinaryVarintHyps remoteGF) ∧
    (∀ G L, letI := heapAt G L; netN.StringsIndexHyp remoteGF) ∧
    (∀ G L, letI := heapAt G L; replica2.SortSliceHyp remoteGF) ∧
    (∀ G L, letI := heapAt G L; lib.MathPowHyp remoteGF) ∧
    (∀ G L, letI := heapAt G L; lib.RandSeedHyp remoteGF) ∧
    ∃ H : (∀ G L (π : NetProtoGS), letI := heapAt G L;
        letI := netRpcHttpAddr remoteGF (Gg := G); RpcHttpHyp remoteGF),
      (∀ G L (π : NetProtoGS), letI := heapAt G L; letI := netRpcHttpAddr remoteGF (Gg := G);
        letI := H G L π; RpcBootHyp remoteGF) := by
  refine ⟨fun G L => ?_, fun G L => ?_, fun G L => ?_, fun G L => ?_, fun G L => ?_,
    fun G L => ?_, fun G L => ?_, fun G L => ?_,
    ⟨fun G L π => rpcHttpHyp (hG := heapAt G L) (π := π), fun G L π => ?_⟩⟩
  · exact net.rpc.initHyp_holds (hG := heapAt G L)
  · exact net.http.initHyp_holds (hG := heapAt G L)
  · exact mrand_initHyp_holds (hG := heapAt G L)
  · exact binaryVarint_holds (hG := heapAt G L)
  · exact stringsIndex_holds (hG := heapAt G L)
  · exact sortSlice_holds (hG := heapAt G L)
  · exact mathPow_holds (hG := heapAt G L)
  · exact randSeed_holds (hG := heapAt G L)
  · exact rpcBootHyp_holds (hG := heapAt G L) (π := π)

end statement

end gryff.examples.gryffnet.instances
end Perennial
