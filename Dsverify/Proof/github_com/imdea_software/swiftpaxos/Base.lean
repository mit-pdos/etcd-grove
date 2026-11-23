/-
The swiftpaxos kit's common base (notes/dsv-swiftpaxos.md), in place of the lab's generated
`SwiftNetSpec.lean` (dsverify-lab examples/swiftpaxos/proof, run swift-n2nofast-1) and its
`Harness/SafeDistSha.lean`:

* the extension list of the kit's machines, `netShaExts`: this repository's net extension
  (`Net.netExt`) and Perennial's SHA-256 extension with `sha256NoCollisionFilter` (a hash step that
  would return the hash of another input hashed before is an `AngelicExit`), with its semantics,
  ghost state and `HasExt`/`HasSha256` instances, under the lab's names (namespace `Dsv`), so the
  lab's files keep their `attribute [local instance] netShaExts ...` lines. (`Net/Statement`'s
  bridge is for `[netExt]` alone: `notes/dsv-swiftpaxos.md`, "Design findings".)
* `SwiftNetPkgState`: the run's choice of each package's post-initialization state (`isPkgInit`),
  as the lab's, and the `IsPkgInit` instances of the kit's packages over it.
-/
module

public import Dsverify.GeneratedProof.github_com.imdea_software.swiftpaxos.examples.swiftnet
public import GooseLang.Ext.Net.Adequacy
public import Perennial.GooseLang.Ext.Sha256.Specs
public import Perennial.Proof.crypto.sha256
public import Dsverify.GeneratedProof.github_com.emirpasic.gods.utils
public import Dsverify.GeneratedProof.github_com.google.uuid
public import Dsverify.GeneratedProof.os.signal
public import Net.Proof.net.Base
public import Dsverify.Proof.github_com.emirpasic.gods.maps.treemap.Defs
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Base
public import Proof.net.url.PkgInit
public import Proof.os.PkgInit
public import Proof.bufio.PkgInit
public import Proof.syscall.PkgInit
public import Proof.math.rand.Base
public import Proof.unicode.utf8.Base
public import Proof.internal.poll.PkgInit
public import Perennial.Proof.log
public import Perennial.Proof.sync
public import Perennial.Proof.time
public import Perennial.Proof.io
public import Perennial.Proof.bytes
public import Perennial.Proof.context
public import Perennial.Proof.reflect
public import Perennial.Proof.slices
public import Perennial.Proof.strings
public import Perennial.Proof.fmt
public import Perennial.Proof.errors
public import Perennial.Proof.strconv
public import Perennial.Proof.sort
public import Perennial.Proof.math
public import Perennial.Proof.encoding.binary
public import Perennial.Proof.runtime
public import Perennial.Proof.math.bits

@[expose] public section

noncomputable section

namespace Perennial

namespace Dsv

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

/-! ## The extension list: TCP and SHA-256 -/

/-- The extensions of the kit's machines: TCP, and SHA-256 with `sha256NoCollisionFilter`. -/
@[reducible] def netShaExts : GooseExts := ⟨[netExt, sha256Ext sha256NoCollisionFilter]⟩

/-- The semantics of `netShaExts`. -/
@[reducible] def netShaExtsSemantics : @GooseSemantics netShaExts :=
  letI := netShaExts
  ⟨(net_semantics, sha256_semantics sha256NoCollisionFilter, ⟨⟩)⟩

/-- The ghost state of `netShaExts`. -/
@[reducible] def netShaExtsInterp : @GooseInterp netShaExts :=
  letI := netShaExts
  ⟨(net_interp, sha256_interp sha256NoCollisionFilter, ⟨⟩)⟩

set_option linter.defProp false in
/-- `netShaExts` has the TCP extension. -/
@[reducible] def netShaExts_has :
    @HasExt netShaExts netShaExtsSemantics netShaExtsInterp netExt _ _ :=
  letI := netShaExts; letI := netShaExtsSemantics; letI := netShaExtsInterp
  { registered := rfl, sem_eq := rfl, interp_eq := rfl }

set_option linter.defProp false in
/-- `netShaExts` has the SHA-256 extension. -/
@[reducible] def netShaExts_hasSha :
    @HasExt netShaExts netShaExtsSemantics netShaExtsInterp (sha256Ext sha256NoCollisionFilter) _ _ :=
  letI := netShaExts; letI := netShaExtsSemantics; letI := netShaExtsInterp
  { registered := rfl, sem_eq := rfl, interp_eq := rfl }

/-- The kit's SHA-256 extension has the filter `sha256NoCollisionFilter`. -/
theorem netShaExts_hasSha256 :
    @HasSha256 netShaExts netShaExtsSemantics netShaExtsInterp sha256NoCollisionFilter :=
  letI := netShaExts; letI := netShaExtsSemantics; letI := netShaExtsInterp
  ⟨netShaExts_hasSha⟩

/-- Collision resistance holds of the filter (Perennial's). -/
theorem netSha_noCollision : Sha256NoCollision sha256NoCollisionFilter :=
  sha256NoCollisionFilter_noCollision

/-- The ghost state of a machine of the deployment (the lab's `netDistGF`): `Net`'s `netGF`, whose
universal slot holds the ghost state of both extensions. -/
abbrev netDistGF : BundledGFunctors := netGF

end Dsv

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net Dsv

namespace github_com.imdea_software.swiftpaxos

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section defs
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

/-- **The libraries' representation predicates, hypotheses** (notes/dsv-swiftpaxos.md,
"Hypotheses"): the predicates the specs of the libraries without a proved model here are stated
over, with the laws the proof uses of them, each named after the lab's definition or lemma (the
lab proved them over its own models). A deployment's proof is given them, with their specs
(`SwiftHyps`), and proves `swiftpaxos_remote_robust` for any choice. -/
class SwiftLibs (GF : BundledGFunctors) where
  /-- lab `Proof/treemap/Specs.lean` `treemap.isTreeMap`: the `*treemap.Map` at `tm` holds the
  sorted entries `es`, keys encoded by `enc`. -/
  isTreeMap : Loc → (w64 → GoInterface) → github_com.emirpasic.gods.maps.treemap.Entries → IProp GF
  /-- lab `treemap.isTreeMap_sorted`. -/
  isTreeMap_sorted : ∀ tm enc es, isTreeMap tm enc es ⊢
    isTreeMap tm enc es ∗ ⌜github_com.emirpasic.gods.maps.treemap.sortedE es⌝

/-- The run's choice of each package's own post-initialization predicate (`isPkgInitDef`:
its package-level state), for the kit's packages and the packages they import that have no
`IsPkgInit` instance elsewhere in what this part imports (the lab's `SwiftNetPkgState`, widened).
The library hypotheses' representation predicates are its `SwiftLibs` part. -/
class SwiftNetPkgState (GF : BundledGFunctors) extends SwiftLibs GF where
  /-- `github.com/emirpasic/gods/utils`'s package-level state -/
  utils : IProp GF
  /-- `github.com/emirpasic/gods/containers`'s package-level state -/
  containers : IProp GF
  /-- `github.com/emirpasic/gods/maps`'s package-level state -/
  maps : IProp GF
  /-- `github.com/emirpasic/gods/trees`'s package-level state -/
  trees : IProp GF
  /-- `encoding/json`'s package-level state -/
  json : IProp GF
  /-- `github.com/emirpasic/gods/trees/redblacktree`'s package-level state -/
  redblacktree : IProp GF
  /-- `github.com/emirpasic/gods/maps/treemap`'s package-level state -/
  treemap : IProp GF
  /-- `github.com/orcaman/concurrent-map` (names only)'s package-level state -/
  concurrent_map : IProp GF
  /-- `github.com/google/uuid` (names only)'s package-level state -/
  uuid : IProp GF
  /-- `encoding/gob` (names only)'s package-level state -/
  gob : IProp GF
  /-- `os/signal` (names only)'s package-level state -/
  signal : IProp GF
  /-- `internal/bytealg`'s package-level state -/
  bytealg : IProp GF
  /-- `crypto/tls`'s package-level state -/
  crypto_tls : IProp GF
  /-- `encoding/hex`'s package-level state -/
  hex : IProp GF
  /-- `go/token` (the net/rpc model's trusted `IsExported`)'s package-level state -/
  token : IProp GF
  /-- `path`'s package-level state -/
  path : IProp GF
  /-- `net/textproto` (names only, the part `Net/`'s)'s package-level state -/
  textproto : IProp GF
  /-- `golang.org/x/net/http/httpguts` (names only)'s package-level state -/
  httpguts : IProp GF
  /-- `net/http` (the model's)'s package-level state -/
  nethttp : IProp GF
  /-- `net/rpc` (the model's)'s package-level state -/
  netrpc : IProp GF
  /-- `github.com/imdea-software/swiftpaxos/rpc`'s package-level state -/
  rpc : IProp GF
  /-- `github.com/imdea-software/swiftpaxos/dlog`'s package-level state -/
  dlog : IProp GF
  /-- `github.com/imdea-software/swiftpaxos/config`'s package-level state -/
  config : IProp GF
  /-- `github.com/imdea-software/swiftpaxos/state`'s package-level state -/
  state : IProp GF
  /-- `github.com/imdea-software/swiftpaxos/hook`'s package-level state -/
  hook : IProp GF
  /-- `github.com/imdea-software/swiftpaxos/replica/defs`'s package-level state -/
  defs : IProp GF
  /-- `github.com/imdea-software/swiftpaxos/replica`'s package-level state -/
  replica : IProp GF
  /-- `github.com/imdea-software/swiftpaxos/client`'s package-level state -/
  client : IProp GF
  /-- `github.com/imdea-software/swiftpaxos/swift`'s package-level state -/
  swift : IProp GF
  /-- `github.com/imdea-software/swiftpaxos/master`'s package-level state -/
  master : IProp GF

/-- A choice of `SwiftNetPkgState` at every heap. -/
abbrev SwiftNetPkgStates [GoGlobalContext] :=
  ∀ {GF : BundledGFunctors} [HeapGS HasLC.hasLC GF] [go.Semantics], SwiftNetPkgState GF

instance utils_isPkgInit_inst [pkgState : SwiftNetPkgState GF] :
    IsPkgInit (IProp GF) pkg_id.github_com.emirpasic.gods.utils :=
  define_is_pkg_init (pkgState.utils)
instance utils_get_isPkgInit_wf_inst [pkgState : SwiftNetPkgState GF] :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.emirpasic.gods.utils :=
  build_get_is_pkg_init_wf

instance containers_isPkgInit_inst [pkgState : SwiftNetPkgState GF] :
    IsPkgInit (IProp GF) pkg_id.github_com.emirpasic.gods.containers :=
  define_is_pkg_init (pkgState.containers)
instance containers_get_isPkgInit_wf_inst [pkgState : SwiftNetPkgState GF] :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.emirpasic.gods.containers :=
  build_get_is_pkg_init_wf

instance maps_isPkgInit_inst [pkgState : SwiftNetPkgState GF] :
    IsPkgInit (IProp GF) pkg_id.github_com.emirpasic.gods.maps :=
  define_is_pkg_init (pkgState.maps)
instance maps_get_isPkgInit_wf_inst [pkgState : SwiftNetPkgState GF] :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.emirpasic.gods.maps :=
  build_get_is_pkg_init_wf

instance trees_isPkgInit_inst [pkgState : SwiftNetPkgState GF] :
    IsPkgInit (IProp GF) pkg_id.github_com.emirpasic.gods.trees :=
  define_is_pkg_init (pkgState.trees)
instance trees_get_isPkgInit_wf_inst [pkgState : SwiftNetPkgState GF] :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.emirpasic.gods.trees :=
  build_get_is_pkg_init_wf

instance json_isPkgInit_inst [pkgState : SwiftNetPkgState GF] :
    IsPkgInit (IProp GF) pkg_id.encoding.json :=
  define_is_pkg_init (pkgState.json)
instance json_get_isPkgInit_wf_inst [pkgState : SwiftNetPkgState GF] :
    GetIsPkgInitWf (IProp GF) pkg_id.encoding.json :=
  build_get_is_pkg_init_wf

instance redblacktree_isPkgInit_inst [pkgState : SwiftNetPkgState GF] :
    IsPkgInit (IProp GF) pkg_id.github_com.emirpasic.gods.trees.redblacktree :=
  define_is_pkg_init (pkgState.redblacktree)
instance redblacktree_get_isPkgInit_wf_inst [pkgState : SwiftNetPkgState GF] :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.emirpasic.gods.trees.redblacktree :=
  build_get_is_pkg_init_wf

instance treemap_isPkgInit_inst [pkgState : SwiftNetPkgState GF] :
    IsPkgInit (IProp GF) pkg_id.github_com.emirpasic.gods.maps.treemap :=
  define_is_pkg_init (pkgState.treemap)
instance treemap_get_isPkgInit_wf_inst [pkgState : SwiftNetPkgState GF] :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.emirpasic.gods.maps.treemap :=
  build_get_is_pkg_init_wf

instance concurrent_map_isPkgInit_inst [pkgState : SwiftNetPkgState GF] :
    IsPkgInit (IProp GF) pkg_id.github_com.orcaman.concurrent_map :=
  define_is_pkg_init (pkgState.concurrent_map)
instance concurrent_map_get_isPkgInit_wf_inst [pkgState : SwiftNetPkgState GF] :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.orcaman.concurrent_map :=
  build_get_is_pkg_init_wf

instance uuid_isPkgInit_inst [pkgState : SwiftNetPkgState GF] :
    IsPkgInit (IProp GF) pkg_id.github_com.google.uuid :=
  define_is_pkg_init (pkgState.uuid)
instance uuid_get_isPkgInit_wf_inst [pkgState : SwiftNetPkgState GF] :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.google.uuid :=
  build_get_is_pkg_init_wf

instance gob_isPkgInit_inst [pkgState : SwiftNetPkgState GF] :
    IsPkgInit (IProp GF) pkg_id.encoding.gob :=
  define_is_pkg_init (pkgState.gob)
instance gob_get_isPkgInit_wf_inst [pkgState : SwiftNetPkgState GF] :
    GetIsPkgInitWf (IProp GF) pkg_id.encoding.gob :=
  build_get_is_pkg_init_wf

instance signal_isPkgInit_inst [pkgState : SwiftNetPkgState GF] :
    IsPkgInit (IProp GF) pkg_id.os.signal :=
  define_is_pkg_init (pkgState.signal)
instance signal_get_isPkgInit_wf_inst [pkgState : SwiftNetPkgState GF] :
    GetIsPkgInitWf (IProp GF) pkg_id.os.signal :=
  build_get_is_pkg_init_wf

instance bytealg_isPkgInit_inst [pkgState : SwiftNetPkgState GF] :
    IsPkgInit (IProp GF) pkg_id.internal.bytealg :=
  define_is_pkg_init (pkgState.bytealg)
instance bytealg_get_isPkgInit_wf_inst [pkgState : SwiftNetPkgState GF] :
    GetIsPkgInitWf (IProp GF) pkg_id.internal.bytealg :=
  build_get_is_pkg_init_wf

instance crypto_tls_isPkgInit_inst [pkgState : SwiftNetPkgState GF] :
    IsPkgInit (IProp GF) pkg_id.crypto.tls :=
  define_is_pkg_init (pkgState.crypto_tls)
instance crypto_tls_get_isPkgInit_wf_inst [pkgState : SwiftNetPkgState GF] :
    GetIsPkgInitWf (IProp GF) pkg_id.crypto.tls :=
  build_get_is_pkg_init_wf

instance hex_isPkgInit_inst [pkgState : SwiftNetPkgState GF] :
    IsPkgInit (IProp GF) pkg_id.encoding.hex :=
  define_is_pkg_init (pkgState.hex)
instance hex_get_isPkgInit_wf_inst [pkgState : SwiftNetPkgState GF] :
    GetIsPkgInitWf (IProp GF) pkg_id.encoding.hex :=
  build_get_is_pkg_init_wf

instance token_isPkgInit_inst [pkgState : SwiftNetPkgState GF] :
    IsPkgInit (IProp GF) pkg_id.go.token :=
  define_is_pkg_init (pkgState.token)
instance token_get_isPkgInit_wf_inst [pkgState : SwiftNetPkgState GF] :
    GetIsPkgInitWf (IProp GF) pkg_id.go.token :=
  build_get_is_pkg_init_wf

instance path_isPkgInit_inst [pkgState : SwiftNetPkgState GF] :
    IsPkgInit (IProp GF) pkg_id.path :=
  define_is_pkg_init (pkgState.path)
instance path_get_isPkgInit_wf_inst [pkgState : SwiftNetPkgState GF] :
    GetIsPkgInitWf (IProp GF) pkg_id.path :=
  build_get_is_pkg_init_wf

instance textproto_isPkgInit_inst [pkgState : SwiftNetPkgState GF] :
    IsPkgInit (IProp GF) pkg_id.net.textproto :=
  define_is_pkg_init (pkgState.textproto)
instance textproto_get_isPkgInit_wf_inst [pkgState : SwiftNetPkgState GF] :
    GetIsPkgInitWf (IProp GF) pkg_id.net.textproto :=
  build_get_is_pkg_init_wf

instance httpguts_isPkgInit_inst [pkgState : SwiftNetPkgState GF] :
    IsPkgInit (IProp GF) pkg_id.vendor.golang_org.x.net.http.httpguts :=
  define_is_pkg_init (pkgState.httpguts)
instance httpguts_get_isPkgInit_wf_inst [pkgState : SwiftNetPkgState GF] :
    GetIsPkgInitWf (IProp GF) pkg_id.vendor.golang_org.x.net.http.httpguts :=
  build_get_is_pkg_init_wf

instance nethttp_isPkgInit_inst [pkgState : SwiftNetPkgState GF] :
    IsPkgInit (IProp GF) pkg_id.net.http :=
  define_is_pkg_init (pkgState.nethttp)
instance nethttp_get_isPkgInit_wf_inst [pkgState : SwiftNetPkgState GF] :
    GetIsPkgInitWf (IProp GF) pkg_id.net.http :=
  build_get_is_pkg_init_wf

instance netrpc_isPkgInit_inst [pkgState : SwiftNetPkgState GF] :
    IsPkgInit (IProp GF) pkg_id.net.rpc :=
  define_is_pkg_init (pkgState.netrpc)
instance netrpc_get_isPkgInit_wf_inst [pkgState : SwiftNetPkgState GF] :
    GetIsPkgInitWf (IProp GF) pkg_id.net.rpc :=
  build_get_is_pkg_init_wf

instance rpc_isPkgInit_inst [pkgState : SwiftNetPkgState GF] :
    IsPkgInit (IProp GF) pkg_id.github_com.imdea_software.swiftpaxos.rpc :=
  define_is_pkg_init (pkgState.rpc)
instance rpc_get_isPkgInit_wf_inst [pkgState : SwiftNetPkgState GF] :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.imdea_software.swiftpaxos.rpc :=
  build_get_is_pkg_init_wf

instance dlog_isPkgInit_inst [pkgState : SwiftNetPkgState GF] :
    IsPkgInit (IProp GF) pkg_id.github_com.imdea_software.swiftpaxos.dlog :=
  define_is_pkg_init (pkgState.dlog)
instance dlog_get_isPkgInit_wf_inst [pkgState : SwiftNetPkgState GF] :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.imdea_software.swiftpaxos.dlog :=
  build_get_is_pkg_init_wf

instance config_isPkgInit_inst [pkgState : SwiftNetPkgState GF] :
    IsPkgInit (IProp GF) pkg_id.github_com.imdea_software.swiftpaxos.config :=
  define_is_pkg_init (pkgState.config)
instance config_get_isPkgInit_wf_inst [pkgState : SwiftNetPkgState GF] :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.imdea_software.swiftpaxos.config :=
  build_get_is_pkg_init_wf

instance state_isPkgInit_inst [pkgState : SwiftNetPkgState GF] :
    IsPkgInit (IProp GF) pkg_id.github_com.imdea_software.swiftpaxos.state :=
  define_is_pkg_init (pkgState.state)
instance state_get_isPkgInit_wf_inst [pkgState : SwiftNetPkgState GF] :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.imdea_software.swiftpaxos.state :=
  build_get_is_pkg_init_wf

instance hook_isPkgInit_inst [pkgState : SwiftNetPkgState GF] :
    IsPkgInit (IProp GF) pkg_id.github_com.imdea_software.swiftpaxos.hook :=
  define_is_pkg_init (pkgState.hook)
instance hook_get_isPkgInit_wf_inst [pkgState : SwiftNetPkgState GF] :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.imdea_software.swiftpaxos.hook :=
  build_get_is_pkg_init_wf

instance defs_isPkgInit_inst [pkgState : SwiftNetPkgState GF] :
    IsPkgInit (IProp GF) pkg_id.github_com.imdea_software.swiftpaxos.replica.defs :=
  define_is_pkg_init (pkgState.defs)
instance defs_get_isPkgInit_wf_inst [pkgState : SwiftNetPkgState GF] :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.imdea_software.swiftpaxos.replica.defs :=
  build_get_is_pkg_init_wf

instance replica_isPkgInit_inst [pkgState : SwiftNetPkgState GF] :
    IsPkgInit (IProp GF) pkg_id.github_com.imdea_software.swiftpaxos.replica :=
  define_is_pkg_init (pkgState.replica)
instance replica_get_isPkgInit_wf_inst [pkgState : SwiftNetPkgState GF] :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.imdea_software.swiftpaxos.replica :=
  build_get_is_pkg_init_wf

instance client_isPkgInit_inst [pkgState : SwiftNetPkgState GF] :
    IsPkgInit (IProp GF) pkg_id.github_com.imdea_software.swiftpaxos.client :=
  define_is_pkg_init (pkgState.client)
instance client_get_isPkgInit_wf_inst [pkgState : SwiftNetPkgState GF] :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.imdea_software.swiftpaxos.client :=
  build_get_is_pkg_init_wf

instance swift_isPkgInit_inst [pkgState : SwiftNetPkgState GF] :
    IsPkgInit (IProp GF) pkg_id.github_com.imdea_software.swiftpaxos.swift :=
  define_is_pkg_init (pkgState.swift)
instance swift_get_isPkgInit_wf_inst [pkgState : SwiftNetPkgState GF] :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.imdea_software.swiftpaxos.swift :=
  build_get_is_pkg_init_wf

instance master_isPkgInit_inst [pkgState : SwiftNetPkgState GF] :
    IsPkgInit (IProp GF) pkg_id.github_com.imdea_software.swiftpaxos.master :=
  define_is_pkg_init (pkgState.master)
instance master_get_isPkgInit_wf_inst [pkgState : SwiftNetPkgState GF] :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.imdea_software.swiftpaxos.master :=
  build_get_is_pkg_init_wf

instance swiftnet_isPkgInit_inst [pkgState : SwiftNetPkgState GF] :
    IsPkgInit (IProp GF) pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet :=
  define_is_pkg_init iprop(True)
instance swiftnet_get_isPkgInit_wf_inst [pkgState : SwiftNetPkgState GF] :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet :=
  build_get_is_pkg_init_wf

end defs

end github_com.imdea_software.swiftpaxos

end Perennial
