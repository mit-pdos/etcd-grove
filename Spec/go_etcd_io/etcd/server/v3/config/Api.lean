/-
# `server/config`: the server's configuration as the specs read it (batch 2e)

`config.ServerConfig` is a Go struct passed by value (`NewServer(cfg)`): its scalar fields are in the
Lean value (`cfg.Name'`, `cfg.NewCluster'`, `cfg.TickMs'`, ...) and every statement reads them there.
What is behind a pointer, a slice or a map (the URL lists, the initial-cluster map) is in the heap,
read-only for good once the configuration is built: `cfgHeap cfg c` gives it as the pure model `c`.

## Vocabulary

* `Model` (transparent): the heap parts of a configuration, as strings: the initial cluster
  (`InitialPeerURLsMap`: each name with its peer URLs, `url.URL.String()` of each, in the map's
  insertion-independent order: a list whose names are distinct), the member's own peer and client
  URLs (`PeerURLs`, `ClientURLs`, `StringSlice()`).
* `cfgHeap cfg c` (persistent, timeless): **the heap parts of `cfg` hold `c`**, read-only (`↦□` of
  the slices' and the map's contents). Intended realization: the read-only points-to of the
  `types.URLs` slices (each `url.URL` struct and its strings) and of the `types.URLsMap` map, with
  `c` their string forms (`url.URL.String` is a pure function of the struct's fields). Produced by
  whoever builds the configuration (`examples/lib/etcdstart`'s `newServerMode`: composite literals,
  then discarded fractions), consumed by `bootstrap`'s contract.
* `Dirs` (transparent), `dirsOf cfg`: **where a member keeps its files**: the data directory
  (`DataDir`) and the dedicated WAL directory (`DedicatedWALDir`, `""` for the default
  `<data>/member/wal`). The member's durable resources (`EtcdServer.memberDisk`, `dataDirFresh`)
  are keyed by it.
* The paths `backendPathOf`, `walDirOf`, `snapDirOf` (opaque pure functions: `filepath.Join`'s
  cleaning is Go's, not stated): what `BackendPath()`, `WALDir()`, `SnapDir()` return.
* `reqTimeoutOf cfg` (transparent): `ReqTimeout()`'s value, the wrapping arithmetic Go computes
  (`5s + 2 * time.Duration(ElectionTicks * int(TickMs)) * 1ms`), as `PeerDialTimeout` and
  `ElectionTimeout` likewise: a trusted contract states what the code computes, never a property
  of it (PRINCIPLES, "Sound").

## Laws

`cfgHeap_persistent`, `cfgHeap_timeless`, `cfgHeap_agree`.

## Requirement snippets

`examples/specreq/etcdserverboot/` (`config.go`: the configurations the starters build).
-/
module

public import Spec.go_etcd_io.etcd.client.pkg.v3.types.Api
public import GeneratedProof.go_etcd_io.etcd.server.v3.config
public import Spec.PkgInit.go_etcd_io.etcd.server.v3.config

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Config

open Iris Iris.BI

/-- The heap parts of a server configuration (see the header). -/
structure Model where
  /-- `InitialPeerURLsMap`: each member name with its peer URLs (their `String()` forms) -/
  initialCluster : List (GoString × List GoString)
  /-- `PeerURLs` -/
  peerURLs : List GoString
  /-- `ClientURLs` -/
  clientURLs : List GoString

/-- The peer URLs the initial cluster gives the name `n` (none if `n` is not in it). -/
def Model.initialURLs (c : Model) (n : GoString) : Option (List GoString) :=
  (c.initialCluster.find? (fun p => decide (p.1 = n))).map (·.2)

/-- Where a member keeps its files: the data directory and the dedicated WAL directory (`""`: the
default under the data directory). -/
structure Dirs where
  dataDir : GoString
  walDir : GoString

/-- The directories of configuration `cfg`. -/
def dirsOf [GooseExts] [GoGlobalContext] (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) :
    Dirs :=
  ⟨cfg.DataDir', cfg.DedicatedWALDir'⟩

/-- `BackendPath()` of a configuration whose data directory is `d` (`<d>/member/snap/db`). -/
opaque backendPathOf (d : GoString) : GoString

/-- `WALDir()` of a configuration with these directories. -/
opaque walDirOf (ds : Dirs) : GoString

/-- `SnapDir()` of a configuration whose data directory is `d` (`<d>/member/snap`). -/
opaque snapDirOf (d : GoString) : GoString

section vals
variable [GooseExts] [GoGlobalContext]

/-- `ElectionTicks * int(TickMs)`, Go's wrapping `int` product, as a `time.Duration`. -/
def electionMs (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) : w64 :=
  cfg.ElectionTicks' * cfg.TickMs'

/-- `ReqTimeout()`: `5s + 2 * electionMs * 1ms` (wrapping). -/
def reqTimeoutOf (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) : w64 :=
  W64 5000000000 + W64 2 * electionMs cfg * W64 1000000

/-- `ElectionTimeout()`: `electionMs * 1ms` (wrapping). -/
def electionTimeoutOf (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) : w64 :=
  electionMs cfg * W64 1000000

/-- `PeerDialTimeout()`: `1s + electionMs * 1ms` (wrapping). -/
def peerDialTimeoutOf (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) : w64 :=
  W64 1000000000 + electionMs cfg * W64 1000000

end vals

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext]

/-- **The heap parts of `cfg` hold `c`**, read-only for good (persistent). -/
opaque cfgHeap (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (c : Model) : IProp GF :=
  iprop(True)

def cfgHeap_persistent.spec : Prop := ∀ cfg c, Persistent (cfgHeap (GF := GF) cfg c)

def cfgHeap_timeless.spec : Prop := ∀ cfg c, Timeless (cfgHeap (GF := GF) cfg c)

def cfgHeap_agree.spec : Prop := ∀ cfg c c',
  cfgHeap (GF := GF) cfg c ∗ cfgHeap cfg c' ⊢ ⌜c = c'⌝

/-- **Provisional (1c's `types`):** the `types.URLsMap` `m` holds, read-only for good, each name
with URLs whose `String()` forms are given. Persistent. -/
opaque urlsMapStrs (m : GoMap) (cl : List (GoString × List GoString)) : IProp GF := iprop(True)

/-- **Introduction** (round 1, completeness F1): the read-only URL slices and map, as a starter
builds them (composite literals of `types.URLs`/`types.URLsMap`, then never written). -/
def cfgHeap_intro.spec : Prop := ∀ (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig)
    (c : Model),
  Types.urlsStrs (GF := GF) cfg.PeerURLs' c.peerURLs ∗ Types.urlsStrs cfg.ClientURLs' c.clientURLs ∗
    urlsMapStrs cfg.InitialPeerURLsMap' c.initialCluster ⊢ cfgHeap cfg c

end res

end Config
end EtcdGrove
end Perennial
