/-
The model of prometheus's default registry (`examples/lib/promreg`, notes/prom-registry.md): its
ghost state and invariant. Lean-first.

* **The ghost names of a run** (`PromRegGS`, as `WalGS`): a ghost map from descriptor and collector
  IDs to `()`, allocated by each run's proof (`promReg_alloc`); its exclusive elements are the rights
  to register (`idTok`). No axiom produces one (`notes/decisions.md`, the prom-registry entry).
* **The registry** (`isRegistry f r`, persistent): the `*Registry` `r`'s map fields (read-only), and
  its mutex, whose invariant (`regInv`) owns the three maps and the element of every registered
  descriptor ID and collector ID; every registered name is built in or has its ID `f n` registered
  (`f` is the naming of IDs, prometheus's `descId`). So a caller holding `idTok (f n)`, `n` not
  built in, knows `f n` and `n` unregistered.
-/
module

public import GeneratedProof.github_com.mit_pdos.etcd_grove.examples.lib.promreg
public import Perennial.Golang.Theory.Map
public import Perennial.Ghost.GhostMap
public import Perennial.Proof.sync.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace promreg

open Iris Iris.BI Iris.ProofMode
open _root_.Perennial.github_com.mit_pdos.etcd_grove.examples.lib

/-- **The ghost names of one run's registry rights** (allocated by the run's proof,
`promReg_alloc`). -/
class PromRegGS (GF : BundledGFunctors) where
  γ : GName

/-! ## The builtins (`SeedBuiltins`; configuration C, `model_test.go`'s `TestBuiltins`) -/

/-- `BuiltinIDs()`. -/
def builtinIDs : List w64 :=
  [W64 0x512fd998710995b,
    W64 0x1656dbe17be56c8e,
    W64 0x25ecb62222d45656,
    W64 0x262eac1a08329894,
    W64 0x27c54efad053ac38,
    W64 0x3344a85f7b6c8e8f,
    W64 0x370d8b8ba9508228,
    W64 0x3ae6afd8564ad088,
    W64 0x3e79faf5f9128782,
    W64 0x411d6370a35c0ff3,
    W64 0x43ee38314d0e9d26,
    W64 0x4f8a790dd5db0ffd,
    W64 0x5036f4e6bfcbacb3,
    W64 0x59cff99389bbcab8,
    W64 0x5dcc41232e6f6fcf,
    W64 0x685c04a736f2da00,
    W64 0x69a5f00e0c426211,
    W64 0x6b4103ccc4d2326c,
    W64 0x70eb462430943cff,
    W64 0x769a93a32973af9b,
    W64 0x80adfa8af06370e0,
    W64 0x87989ab99a809acc,
    W64 0x8b08ab44d6d64d78,
    W64 0x8ce99c9889b6fbce,
    W64 0x8f317e9bd37b52b8,
    W64 0x9d3545e5f6f93ba5,
    W64 0x9ec03ad3db5d4289,
    W64 0xa85bf07416d4b8e0,
    W64 0xac4ef85db62472cb,
    W64 0xc5ec13c9ed3ec103,
    W64 0xc87f9396f586162b,
    W64 0xd8075733a79d1e3a,
    W64 0xd9589318aee2aa20,
    W64 0xdb617cf0bc600144,
    W64 0xe39410b0b2ace77d,
    W64 0xe6efe65b451f2f19,
    W64 0xe7d1a41eea0bc77a,
    W64 0xe98ebbd01e4f623a]

/-- `BuiltinNames()`. -/
def builtinNames : List GoString :=
  [go!"go_gc_duration_seconds", go!"go_gc_gogc_percent", go!"go_gc_gomemlimit_bytes", go!"go_goroutines", go!"go_info", go!"go_memstats_alloc_bytes", go!"go_memstats_alloc_bytes_total", go!"go_memstats_buck_hash_sys_bytes", go!"go_memstats_frees_total", go!"go_memstats_gc_sys_bytes", go!"go_memstats_heap_alloc_bytes", go!"go_memstats_heap_idle_bytes", go!"go_memstats_heap_inuse_bytes", go!"go_memstats_heap_objects", go!"go_memstats_heap_released_bytes", go!"go_memstats_heap_sys_bytes", go!"go_memstats_last_gc_time_seconds", go!"go_memstats_mallocs_total", go!"go_memstats_mcache_inuse_bytes", go!"go_memstats_mcache_sys_bytes", go!"go_memstats_mspan_inuse_bytes", go!"go_memstats_mspan_sys_bytes", go!"go_memstats_next_gc_bytes", go!"go_memstats_other_sys_bytes", go!"go_memstats_stack_inuse_bytes", go!"go_memstats_stack_sys_bytes", go!"go_memstats_sys_bytes", go!"go_sched_gomaxprocs_threads", go!"go_threads", go!"process_cpu_seconds_total", go!"process_max_fds", go!"process_network_receive_bytes_total", go!"process_network_transmit_bytes_total", go!"process_open_fds", go!"process_resident_memory_bytes", go!"process_start_time_seconds", go!"process_virtual_memory_bytes", go!"process_virtual_memory_max_bytes"]

/-- `BuiltinDims()`. -/
def builtinDims : List w64 :=
  [W64 0xf26f282174a16582,
    W64 0x6f193a898d82b57e,
    W64 0x3f946342ef3e2dc1,
    W64 0xd6ea775f3e57e0a3,
    W64 0xd1ef65438edd64ca,
    W64 0xcb9e68d810ea886,
    W64 0x17cc9550218dfec4,
    W64 0x7123dfe4d102ec69,
    W64 0xc546633d5f4c2aee,
    W64 0x11ada46281e85a2,
    W64 0x7c5deb187b85727,
    W64 0x4d92700b6179627e,
    W64 0x5614f86bbcc71153,
    W64 0x4904e5a3507bc880,
    W64 0xf36123dbdf6efbc9,
    W64 0xbd3e7caa8f21ce08,
    W64 0x73a8a404a2b111fe,
    W64 0x318b0ef37cbb1a3f,
    W64 0xf0f1c70cebad1075,
    W64 0xad60f0b1578fc8c4,
    W64 0x245f1e59f37ed4a4,
    W64 0xb85def6346437dc9,
    W64 0x84369ece0eb7f645,
    W64 0x60c4c92a200f4c53,
    W64 0x9012115f6f8ae238,
    W64 0xf6a0e04a911cd1a,
    W64 0xa5ff86d00c9ad67c,
    W64 0x1602c8428d1addf3,
    W64 0xf559241e19ae5834,
    W64 0x7969c0480bf010ff,
    W64 0xc40e6e0ce638254b,
    W64 0xa804b284be1ced27,
    W64 0x5f99f2510c2201d7,
    W64 0xdfd12ffdc6d1d772,
    W64 0xcfa21a2f3ba47cad,
    W64 0x9e3999b4a0663cbd,
    W64 0xecb155a0ecaa6d63,
    W64 0x59c47110ce47128e]

/-- `BuiltinCollectors()`. -/
def builtinCollectors : List w64 :=
  [W64 0x2af17207bfef49d7,
    W64 0x3c6db576c524bad7]

/-- The IDs whose rights the builtins take: their descriptor IDs and collector IDs. -/
def builtinKeys : List w64 := builtinIDs ++ builtinCollectors

theorem builtinKeys_nodup : builtinKeys.Nodup := by decide +kernel

/-! ## What a collector registers -/

/-- The IDs `Register` adds for descriptors `ds` (all valid): their distinct IDs and the collector
ID, the XOR of the distinct IDs (`registry.go:318-321`). -/
def descKeys [GooseExts] (ds : List promreg.Desc) : List w64 :=
  let ids := (ds.map (·.ID')).eraseDups
  if ids.foldl (· ^^^ ·) 0 ∈ ids then ids else ids ++ [ids.foldl (· ^^^ ·) 0]

/-- Descriptors `Register` accepts, for the registry's naming `f`: valid, each ID its name's, no
builtin name, one dim hash per name. -/
def descsOk [GooseExts] (f : GoString → w64) (ds : List promreg.Desc) : Prop :=
  (∀ d ∈ ds, d.Invalid' = false ∧ d.ID' = f d.FQName' ∧ d.FQName' ∉ builtinNames) ∧
  (∀ d ∈ ds, ∀ d' ∈ ds, d.FQName' = d'.FQName' → d.DimHash' = d'.DimHash') ∧ ds ≠ []

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [promG : PromRegGS GF]

/-- **The right to the ID `k`** (exclusive): this run's ghost map's element. -/
def idTok (k : w64) : IProp GF := ghostMapElem (K := w64) (V := Unit) promG.γ k (DFrac.own 1) ()

/-- The rights to the IDs `ks`. -/
def idToks (ks : List w64) : IProp GF := iprop([∗list] k ∈ ks, idTok k)

/-- The rights the builtins take (prometheus's initializer). -/
def builtinToks : IProp GF := idToks builtinKeys

/-- The mutex's invariant: the maps (`descIDs`, `dimHashesByName`, `collectorsByID`, all values
`true`), the element of every registered ID (descriptor or collector), and every registered name
built in or with its ID registered. -/
def regInv (f : GoString → w64) (mI mD mC : Loc) : IProp GF :=
  iprop(∃ (ids : GMap w64 Bool) (dims : GMap GoString w64) (cols : GMap w64 Bool),
    mI ↦$ ids ∗ mD ↦$ dims ∗ mC ↦$ cols ∗
    ([∗map] k ↦ _b ∈ ids ∪ cols, idTok k) ∗
    ⌜(∀ k b, ids !! k = some b → b = true) ∧ (∀ k b, cols !! k = some b → b = true) ∧
      (∀ n h, dims !! n = some h → n ∈ builtinNames ∨ ids !! f n = some true)⌝)

/-- **The registry `r`** (persistent), naming IDs by `f`. -/
def isRegistry (f : GoString → w64) (r : Loc) : IProp GF :=
  iprop(∃ (mI mD mC : Loc),
    structFieldRef promreg.Registry go!"descIDs" r ↦□ mI ∗
    structFieldRef promreg.Registry go!"dimHashesByName" r ↦□ mD ∗
    structFieldRef promreg.Registry go!"collectorsByID" r ↦□ mC ∗
    sync.isMutex (structFieldRef promreg.Registry go!"mu" r) (regInv f mI mD mC))

instance isRegistry_persistent (f : GoString → w64) (r : Loc) :
    Persistent (isRegistry (GF := GF) f r) := by
  unfold isRegistry; infer_instance

end defs

end promreg
end EtcdGrove
end Perennial
