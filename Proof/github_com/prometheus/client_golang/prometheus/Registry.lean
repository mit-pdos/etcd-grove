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
each to the one package that registers it (`namesFree regNames`, a registering package's; `ownInitResL`, mustreg 2026-11-20); since every right
exists once, two packages registering one name would show up there, as two packages needing
one right.

**What is axiomatized** (each true of prometheus's Go code, client_golang v1.24.1, the version
etcd's `server/go.mod` pins):
- (until 2026-11-22) `collectorName c n`, an opaque `Prop`: now a definition over the real
  registry's descriptors (`RegInv.lean`, route (b), notes/prom-registry.md);
- `nameFree n` (abstract resource): the right to register a collector whose one descriptor is
  `n`'s, without const labels, in the default registry: no collector registered there (now, or
  later by anyone but the holder) has a descriptor named `n`, nor one whose ID is that
  descriptor's ID (`descId n`, `xxhash(n + "\xff")`), nor a collector ID equal to it;

`counterOpts o ns sub name help` (`o` is the `CounterOpts` literal with those four fields, the
others zero) is a definition: `Opts` is translated (until 2026-11-18 it was an axiomatized type,
and `counterOpts` and the literal's spec `wp_counterOptsLit` were axioms).

(metric-inits, 2026-11-19) The constructors `NewGauge` and `NewHistogram` (and the histograms'
`ExponentialBuckets`, for a factor of 2) have specs like `NewCounter`'s, with the definitions
`histOpts` (a `HistogramOpts` literal with a `Buckets` slice), `bucketsOk` (bounds `NewHistogram`
accepts) and `expBuckets`/`expBucketsArgsOk` (`ExponentialBuckets(start, 2, n)`'s exact buckets, as
float64 bits; `expBuckets_ok` proves them accepted), so that the packages' metric variables have
translated initializers rather than one trust-boundary axiom `<X>_init` each.

(prometheus-id-collision, 2026-11-20) Distinct names can have one descriptor ID (`descId`, the
xxhash of `n ++ [0xff]`; `descId_collision`), and the registry refuses the second: until then
program start handed out the rights of any distinct names (`goose_adequacy_start`), so a program
registering counters of two colliding names was proved not to panic, and panics
(`notes/axiom-review/prometheus-id-collision.md`). Program start now hands out rights only for
names whose IDs are pairwise distinct (`descIdsDistinct`, decided for each program's names).

Each axiom is about uninterpreted constants (the names-only functions), so a model in which they
diverge satisfies them: they cannot make the logic inconsistent. The specs of `NewCounter` and
`MustRegister` are in `Spec/github_com/prometheus/client_golang/prometheus/`.
-/
module

public import GeneratedProof.github_com.prometheus.client_golang.prometheus
public import Proof.github_com.cespare.xxhash.v2.Model

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace prometheus

open Iris Iris.BI

/-- prometheus's `BuildFQName(namespace, subsystem, name)` (`metric.go`): the non-empty parts
joined by `_`, or empty if `name` is. -/
def fqName (ns sub name : GoString) : GoString :=
  if name = [] then [] else
    (if ns = [] then [] else ns ++ go!"_") ++ (if sub = [] then [] else sub ++ go!"_") ++ name

/-- A metric name `NewDesc` accepts (`model.UTF8Validation.IsValidMetricName`: non-empty valid
UTF-8), stated for ASCII names (valid UTF-8). Decidable: `decide` checks a literal. -/
def nameOk (n : GoString) : Prop := n ≠ [] ∧ ∀ b ∈ n, b.toNat < 128

instance (n : GoString) : Decidable (nameOk n) := by unfold nameOk; infer_instance

/-- The bits of the float64 `2.0`. -/
def float64Two : w64 := W64 0x4000000000000000

/-- The arguments `start` (float64 bits) and `count` of `ExponentialBuckets(start, 2, count)` for
which its buckets are exact: `start` a positive normal float64 (biased exponent at least 1, sign
bit clear), `count ≥ 1`, and the `count`-th bucket `start * 2^(count-1)` still finite (biased
exponent at most `0x7FE`). Doubling a normal float64 whose result is normal is exact and adds 1 to
the biased exponent, i.e. `2^52` to the bits. -/
def expBucketsArgsOk (start count : w64) : Prop :=
  0x10000000000000 ≤ uint.nat start ∧ 1 ≤ sint.Z count ∧
    uint.nat start + (sint.Z count).toNat.pred * 2 ^ 52 < 0x7FF0000000000000

instance (start count : w64) : Decidable (expBucketsArgsOk start count) := by
  unfold expBucketsArgsOk; infer_instance

/-- The buckets (float64 bits) of `ExponentialBuckets(start, 2, n)` under `expBucketsArgsOk`:
`start * 2^i` for `i < n`, i.e. `start`'s bits plus `i * 2^52`. -/
def expBuckets (start : w64) (n : Nat) : List w64 :=
  (List.range n).map (fun i : Nat => W64 (uint.Z start + (i : Int) * 2 ^ 52))

/-- Bucket upper bounds `NewHistogram` accepts (`histogram.go`, `newHistogram`: "histogram
buckets must be in increasing order"), stated for finite non-negative float64s (bits below
`+Inf`'s `0x7FF0000000000000`, sign bit clear), whose float order is their bits' order: strictly
increasing. -/
def bucketsOk (bs : List w64) : Prop :=
  (∀ b ∈ bs, uint.nat b < 0x7FF0000000000000) ∧ bs.Pairwise (fun a b => uint.nat a < uint.nat b)

instance (bs : List w64) : Decidable (bucketsOk bs) := by unfold bucketsOk; infer_instance

theorem expBuckets_nat {start : w64} {n i : Nat} (hi : i < n)
    (h : uint.nat start + n.pred * 2 ^ 52 < 0x7FF0000000000000) :
    uint.nat (W64 (uint.Z start + (i : Int) * 2 ^ 52)) = uint.nat start + i * 2 ^ 52 := by
  have hi' : i ≤ n.pred := Nat.le_pred_of_lt hi
  have : i * 2 ^ 52 ≤ n.pred * 2 ^ 52 := Nat.mul_le_mul_right _ hi'
  word

/-- `ExponentialBuckets(start, 2, n)`'s buckets under `expBucketsArgsOk` (stated of `n`, the
count as a `Nat`) are ones `NewHistogram` accepts. -/
theorem expBuckets_ok {start : w64} {n : Nat}
    (hb : uint.nat start + n.pred * 2 ^ 52 < 0x7FF0000000000000) :
    bucketsOk (expBuckets start n) := by
  unfold bucketsOk expBuckets
  constructor
  · intro b hb'
    simp only [List.mem_map, List.mem_range] at hb'
    obtain ⟨i, hi, rfl⟩ := hb'
    rw [expBuckets_nat hi hb]
    have : i * 2 ^ 52 ≤ n.pred * 2 ^ 52 := Nat.mul_le_mul_right _ (Nat.le_pred_of_lt hi)
    exact Nat.lt_of_le_of_lt (Nat.add_le_add_left this _) hb
  · rw [List.pairwise_map]
    refine List.pairwise_lt_range.imp_of_mem ?_
    intro i j hi hj hij
    simp only [List.mem_range] at hi hj
    rw [expBuckets_nat hi hb, expBuckets_nat hj hb]
    have : i * 2 ^ 52 < j * 2 ^ 52 := Nat.mul_lt_mul_of_pos_right hij (by decide)
    exact Nat.add_lt_add_left this _

/-- **The ID of the descriptor named `n` without const labels** (`desc.go`, `V2.NewDesc`: the
xxhash of the const label values in the order of their sorted names, the fully-qualified name
first, each followed by the separator byte `0xff`, `separatorByteSlice`; with no const labels, of
`n ++ [0xff]`). A vector's descriptor has the same ID: its variable labels enter only `dimHash`.
`Registry.Register` refuses a collector whose descriptor ID, or whose collector ID (the XOR of its
descriptor IDs: here that one ID), is already registered. -/
def descId (n : GoString) : w64 := xxhash.sum64 (n ++ [255#8])

/-- **The label-free descriptor IDs of the names `Ns` are pairwise distinct** (prometheus-id-
collision, 2026-11-20): the decidable part of program start's claim on the names it hands out
(`goose_adequacy_start`'s `hNsIds`, discharged by `decide +kernel` for each program's names). Two
distinct names can have one ID (`descId_collision`), and then registering both panics although
neither is registered twice (`examples/axiomcx/promidcollide`,
`notes/axiom-review/prometheus-id-collision.md`). -/
def descIdsDistinct (Ns : List GoString) : Prop := (Ns.map descId).Nodup

instance (Ns : List GoString) : Decidable (descIdsDistinct Ns) := by
  unfold descIdsDistinct; infer_instance

/-- Two valid metric names whose label-free descriptors have the same ID (found by a
distinguished-point collision search, 2026-11-20): registering counters of both with the default
registry panics on the second (`examples/axiomcx/promidcollide`). -/
theorem descId_collision :
    go!"m_b699caa269ad35ee" ≠ go!"m_641c7bdac316dcb7" ∧
    descId go!"m_b699caa269ad35ee" = descId go!"m_641c7bdac316dcb7" ∧
    nameOk go!"m_b699caa269ad35ee" ∧ nameOk go!"m_641c7bdac316dcb7" := by
  decide +kernel

section preds
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The `CounterOpts` value `o` is `prometheus.CounterOpts{Namespace: ns, Subsystem: sub, Name:
name, Help: help}` (its other fields zero: no const labels, no unit). The value such a literal
evaluates to (`Opts` is translated). -/
def counterOpts (o : github_com.prometheus.client_golang.prometheus.CounterOpts)
    (ns sub name help : GoString) : Prop :=
  o = { Namespace' := ns, Subsystem' := sub, Name' := name, Help' := help, Unit' := [],
        ConstLabels' := null, now' := func.nil }

/-- The `HistogramOpts` value `o` is `prometheus.HistogramOpts{Namespace: ns, Subsystem: sub,
Name: name, Help: help, Buckets: s}` (its other fields zero: no const labels, no unit, native
histograms off). The value such a literal evaluates to (`HistogramOpts` is translated). -/
def histOpts (o : github_com.prometheus.client_golang.prometheus.HistogramOpts)
    (ns sub name help : GoString) (s : GoSlice) : Prop :=
  o = { (zeroValDef : github_com.prometheus.client_golang.prometheus.HistogramOpts) with
        Namespace' := ns, Subsystem' := sub, Name' := name, Help' := help, Buckets' := s }

/-- **The right to register the name `n`** with prometheus's default registry (exclusive):
no collector registered there, now or later by anyone but the holder, has a descriptor named
`n`, or whose ID (or collector ID) is the ID of `n`'s label-free descriptor (`descId n`). Given at
program start, once per name, for names whose IDs are pairwise distinct (`descIdsDistinct`: the
holder of another name's right registers that name's ID). -/
axiom nameFree {GF : BundledGFunctors} (n : GoString) : IProp GF

end preds

end prometheus
end EtcdGrove
end Perennial
