/-
etcd's cache `Config` and its options (`cache/config.go`): the vocabulary of
`Spec/go_etcd_io/etcd/cache/v3/{defaultConfig,With*}.lean` and of `New`'s spec. Lean-first (no
Rocq counterpart).

An `Option` is a closure `func(*Config)`; `cfgOptSpec f g` is its triple, with the model
transformer `g : Config → Config` (as `optSpec` is for `clientv3.OpOption`s, `InvOp.lean`).
`New(client, prefix, opts...)` applies the options in order to `defaultConfig()`
(`cfgApply`).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3

/-- The value `defaultConfig()` returns (`cache/config.go`; durations in nanoseconds). -/
def defaultConfigVal [FfiSyntax] : Config :=
  { PerWatcherBufferSize' := W64 10
    HistoryWindowSize' := W64 2048
    ResyncInterval' := W64 50000000
    InitialBackoff' := W64 50000000
    MaxBackoff' := W64 2000000000
    GetTimeout' := W64 5000000000
    WaitTimeout' := W64 3000000000
    BTreeDegree' := W64 32
    ProgressRequestInterval' := W64 100000000
    ProgressNotifyInterval' := W64 600000000000 }

/-- The configuration after the options with transformers `gs`, applied in order to `c`. -/
def cfgApply [FfiSyntax] (gs : List (Config → Config)) (c : Config) : Config :=
  gs.foldl (fun c g => g c) c

theorem cfgApply_take_succ [FfiSyntax] (gs : List (Config → Config)) (c : Config) (n : Nat)
    (g : Config → Config) (h : gs[n]? = some g) :
    cfgApply (gs.take (n + 1)) c = g (cfgApply (gs.take n) c) := by
  unfold cfgApply
  rw [List.take_add_one, h]
  simp

/-- `newCache`'s validation: `HistoryWindowSize > 0` and `BTreeDegree >= 2`. -/
def CfgValid [FfiSyntax] (c : Config) : Prop :=
  0 < sint.Z c.HistoryWindowSize' ∧ 2 ≤ sint.Z c.BTreeDegree'

instance CfgValid.decidable [FfiSyntax] (c : Config) : Decidable (CfgValid c) := by
  unfold CfgValid; infer_instance

/-- What the proofs need of a configuration `newCache` accepts and the code does not check: the
history capacity at most `2^61` (`newRingBuffer`: `at` computes up to `3·cap`), the btree degree
at most `2^62` (the btree's `maxItems()` overflows above), and a non-negative
`PerWatcherBufferSize` (finding 5: `make(chan, -1)` panics in `Watch` and in the watch loop). -/
def CfgBounded [FfiSyntax] (c : Config) : Prop :=
  sint.Z c.HistoryWindowSize' ≤ 2 ^ 61 ∧ sint.Z c.BTreeDegree' ≤ 2 ^ 62 ∧
    0 ≤ sint.Z c.PerWatcherBufferSize'

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- The `Option` closure `f` (`func(*Config)`) transforms the `Config` it is given by `g`
(persistent). -/
def cfgOptSpec (f : GoFunc) (g : Config → Config) : IProp GF :=
  iprop(□ ∀ (cp : Loc) (c : Config),
    {{ cp ↦ c }} (App (Val #f) (Val #cp)) {{ RET #(); cp ↦ g c }})

instance cfgOptSpec_persistent (f : GoFunc) (g : Config → Config) :
    Persistent (cfgOptSpec (GF := GF) f g) := by
  unfold cfgOptSpec; infer_instance

/-- The `[]Option` slice `sl` (read-only) holds closures with the transformers `gs`. -/
def cfgOptsAt (sl : GoSlice) (gs : List (Config → Config)) : IProp GF :=
  iprop(∃ fs : List GoFunc, sl ↦*□ fs ∗ ⌜fs.length = gs.length⌝ ∗
    □ ∀ (i : Nat) (f : GoFunc) (g : Config → Config), ⌜fs[i]? = some f⌝ -∗ ⌜gs[i]? = some g⌝ -∗
      cfgOptSpec f g)

instance cfgOptsAt_persistent (sl : GoSlice) (gs : List (Config → Config)) :
    Persistent (cfgOptsAt (GF := GF) sl gs) := by
  unfold cfgOptsAt; infer_instance

end defs

end EtcdGrove
end Perennial
