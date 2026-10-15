/- Lean-first (no Rocq counterpart).

`checkParallel(model, history, computeInfo, timeout)` (checker.go): one `checkSingle`
goroutine per partition, under a context cancelled when a partition fails (unless
`computeInfo`) or at the timeout. Given each partition's entries (`EntriesFor`, read-only),
on partitions that are all linearizable it never answers `Illegal`, and with no timeout
(`timeout <= 0`) it answers `Ok`. `LinearizationInfo` (for the visualizer) has no claim.
`context.isClosedchanInit` is what `context.WithCancel(context.Background())` needs.
-/
module

public import Proof.github_com.anishathalye.porcupine.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace porcupine

open Iris Iris.BI github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

/-- See the file header. -/
abbrev checkParallel.spec : Prop :=
  ∀ (σ : Type) (S : ModelSpec GF σ) (m : Model) (hsl : GoSlice) (sls : List GoSlice)
    (hs : List (List (Theory.Op OpV))) (cp : Bool) (dur : w64),
  sls.length = hs.length → (hs.length : Int) < 2 ^ 32 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.anishathalye.porcupine ∗
      context.isClosedchanInit ∗ isModelFilled S m ∗ hsl ↦*□ sls ∗
      ([∗list] i ↦ sl ∈ sls, ∃ (h : List (Theory.Op OpV)) (es : List entry),
        ⌜hs[i]? = some h ∧ EntriesFor h es ∧ (h.length : Int) < 2 ^ 60⌝ ∗
        sl ↦*□ es ∗ histIoOk S h) }}
    (App (App (App (App (Val (@! github_com.anishathalye.porcupine.checkParallel))
      (Val #m)) (Val #hsl)) (Val #cp)) (Val #dur))
  {{ (r : GoString) (info : LinearizationInfo), RET (PairV #r #info);
      ⌜(∀ h ∈ hs, Linearizable S.M h) →
        r ≠ go!"Illegal" ∧ (sint.Z dur ≤ 0 → r = go!"Ok")⌝ }}

end spec

end porcupine
end EtcdGrove
end Perennial
