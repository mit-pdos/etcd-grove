/-
Proof of `Spec/go_etcd_io/etcd/client/v3/experimental/recipes/PriorityQueue__EnqueueUint64.lean`.
Lean-first (no Rocq counterpart); `PriorityQueue__Enqueue.lean`'s proof with a `uint64` priority.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.PriorityQueue__EnqueueUint64
public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.newSequentialKV

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace recipes

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.experimental.recipes go_etcd_io.etcd.api.v3

section fmt_uint64

/-- `fmt`'s `uint64` argument has one value (as Perennial's `IntArgValue.uniq_uint16`). -/
theorem IntArgValue_uniq_uint64 [FfiSyntax] [GoGlobalContext] [go.IntoValInj w64] (n : w64) :
    ∀ z', _root_.Perennial.fmt.IntArgValue (interface.mk go.uint64 #n) z' → z' = uint.Z n := by
  intro z' h
  obtain ⟨n', hv, rfl⟩ := _root_.Perennial.fmt.IntArgValue.of_uint64 h
  rw [go.intoVal_inj hv]

/-- `Sprintf("%s%05d", x, n)` for a string `x` and a `uint64` `n` is exactly `x` then `n` in
decimal with leading zeros up to 5 digits (as Perennial's `SprintfOut.str_05d_uint16`; `padZeros`
pads, never truncates: a 6-to-20-digit `n` is printed whole). -/
theorem SprintfOut_str_05d_uint64 [FfiSyntax] [GoGlobalContext] [go.IntoValInj GoString]
    [go.IntoValInj w64] (x : GoString) (n : w64) (out : GoString)
    (h : _root_.Perennial.fmt.SprintfOut go!"%s%05d"
      [interface.mkOk go.string #x, interface.mkOk go.uint64 #n] out) :
    out = x ++ _root_.Perennial.fmt.padZeros 5 (_root_.Perennial.fmt.decimal (uint.Z n)) := by
  have hfmt : go!"%s%05d" = W8 37 :: W8 115 :: W8 37 :: [W8 48, W8 53, W8 100] := rfl
  rw [hfmt] at h
  obtain ⟨o1, rfl, h1⟩ := _root_.Perennial.fmt.SprintfOut.str_inv h
  obtain ⟨o2, rfl, h2⟩ := _root_.Perennial.fmt.SprintfOut.int_inv (w := 5) (rest := []) (by decide)
    (_root_.Perennial.fmt.IntArgValue.uint64 n) (IntArgValue_uniq_uint64 n) h1
  rw [_root_.Perennial.fmt.SprintfOut.done_inv h2,
    _root_.Perennial.fmt.decimalPad_of_nonneg _ (by word)]
  simp

end fmt_uint64

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.experimental.recipes.Assumptions]

theorem PriorityQueue.EnqueueUint64.wp_proof (hNSK : newSequentialKV.spec (GF := GF) (hG := hG)) :
    PriorityQueue.EnqueueUint64.spec (GF := GF) (hG := hG) := by
  intro q client key val pr lo
  wp_start as ⟨#Hq, #Hlo⟩
  iunfold isPriorityQueue at Hq
  icases Hq with ⟨#Hqc, -, #Hqk, #Hcl⟩
  ihave ⟨%kv, #Hkvf, #Hkv⟩ := isEtcdRecipesClient_kv $$ Hcl
  wp_auto
  wp_apply wp_slice_literal
  try (isplitr; (ipureintro; rfl))
  iintro %sla ⟨Hargs, -⟩
  (try wp_auto)
  ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  wp_apply _root_.Perennial.fmt.wp_Sprintf _ _ _ _ ?wf $$ [$Hfmt $Hargs] as %pfx ⟨Hargs, %Hpfx⟩
  case wf =>
    rw [show sint.nat (W64 (0 + 1)) = 1 by rfl]
    simp only [List.set_cons_succ, List.set_cons_zero]
    exact .cons_string _ _ (.cons_int _ _ _ (_root_.Perennial.fmt.IntArgValue.uint64 pr) .nil)
  rw [show sint.nat (W64 (0 + 1)) = 1 by rfl] at Hpfx
  simp only [List.set_cons_succ, List.set_cons_zero] at Hpfx
  have Hpfx' := SprintfOut_str_05d_uint64 (key ++ go!"/") pr pfx Hpfx
  subst Hpfx'
  (try wp_auto)
  wp_apply hNSK kv [] _ val lo $$ [$Hpkg $Hkv $Hlo] as %rk %err Hres
  · ipureintro; exact ⟨List.nil_prefix, List.nil_prefix⟩
  icases Hres with (⟨%Heq, %k, %g, %r, -, #Hr, #Hc, %Hrr⟩ | %Hne)
  · subst Heq
    (try wp_auto)
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iexists k, g, r
    iframe Hr Hc
    ipureintro; exact ⟨Hrr.1, Hrr.2.1, Hrr.2.2.1⟩
  · (try wp_auto)
    iapply HΦ
    iright
    ipureintro; exact Hne.1

end proof

end recipes
end EtcdGrove
end Perennial
