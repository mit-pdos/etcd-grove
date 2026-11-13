/- Lean-first (no Rocq counterpart).

# The cut's use of the file pipeline (W2 of `notes/wal-fsext-plan.md`, `WAL__cut.lean`'s steps 4
and 6)

* `wp_walPipeH_open`: `w.fp.Open()` from the handle's pipeline (`walPipeH fp dir j k`, `k` cuts made,
  `k + 2 < 2^63`): the file `n` (`pipeFile`: `pipeTmp n` whole, zeros, its claim), the caller's
  token after `n + 1` files; on an error nothing (the cut's error loses the handle).
* `walPipeH_next`: after the cut renamed the file away, its claim (on `pipeTmp n`, now absent:
  `tmpClaim_absent`) is the one the next `Open` hands back (`pipeTmp (n + 2) = pipeTmp n`): the
  handle's pipeline after `k + 1` cuts.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Handle
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.filePipeline__Open

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Fs

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions]

/-- A whole claim on an absent name is a pipeline claim. -/
theorem tmpClaim_absent (j : Ino) (b : GoString) (h : NamesH) (hb : h.cur !! b = none) :
    osNames (GF := GF) j (.only [b]) (DFrac.own 1) h ⊢ tmpClaim j b := by
  iintro Hn
  iunfold tmpClaim
  iexists h
  iframe Hn
  rw [hb]
  simp only [tmpEnt]
  iempintro

/-- **`w.fp.Open()` from the handle's pipeline.** -/
theorem wp_walPipeH_open
    (wp_Open : go_etcd_io.etcd.server.v3.storage.wal.filePipeline.Open.spec (GF := GF) (hG := hG))
    (fp : Loc) (dir : GoString) (j : Ino) (k : Nat) (hk : k + 2 < 2 ^ 63) :
    {{ walPipeH (GF := GF) fp dir j k }}
      (App (Val (fp @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.filePipeline.ty
        @!! go!"Open")) (Val #()))
    {{ (lf : Loc) (err : GoInterface), RET (PairV #lf #err);
        (⌜err = interface.nil⌝ ∗ ∃ (γ : PipeNames) (R : Roots) (dq : DFrac) (sz : w64)
            (n : Nat), isFilePipe fp γ R dir dq j sz ∗ pipeMain γ (n + 1) ∗ pipeFile j dir n lf ∗
            ⌜n ≤ k⌝) ∨
        ⌜err ≠ interface.nil⌝ }} := by
  iintro %Φ Hp HΦ
  iunfold walPipeH at Hp
  icases Hp with ⟨%γ, %R, %dq, %sz, %n, #Hfp, Hmain, Hc, %hn⟩
  iapply wp_Open fp γ R dir dq j sz n $$ [$Hfp $Hmain Hc]
  · iunfold pipeQ
    iframe Hc
    ipureintro; omega
  inext
  iintro %lf %err Hr
  iapply HΦ
  icases Hr with (⟨%he, Hmain, Hf⟩ | ⟨⟨%he, -⟩, -⟩)
  · ileft
    isplitr
    · ipureintro; exact he
    iexists γ, R, dq, sz, n
    iframe
    isplitl []
    · iexact Hfp
    ipureintro; exact hn
  · iright
    ipureintro; exact he

/-- **The handle's pipeline after a cut**: the claim on the renamed file's name, `pipeTmp n`, is
the one the next `Open` hands back. -/
theorem walPipeH_next (fp : Loc) (dir : GoString) (k : Nat) (γ : PipeNames) (R : Roots)
    (dq : DFrac) (j : Ino) (sz : w64) (n : Nat) (hn : n ≤ k) :
    isFilePipe (GF := GF) fp γ R dir dq j sz ∗ pipeMain γ (n + 1) ∗ tmpClaim j (pipeTmp n) ⊢
      walPipeH fp dir j (k + 1) := by
  iintro ⟨#Hfp, Hmain, Hc⟩
  iunfold walPipeH
  iexists γ, R, dq, sz, n + 1
  iframe Hfp Hmain
  rw [show n + 1 + 1 = n + 2 by omega, pipeTmp_add_two]
  iframe Hc
  ipureintro; omega

end iris

end WalFs
end EtcdGrove
end Perennial
