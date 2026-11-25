/-
**kvnet's crash corollary from the general one** (etcd-dist D4c; proved, untrusted): `NetFsBridge.lean`'s
`robust_of_netFsBoot_addrs` (over `kvraftExts = [netExt, fsExt]` at `fs_semantics`), re-derived from
`DistCrashAdequacy.lean`'s `robust_of_dist_crash_adequacy_fs` with the file extension's crash premise `True` and nothing
else in the crash resources (`kvraft_crashStart_split`: the net extension's are `emp`), the initial
states' conditions from `kvraftInitCompat`, and each machine's `FsInit` from `fs_semantics`' `initLocal`.
So kvnet's `kvraft_robust` (kvnet's `raft_kvnet_robust` until the rename, 2026-11-25) could use the general corollary unchanged: its `CrashBootWp`/`StableBootWp`
obligations give the general ones (`crashBootWpG_of_crashBoot`, `stableBootWpG_of_stableBoot`).
-/
module

public import Net.Statement.NetFsBridge
public import Net.Statement.DistCrashAdequacy

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

namespace Net

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Robustness NetFs

attribute [local instance] kvraftExts kvraftExtsSemantics kvraftExtsInterp kvraftExtsCrashInterp
  kvraftExts_hasNet kvraftExts_hasFs GooseGlobalGS.gooseInvGS

section kvnet
variable [GoGlobalContext] {GF : BundledGFunctors} [hPre : GooseGpreS GF]

/-- The crash resources of `[netExt, fsExt]` split as `robust_of_dist_crash_adequacy_fs` asks: the file
extension's, at the crash premise `True`, and nothing else. -/
theorem kvraft_crashStart_split (L L' : GooseLocalGS GF) :
    extsCrashStart L L' ⊢
      Fs.osCrashStart (fun _ _ => True) (Fs.gooseOsGS (L := L)) (Fs.gooseOsGS (L := L')) ∗
        iprop(True) := by
  iintro H
  ihave H' := kvraft_fs_crashStart L L' $$ H
  isplitl [H']
  · iexact H'
  · itrivial

/-- kvnet's crash obligation gives the general one (no use of the bounds, nothing taken from `X`). -/
theorem crashBootWpG_of_crashBoot [lctx : GoLocalContext] [G : GooseGlobalGS .hasLC GF]
    (lo bound : Nat) (e : Expr) (P : GooseLocalGS GF → IProp GF) (H : CrashBootWp e P) :
    CrashBootWpG (fun _ _ => True) (fun _ _ => iprop(True)) lo bound e P := by
  intro L hL _ _ _
  iintro HP Htok
  imod H L hL $$ HP Htok with ⟨Hwp, Hcr⟩
  imodintro
  iframe Hwp
  iintro %L' %V' Hcrd Hinv Hr - Hgs Hlc
  iapply Hcr $$ %L' %V' Hcrd Hinv Hr Hgs Hlc

/-- kvnet's stable obligation gives the general one (`fsStartRes` is `fsStartResG` at `kvraftExts`). -/
theorem stableBootWpG_of_stableBoot [lctx : GoLocalContext] [G : GooseGlobalGS .hasLC GF]
    (lo bound : Nat) (e : Expr) (σ : state) (P : IProp GF) (H : StableBootWp e σ P) :
    StableBootWpG lo bound e σ P :=
  fun L hL _ _ _ => H L hL

/-- **`robust_of_netFsBoot_addrs`, from `robust_of_dist_crash_adequacy_fs`** (same statement). -/
theorem robust_of_netFsBoot_addrs_of_adequacy [lctx : GoLocalContext] (addrs : List GoString)
    (crashing stable : List (Expr × state)) (g : GlobalState) (threads bound : Nat)
    (Hnd : addrs.Nodup) (Hok : ∀ a ∈ addrs, addrOk a = true)
    (Hstart : ∀ [GooseGlobalGS .hasLC GF], receiptBound GF ≤ bound →
      ⊢ ([∗list] a ∈ addrs, addrUnset a) ={⊤}=∗
        ∃ (Pc : Nat → GooseLocalGS GF → IProp GF) (Ps : Nat → IProp GF),
          ⌜∀ (i : Nat) (m : Expr × state), crashing[i]? = some m → CrashBootWp m.1 (Pc i)⌝ ∗
          ⌜∀ (j : Nat) (m : Expr × state), stable[j]? = some m → StableBootWp m.1 m.2 (Ps j)⌝ ∗
          ([∗list] i ↦ m ∈ crashing, ∀ L : GooseLocalGS GF,
            ⌜L.goose_go_local_context = lctx⌝ -∗ fsStartRes L (extLocal Fs.fsExt m.2.world) -∗
            ownGoState (hG := L.goose_go_stateGS) ∅ ={⊤}=∗ Pc i L) ∗
          [∗list] j ↦ _m ∈ stable, Ps j) :
    Robust crashing stable g threads bound := by
  intro hfresh hig hil
  have hfs : ∀ m, m ∈ crashing ++ stable → Fs.FsInit (extLocal Fs.fsExt m.2.world) :=
    fun m hm => (hil m hm).2.1
  refine robust_of_dist_crash_adequacy_fs (GF := GF) (fun _ _ => True) (fun _ _ => iprop(True))
    kvraft_crashStart_split addrs crashing stable g threads bound 0 (Nat.zero_le _) Hnd Hok
    (fun hg hl => ⟨extsInitgP_of_init kvraftInitCompat hg,
      fun m hm => extsInitP_of_init kvraftInitCompat (hl m hm),
      fun m hm => hfs m (List.mem_append_left _ hm)⟩) ?_ hfresh hig hil
  intro G _ hb
  iintro Hs
  imod Hstart hb $$ Hs with ⟨%Pc, %Ps, %HPc, %HPs, Hc, Hst⟩
  imodintro
  iexists Pc, Ps
  iframe Hst
  isplitr
  · ipureintro
    exact fun i m hm => crashBootWpG_of_crashBoot 0 bound m.1 (Pc i) (HPc i m hm)
  isplitr
  · ipureintro
    exact fun j m hm => distBootWpSL_of_stableBootG 0 bound m.1 m.2 (Ps j)
      (hfs m (List.mem_append_right _ (List.mem_of_getElem? hm)))
      (stableBootWpG_of_stableBoot 0 bound m.1 m.2 (Ps j) (HPs j m hm))
  iapply BigSepL.bigSepL_mono ?_ $$ Hc
  intro k m hm
  unfold fsStartResG fsStartRes
  iintro H %L %hL %_ Hr Hgs
  iapply H $$ %L %hL Hr Hgs

end kvnet

end Net
end Perennial
