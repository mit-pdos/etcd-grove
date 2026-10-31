/-
**M2, the apply side: the drafted trusted statements** (`notes/m2-apply-plan.md`). Imported by
nothing; no `axiom`, no `sorry`; nothing switched. Generated from today's texts
(`NewServer.lean`, `EtcdServer__Compact.lean`), each change marked `(M2, the apply side, Draft)`:

The switch is stated in place (the user's Q6 (a), 2026-10-30): these texts name the definitions
the switch keeps (`isServerReq`, `isServerRead`, `srvBuilt`, ...) and are read under the redefined
ones (item 1's `dispatchOk`, item 5's `kvInv γ γk := kvInvD γ γk γk.cmp`, item 19's ties
`srvReqFieldsAtD`/`srvKVInvsD`), as at the switch.

- (`NewServer.specD`, in place as `NewServer.spec` since 2026-10-31, item 14: the mode the
  configuration's, the closer without the right `srvKVCloserW`; the Draft's copy gone.)
- `EtcdServer.Compact.specD`: over the general `isServerReq` and `isServerRead` (the compaction
  family's `isServerReqC` gone) in compaction mode; their KV invariants are the mode's through
  item 19's ties.
- **The closer without the right** (`srvKVCloserW`, review round 1's F-6): what `start` keeps for
  the snapshot path once the right has gone to the apply thread (A2), the one the snapshot track's
  `restorePre_of_applyM` takes; `srvKVCloserM_split` (proved): the closer by the mode at `c` is
  `srvKVCloserW` and `apply.cmpRight E c`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.NewServer
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Compact
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.M2ApplyDraft
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.M2StorageDraftRestore

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section closer
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/- (`srvKVCloserW` in place, `InvWatchBuilt.lean`, 2026-10-31.) -/

/-- **`start`'s split** (G5, review round 1's F-6): the closer by the mode at `c` (at least `-1`)
is the closer without the right and the apply thread's compaction right at `c`; and back (for the
server's `Stop` path, or a restore that hands the right back). -/
theorem srvKVCloserM_split (s : Loc) (E : apply.AEnv GF) (c : Int) :
    srvKVCloserM (GF := GF) s E c ∗ ⌜-1 ≤ c⌝ ⊣⊢ srvKVCloserW s E ∗ apply.cmpRight E c := by
  unfold srvKVCloserM srvKVCloserW apply.cmpRight
  by_cases h : mvcc.kbCmpM E.γ.kb
  · simp only [h, ↓reduceIte]
    constructor
    · iintro ⟨⟨%wsl, #Hkv, Hcl⟩, %hc⟩
      icases (mvcc.wsCloserR_iff wsl E.s E.γ c).1 $$ Hcl with ⟨%stc, #Hstc, Hsc, Hw, Hr⟩
      iframe Hr
      isplitl [Hsc Hw]
      · iexists wsl
        iframe Hkv
        iexists stc
        iframe Hstc Hsc Hw
      · ipureintro; exact hc
    · iintro ⟨⟨%wsl, #Hkv, %stc, #Hstc, Hsc, Hw⟩, Hr, %hc⟩
      isplitl [Hsc Hw Hr]
      · iexists wsl
        iframe Hkv
        iapply (mvcc.wsCloserR_iff wsl E.s E.γ c).2
        iexists stc
        iframe Hstc Hsc Hw Hr
      · ipureintro; exact hc
  · simp only [h, ↓reduceIte]
    constructor
    · iintro ⟨⟨Hcl, %hc⟩, -⟩
      iframe Hcl
      ipureintro; exact hc
    · iintro ⟨Hcl, %hc⟩
      iframe Hcl
      isplitr
      · ipureintro; exact hc
      · ipureintro; omega

end closer

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

end spec

end EtcdGrove
end Perennial
