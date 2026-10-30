/-
**M2's restore chain, the backend part: item 37, the view widening (Draft)** (`notes/m2-storage-plan.md`,
"The restore chain, backend part (branch m2-backend)"). Imported by nothing; no `axiom`, no `sorry`;
nothing switched.

**What item 37 asks** (review round 4, A1 (c)): after `Restore`, the store's writer holds the backend
view of the full log's `Key` bucket (`bucketMap L'`), while the opened image's backend view is the
thinned bucket (`bucketOfEnts ents`, `entsCutAt`): a backend law widening the clients' view `vd` to
`vd'`, where every key of `vd'` missing from `vd` is registered deletable (`thinV γ vd vd'`, the same
shape as the compaction's own physical-thin-of-logical relation).

**Round 4's shape, a ghost law at the open, is not provable (and is refutable)**: the clients hold
half of the view's ghost (`bView γ 1 vd`: `ghostVar γ.view ½ vd`); the other half is two quarters
held in the *lock* resources (`readTx.mu`'s `rtRes`, `viewQ … L`, and the batch lock's
`batchViewQ`), which no ghost update can reach. A law `bView γ 1 vd ∗ thinV γ vd vd' ⊢ |==> bView γ 1
vd'` (`viewWidenGhost_stmt`) would leave the quarters at `vd` and the clients' half at `vd'`: the
next `Unlock` put session, which combines the three (`ReadSide.lean`'s three-share update), derives
`vd = vd'`, i.e. `False` whenever the widening adds a key. Only an operation holding both locks can
widen.

**The drafted repair, `Unlock`'s put branch widened** (`Unlock.specW`): the put session gives the
clients' whole view `vd` and gets it back at `relog P vd' st` for any `vd'` of which `vd` is thin
(`thinV γ vd vd'`); at `vd' = vd` it is today's (`Unlock.spec_of_specW`, proved). Its proof is
today's `Unlock` proof with `thinV_trans` at the readers' and the cached states' views (`thinV phys
vd`, `thinV γ vd vd'`); **not proved here**. It does not by itself serve `Restore`: `restore()` runs
a put session only when it resumes a compaction (`updateCompactRev`'s `UnsafePut`); off that path the
first put session on the new backend is the store's next write, after `Restore` returned. So either
mvcc's writer carries the pending widening until its first `Unlock`, or (no backend change) mvcc's
writer relation is generalized to "the backend's logical view is thin of the log's bucket"
(`thinV γB (keyView⁻¹ (bucketMap L)) vd`), as the backend's physical view already is of its logical
one. The choice is the restore chain's (mvcc); see the plan section.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__Unlock

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend backend

section draft
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- **Round 4's item 37, as a ghost law** (Draft; **refutable**, the module docstring): the clients'
whole view widened by keys registered deletable, with no lock held. Stated to record why it is not
the repair: the view's other half lives in the two locks' resources. -/
def backend.viewWidenGhost_stmt : Prop :=
  ∀ (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc) (vd vd' : VData),
    isBackend γ P W Pk b ∗ bView γ 1 vd ∗ thinV γ vd vd' ⊢ |={⊤}=> bView γ 1 vd'

/-- **Item 37, drafted as `Unlock`'s put branch widened**: today's `Unlock.spec`, the put session
getting the clients' view back at `relog P vd' st` for a `vd'` of which the given view `vd` is thin
(the keys added registered deletable). Not proved (the module docstring). -/
abbrev backend.batchTxBuffered.Unlock.specW : Prop :=
  ∀ (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc) (t : Loc) (st : BSess) (Q : IProp GF),
  st.cnt.hw = false → sint.Z st.pend + P.hookMax < 2 ^ 58 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ P W Pk b ∗
      bF go!"batchTx" b ↦□ t ∗ batchLocked γ P b st ∗ wbTok γ ∗
      ((thinV γ (sData P st.S) (vData P (st.C, st.R)) ∗
         ⌜∀ n i, P.BT.lookup n = some i → P.HB n = false → bkOf st.W.bks i = []⌝ ∗ W ∗ Pk ∗ Q) ∨
       (∃ vd vd' : VData, bView γ 1 vd ∗ thinV γ vd vd' ∗ Pk ∗
          (bView γ 1 (relog P vd' st) -∗ W ∗ Q))) }}
    (App (Val (t @!! go.GoType.PointerType batchTxBuffered.ty @!! go!"Unlock")) (Val #()))
  {{ RET #(); Q }}

/-- **At no widening, today's `Unlock`** (`vd' = vd`, `thinV_refl`). -/
theorem backend.batchTxBuffered.Unlock.spec_of_specW
    (h : backend.batchTxBuffered.Unlock.specW (GF := GF) (hG := hG)) :
    backend.batchTxBuffered.Unlock.spec (GF := GF) (hG := hG) := by
  intro γ P W Pk b t st Q hhw hroom
  iintro %Φ ⟨#Hpkg, #Hb, #Ht, Hl, Hwb, Hbr⟩ HΦ
  iapply (h γ P W Pk b t st Q hhw hroom) $$ [Hl Hwb Hbr] HΦ
  iframe Hpkg Hb Ht Hl Hwb
  icases Hbr with (Hd | ⟨%vd, Hv, HPk, Hk⟩)
  · ileft; iexact Hd
  · iright
    iexists vd, vd
    iframe Hv HPk Hk
    iapply thinV_refl

end draft

end EtcdGrove
end Perennial
