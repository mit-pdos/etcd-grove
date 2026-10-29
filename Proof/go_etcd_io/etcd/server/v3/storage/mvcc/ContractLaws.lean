/-
**Laws of mvcc's backend contract in its deletable keys** (question 5's switch, the
backend-compaction stage, `notes/backend-cmp-plan.md`; review round 4's R4-4, with R5-3: the slots
`SR`/`SRh` and the right `MW` vary too). The contract `isKeyBackendG` mentions its deletable keys
`Del` in what a read may miss (covariant: `snapThin`, the batch transaction's single-key range) and,
under its compaction condition `Cmp`, in what the compaction job may delete (contravariant). So:

- `isKeyBackendG_weaken`: a contract with compaction and deletable keys implying `Del'` is one
  without compaction (any `Cmp'` that does not hold) over `Del'`, at any slots and right (they occur
  only under `⌜Cmp⌝`: review round 14's F7). With `Del` empty (the backend's `dlNoDel`), the old
  bridge is the new one's instance (`isKeyBackendG_of_backend`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI Iris.ProofMode

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- A thinned snapshot over `Del` is one over any `Del'` that `Del` implies. -/
theorem snapThin_mono (m m' : Bucket) (Del Del' : GoString → IProp GF) :
    snapThin (GF := GF) m m' Del ∗ □ (∀ k, Del k -∗ Del' k) ⊢ snapThin m m' Del' := by
  iintro ⟨Hs, #Hd⟩
  iunfold snapThin at Hs
  iunfold snapThin
  icases Hs with ⟨%Hsub, #Hdel⟩
  isplitr
  · ipureintro; exact Hsub
  iintro !> %k %v %h
  iapply Hd
  iapply Hdel $$ %k %v %h

/-- A snapshot reader over `Del` is one over any `Del'` that `Del` implies. -/
theorem keyReadSnap_monoDel (View : Qp → Bucket → IProp GF) (RT NC : IProp GF)
    (Del Del' : GoString → IProp GF) (rng : Bool) (rt : GoInterfaceOk) (m : Bucket) (L : IProp GF) :
    keyReadSnap (GF := GF) View RT NC Del rng rt m L ∗ □ (∀ k, Del k -∗ Del' k) ⊢
      keyReadSnap View RT NC Del' rng rt m L := by
  iintro ⟨#H, #Hd⟩
  iunfold keyReadSnap at H
  iunfold keyReadSnap
  iintro !> %q %Φ !> Hpre HΦ
  iapply H $$ %q Hpre
  inext
  iintro ⟨Hv, %m', %Rd, %Tok, Htok, #Hl, #Hth⟩
  iapply HΦ
  iframe Hv
  iexists m', Rd, Tok
  iframe Htok Hl
  iapply snapThin_mono
  isplitl
  · iexact Hth
  iintro !>
  iexact Hd

/-- A batch transaction with compaction over `Del` is one without compaction over any `Del'` that
`Del` implies, at any right `MW'` (it occurs only under `⌜Cmp⌝`). -/
theorem batchTxSpecG_weaken (bt : GoInterfaceOk) (View : Qp → Bucket → IProp GF) (RT WT : IProp GF)
    (PutOk : Bucket → Puts → GoString → GoString → Prop) (Del Del' : GoString → IProp GF)
    (W Dep : IProp GF) (Cmp Cmp' : Prop) (Locked : Puts → IProp GF) (P : IProp GF)
    (HF : val → IProp GF) (Rb : GMap GoString backend.BktData → IProp GF) (MW MW' : IProp GF)
    (hC : ¬ Cmp') :
    batchTxSpecG (GF := GF) bt View RT WT PutOk Del W Dep Cmp Locked P HF Rb MW ∗
      □ (∀ k, Del k -∗ Del' k) ⊢
    batchTxSpecG bt View RT WT PutOk Del' W Dep Cmp' Locked P HF Rb MW' := by
  iintro ⟨#H, #Hd⟩
  iunfold batchTxSpecG at H
  iunfold batchTxSpecG
  icases H with ⟨#H1, #H2, #H3, #H4, #H5, #H6, -, -, #H9⟩
  iframe H1 H2 H3 H4 H6 H9
  isplitr
  · iintro !> %l %q %m %b %key %k %dq %Φ !> Hpre HΦ
    iapply H5 $$ %l %q %m %b %key %k %dq Hpre
    inext
    iintro %ks %vs ⟨%Rd, %T, HT, Hback, #Hcap, Hv, Hkey, Hr⟩
    iapply HΦ
    iexists Rd, T
    iframe HT Hback Hcap Hv Hkey
    icases Hr with (Hkv | ⟨Hdk, Hks, Hvs⟩)
    · ileft; iexact Hkv
    · iright
      iframe Hks Hvs
      iapply Hd $$ Hdk
  isplitr
  · iintro !> %hc; exact (hC hc).elim
  iintro !> %hc; exact (hC hc).elim

/-- `batchTxSpecG_weaken` for the batch transaction with its init clauses. -/
theorem isBatchTxG_weaken (bt : GoInterfaceOk) (View : Qp → Bucket → IProp GF) (RT WT : IProp GF)
    (PutOk : Bucket → Puts → GoString → GoString → Prop) (Del Del' : GoString → IProp GF)
    (W Wi Dep : IProp GF) (Cmp Cmp' : Prop) (P : IProp GF) (HF : val → IProp GF)
    (Rb : GMap GoString backend.BktData → IProp GF) (Bt : GoInterfaceOk → IProp GF)
    (MW MW' : IProp GF) (hC : ¬ Cmp') :
    isBatchTxG (GF := GF) bt View RT WT PutOk Del W Wi Dep Cmp P HF Rb Bt MW ∗
      □ (∀ k, Del k -∗ Del' k) ⊢
    isBatchTxG bt View RT WT PutOk Del' W Wi Dep Cmp' P HF Rb Bt MW' := by
  iintro ⟨#H, #Hd⟩
  iunfold isBatchTxG at H
  iunfold isBatchTxG
  icases H with ⟨%Locked, %LockedO, #Hs, #Hi, #Hbt⟩
  iexists Locked, LockedO
  iframe Hi Hbt
  iapply batchTxSpecG_weaken bt View RT WT PutOk Del Del' W Dep Cmp Cmp' Locked P HF Rb MW MW' hC
  isplitl
  · iexact Hs
  iintro !>
  iexact Hd

/-- **The contract without compaction** (review round 14's F7; R4-4 with R5-3): a backend contract
with compaction over `Del` is one without compaction (`¬ Cmp'`) over any `Del'` that `Del` implies,
at any safe-range slots and right (`SR'`, `SRh'`, `MW'`: they occur only under `⌜Cmp⌝`). -/
theorem isKeyBackendG_weaken (b : GoInterface) (View : Qp → Bucket → IProp GF) (RT WT NC : IProp GF)
    (PutOk : Bucket → Puts → GoString → GoString → Prop) (Del Del' : GoString → IProp GF)
    (W Wi Dep : IProp GF) (Cmp Cmp' : Prop) (P : IProp GF) (HF : val → IProp GF)
    (Req : IProp GF → IProp GF → IProp GF) (Rb : GMap GoString backend.BktData → IProp GF)
    (Bt : GoInterfaceOk → IProp GF) (SR SRh MW SR' SRh' MW' : IProp GF) (hC : ¬ Cmp') :
    isKeyBackendG (GF := GF) b View RT WT NC PutOk Del W Wi Dep Cmp P HF Req Rb Bt SR SRh MW ∗
      □ (∀ k, Del k -∗ Del' k) ⊢
    isKeyBackendG b View RT WT NC PutOk Del' W Wi Dep Cmp' P HF Req Rb Bt SR' SRh' MW' := by
  iintro ⟨#H, #Hd⟩
  iunfold isKeyBackendG at H
  iunfold isKeyBackendG
  icases H with ⟨%bi, %Hbi, #Hcrt, #Hrt, #Hbt, #Hfc, #Hsz, #Hszu, -⟩
  iexists bi
  iframe Hfc Hsz Hszu
  isplitr
  · ipureintro; exact Hbi
  isplitr
  · iintro !> %q %m %Φ !> Hpre HΦ
    iapply Hcrt $$ %q %m Hpre
    inext
    iintro %rt ⟨Hv, %L, HL, #Hs⟩
    iapply HΦ
    iframe Hv
    iexists L
    iframe HL
    iapply keyReadSnap_monoDel
    isplitl
    · iexact Hs
    iintro !>
    iexact Hd
  isplitr
  · iintro !> %q %m %Φ !> Hpre HΦ
    iapply Hrt $$ %q %m Hpre
    inext
    iintro %rt ⟨Hv, %L, HL, #Hs⟩
    iapply HΦ
    iframe Hv
    iexists L
    iframe HL
    iapply keyReadSnap_monoDel
    isplitl
    · iexact Hs
    iintro !>
    iexact Hd
  isplitr
  · iintro !> %Φ !> Hpre HΦ
    iapply Hbt $$ Hpre
    inext
    iintro %bt #Hb
    iapply HΦ
    iapply isBatchTxG_weaken bt View RT WT PutOk Del Del' W Wi Dep Cmp Cmp' P HF Rb Bt MW MW' hC
    isplitl
    · iexact Hb
    iintro !>
    iexact Hd
  iintro !> %hc; exact (hC hc).elim

/-- **The old bridge's law** (`isKeyBackendG_weaken` with no deletable key: the backend's
`dlNoDel`, review round 14's F7). -/
theorem isKeyBackendG_weaken_noDel (b : GoInterface) (View : Qp → Bucket → IProp GF)
    (RT WT NC : IProp GF) (PutOk : Bucket → Puts → GoString → GoString → Prop)
    (Del Del' : GoString → IProp GF) (W Wi Dep : IProp GF) (Cmp Cmp' : Prop) (P : IProp GF)
    (HF : val → IProp GF) (Req : IProp GF → IProp GF → IProp GF)
    (Rb : GMap GoString backend.BktData → IProp GF) (Bt : GoInterfaceOk → IProp GF)
    (SR SRh MW SR' SRh' MW' : IProp GF) (hC : ¬ Cmp') :
    isKeyBackendG (GF := GF) b View RT WT NC PutOk Del W Wi Dep Cmp P HF Req Rb Bt SR SRh MW ∗
      □ (∀ k, Del k -∗ False) ⊢
    isKeyBackendG b View RT WT NC PutOk Del' W Wi Dep Cmp' P HF Req Rb Bt SR' SRh' MW' := by
  iintro ⟨#H, #Hd⟩
  iapply isKeyBackendG_weaken b View RT WT NC PutOk Del Del' W Wi Dep Cmp Cmp' P HF Req Rb Bt
    SR SRh MW SR' SRh' MW' hC
  isplitl
  · iexact H
  iintro !> %k Hk
  iexfalso
  iapply Hd $$ Hk

/-! ### Equivalent deletable keys, up to `◇` (`isKeyBackendG_congrDel`) -/

/-- `◇` out of a wand with a pure premise. -/
theorem except0_pure_wand (φ : Prop) (Q : IProp GF) : (⌜φ⌝ -∗ ◇ Q) ⊢ ◇ (⌜φ⌝ -∗ Q) := by
  by_cases h : φ
  · iintro H
    ihave HQ := H $$ []
    · ipureintro; exact h
    imod HQ
    imodintro
    iintro -
    iexact HQ
  · iintro -
    imodintro
    iintro %hφ
    exact (h hφ).elim

/-- A thinned snapshot over `Del` is one over `Del'` up to `◇` when each `Del k` gives `◇ Del' k`. -/
theorem snapThin_congr (m m' : Bucket) (Del Del' : GoString → IProp GF) :
    snapThin (GF := GF) m m' Del ∗ □ (∀ k, Del k -∗ ◇ Del' k) ⊢ ◇ snapThin m m' Del' := by
  iintro ⟨Hs, #Hd⟩
  iunfold snapThin at Hs
  iunfold snapThin
  icases Hs with ⟨%Hsub, #Hdel⟩
  ihave H3 : ◇ □ (∀ k v, ⌜m.lookup k = some v ∧ m'.lookup k = none⌝ -∗ Del' k) $$ []
  · iapply except0_intuitionistically
    iintro !>
    iapply except0_forall.2
    iintro %k
    iapply except0_forall.2
    iintro %v
    iapply except0_pure_wand
    iintro %h
    iapply Hd
    iapply Hdel $$ %k %v %h
  imod H3
  imodintro
  isplitr
  · ipureintro; exact Hsub
  iexact H3

/-- `keyReadSnap_monoDel` up to `◇`. -/
theorem keyReadSnap_congrDel (View : Qp → Bucket → IProp GF) (RT NC : IProp GF)
    (Del Del' : GoString → IProp GF) (rng : Bool) (rt : GoInterfaceOk) (m : Bucket) (L : IProp GF) :
    keyReadSnap (GF := GF) View RT NC Del rng rt m L ∗ □ (∀ k, Del k -∗ ◇ Del' k) ⊢
      keyReadSnap View RT NC Del' rng rt m L := by
  iintro ⟨#H, #Hd⟩
  iunfold keyReadSnap at H
  iunfold keyReadSnap
  iintro !> %q %Φ !> Hpre HΦ
  iapply wp_fupd
  iapply H $$ %q Hpre
  inext
  iintro ⟨Hv, %m', %Rd, %Tok, Htok, #Hl, #Hth⟩
  ihave Hth' := snapThin_congr m m' Del Del' $$ [$Hth]
  · iintro !>; iexact Hd
  imod Hth'
  imodintro
  iapply HΦ
  iframe Hv
  iexists m', Rd, Tok
  iframe Htok Hl Hth'

/-- A batch transaction over `Del` is one over any `Del'` equivalent to it up to `◇`. -/
theorem batchTxSpecG_congrDel (bt : GoInterfaceOk) (View : Qp → Bucket → IProp GF)
    (RT WT : IProp GF) (PutOk : Bucket → Puts → GoString → GoString → Prop)
    (Del Del' : GoString → IProp GF) (W Dep : IProp GF) (Cmp : Prop) (Locked : Puts → IProp GF)
    (P : IProp GF) (HF : val → IProp GF) (Rb : GMap GoString backend.BktData → IProp GF)
    (MW : IProp GF) :
    batchTxSpecG (GF := GF) bt View RT WT PutOk Del W Dep Cmp Locked P HF Rb MW ∗
      □ (∀ k, Del k ∗-∗ ◇ Del' k) ⊢
    batchTxSpecG bt View RT WT PutOk Del' W Dep Cmp Locked P HF Rb MW := by
  iintro ⟨#H, #Hd⟩
  ihave #Hf : (□ (∀ k, Del k -∗ ◇ Del' k) : IProp GF) $$ []
  · iintro !> %k Hk
    icases Hd $$ %k with ⟨#H1, -⟩
    iapply H1 $$ Hk
  ihave #Hb : (□ (∀ k, Del' k -∗ Del k) : IProp GF) $$ []
  · iintro !> %k Hk
    icases Hd $$ %k with ⟨-, #H2⟩
    iapply H2
    imodintro
    iexact Hk
  iunfold batchTxSpecG at H
  iunfold batchTxSpecG
  icases H with ⟨#H1, #H2, #H3, #H4, #H5, #H6, #H7, #H8, #H9⟩
  iframe H1 H2 H3 H4 H6 H8 H9
  isplitr
  · iintro !> %l %q %m %b %key %k %dq %Φ !> Hpre HΦ
    iapply wp_fupd
    iapply H5 $$ %l %q %m %b %key %k %dq Hpre
    inext
    iintro %ks %vs ⟨%Rd, %T, HT, Hback, #Hcap, Hv, Hkey, Hr⟩
    icases Hr with (Hkv | ⟨Hdk, Hks, Hvs⟩)
    · imodintro
      iapply HΦ
      iexists Rd, T
      iframe HT Hback Hcap Hv Hkey
      ileft; iexact Hkv
    · ihave Hdk' := Hf $$ Hdk
      imod Hdk'
      imodintro
      iapply HΦ
      iexists Rd, T
      iframe HT Hback Hcap Hv Hkey
      iright
      iframe Hks Hvs Hdk'
  iintro !> %hc %q %m %b %lo %hi %klo %khi %limit %dqlo %dqhi %hl %Φ !> Hpre HΦ
  iapply wp_fupd
  iapply H7 $$ %hc %q %m %b %lo %hi %klo %khi %limit %dqlo %dqhi %hl Hpre
  inext
  iintro %ks %vs ⟨Hv, Hlo, Hhi, %m', %Rd, %U, HU, #Hth, #Hc1, #Hc2, Hpv, #Hdel, #Hmp, #Hul⟩
  ihave Hth' := snapThin_congr m m' Del Del' $$ [$Hth]
  · iintro !>; iexact Hf
  imod Hth'
  imodintro
  iapply HΦ
  iframe Hv Hlo Hhi
  iexists m', Rd, U
  iframe HU Hth' Hc1 Hc2 Hpv Hmp Hul
  iintro !> %key %k %n %Ψ !> ⟨HK, HU, HDk, #HRd⟩ HΨ
  iapply Hdel $$ %key %k %n [HK HU HDk] HΨ
  iframe HK HU HRd
  iapply Hb $$ HDk

/-- `batchTxSpecG_congrDel` for the batch transaction with its init clauses. -/
theorem isBatchTxG_congrDel (bt : GoInterfaceOk) (View : Qp → Bucket → IProp GF) (RT WT : IProp GF)
    (PutOk : Bucket → Puts → GoString → GoString → Prop) (Del Del' : GoString → IProp GF)
    (W Wi Dep : IProp GF) (Cmp : Prop) (P : IProp GF) (HF : val → IProp GF)
    (Rb : GMap GoString backend.BktData → IProp GF) (Bt : GoInterfaceOk → IProp GF)
    (MW : IProp GF) :
    isBatchTxG (GF := GF) bt View RT WT PutOk Del W Wi Dep Cmp P HF Rb Bt MW ∗
      □ (∀ k, Del k ∗-∗ ◇ Del' k) ⊢
    isBatchTxG bt View RT WT PutOk Del' W Wi Dep Cmp P HF Rb Bt MW := by
  iintro ⟨#H, #Hd⟩
  iunfold isBatchTxG at H
  iunfold isBatchTxG
  icases H with ⟨%Locked, %LockedO, #Hs, #Hi, #Hbt⟩
  iexists Locked, LockedO
  iframe Hi Hbt
  iapply batchTxSpecG_congrDel bt View RT WT PutOk Del Del' W Dep Cmp Locked P HF Rb MW
  isplitl
  · iexact Hs
  iintro !>
  iexact Hd

/-- **The store's deletable keys through the backend's registration** (review round 1's F7; the
Draft's `isKeyBackendG_congrDel.stmt`): a contract over `Del` is one over any `Del'` equivalent to
it up to `◇` (the backend's registration agrees with the store's predicate under `▷`, and the
store's `delKey` is timeless). -/
theorem isKeyBackendG_congrDel (b : GoInterface) (View : Qp → Bucket → IProp GF)
    (RT WT NC : IProp GF) (PutOk : Bucket → Puts → GoString → GoString → Prop)
    (Del Del' : GoString → IProp GF) (W Wi Dep : IProp GF) (Cmp : Prop) (P : IProp GF)
    (HF : val → IProp GF) (Req : IProp GF → IProp GF → IProp GF)
    (Rb : GMap GoString backend.BktData → IProp GF) (Bt : GoInterfaceOk → IProp GF)
    (SR SRh MW : IProp GF) :
    isKeyBackendG (GF := GF) b View RT WT NC PutOk Del W Wi Dep Cmp P HF Req Rb Bt SR SRh MW ∗
      □ (∀ k, Del k ∗-∗ ◇ Del' k) ⊢
    isKeyBackendG b View RT WT NC PutOk Del' W Wi Dep Cmp P HF Req Rb Bt SR SRh MW := by
  iintro ⟨#H, #Hd⟩
  ihave #Hf : (□ (∀ k, Del k -∗ ◇ Del' k) : IProp GF) $$ []
  · iintro !> %k Hk
    icases Hd $$ %k with ⟨#H1, -⟩
    iapply H1 $$ Hk
  iunfold isKeyBackendG at H
  iunfold isKeyBackendG
  icases H with ⟨%bi, %Hbi, #Hcrt, #Hrt, #Hbt, #Hfc, #Hsz, #Hszu, #Hcmp⟩
  iexists bi
  iframe Hfc Hsz Hszu Hcmp
  isplitr
  · ipureintro; exact Hbi
  isplitr
  · iintro !> %q %m %Φ !> Hpre HΦ
    iapply Hcrt $$ %q %m Hpre
    inext
    iintro %rt ⟨Hv, %L, HL, #Hs⟩
    iapply HΦ
    iframe Hv
    iexists L
    iframe HL
    iapply keyReadSnap_congrDel
    isplitl
    · iexact Hs
    iintro !>
    iexact Hf
  isplitr
  · iintro !> %q %m %Φ !> Hpre HΦ
    iapply Hrt $$ %q %m Hpre
    inext
    iintro %rt ⟨Hv, %L, HL, #Hs⟩
    iapply HΦ
    iframe Hv
    iexists L
    iframe HL
    iapply keyReadSnap_congrDel
    isplitl
    · iexact Hs
    iintro !>
    iexact Hf
  iintro !> %Φ !> Hpre HΦ
  iapply Hbt $$ Hpre
  inext
  iintro %bt #Hb
  iapply HΦ
  iapply isBatchTxG_congrDel bt View RT WT PutOk Del Del' W Wi Dep Cmp P HF Rb Bt MW
  isplitl
  · iexact Hb
  iintro !>
  iexact Hd

end laws

end mvcc
end EtcdGrove
end Perennial
