/-
**The KV and its write transaction behind either store** (unit N4, D14a, `notes/decisions.md`).
Lean-first (no Rocq counterpart).

The `mvcc.KV` the etcd server holds is `mvcc.New`'s `*watchableStore`; the txn and apply proofs
read through the plain `*store` it embeds. This file has what lets them run on either:

* **`Read` of a KV over the store `s`** (`kvOver`, `InvStore.lean`): the store's own, or the
  watchable store's promoted method (a load of its `store` field, then `store.Read`):
  `kvOver_Read` is `store.Read`'s spec at either receiver.
* **The write transaction as an interface value** (`twWrap tyX vX mw`): the `*metricsTxnWrite` `mw`
  `store.Write` returns, or the `*watchableStoreTxnWrite` `watchableStore.Write` returns, whose
  embedded `TxnWrite` is `mw` (its struct read-only: `isWatchTxnWrite`). Its `Range`, `Put`,
  `DeleteRange`, `Rev`, `FirstRev`, `Changes` are `mw`'s: the promoted methods load the embedded
  interface and call it (`tw_wp1` … `tw_wp4`, WP transfers, by the methods' arity).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchStore
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__Read

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The write transaction `interface.mkOk tyX vX` over the `*metricsTxnWrite` `mw`**
(persistent): `mw` itself, or a `*watchableStoreTxnWrite` whose embedded `TxnWrite` is `mw` (its
struct read-only). -/
def twWrap (tyX : go.GoType) (vX : val) (mw : Loc) : IProp GF :=
  iprop(⌜tyX = go.GoType.PointerType metricsTxnWrite.ty ∧ vX = #mw⌝ ∨
    ∃ (twl ws : Loc), ⌜tyX = go.GoType.PointerType watchableStoreTxnWrite.ty ∧ vX = #twl⌝ ∗
      twl ↦□ ({ TxnWrite' := interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw,
                s' := ws } : watchableStoreTxnWrite))

instance twWrap_persistent (tyX : go.GoType) (vX : val) (mw : Loc) :
    Persistent (twWrap (GF := GF) tyX vX mw) := by
  unfold twWrap; infer_instance

/-- The `*metricsTxnWrite` itself. -/
theorem twWrap_metrics (mw : Loc) :
    ⊢ twWrap (GF := GF) (go.GoType.PointerType metricsTxnWrite.ty) #mw mw := by
  iunfold twWrap; ileft; ipureintro; exact ⟨rfl, rfl⟩

/-- The two write transactions' types differ. -/
theorem twTy_ne :
    go.GoType.PointerType metricsTxnWrite.ty ≠ go.GoType.PointerType watchableStoreTxnWrite.ty := by
  unfold metricsTxnWrite.ty watchableStoreTxnWrite.ty
  intro h
  simp only [go.GoType.PointerType.injEq, go.GoType.Named.injEq] at h
  exact absurd h.1 (by decide)

/-- **The write transaction is over one `*metricsTxnWrite`.** -/
theorem twWrap_agree (tyX : go.GoType) (vX : val) (mw mw' : Loc) :
    twWrap (GF := GF) tyX vX mw ∗ twWrap tyX vX mw' ⊢ ⌜mw = mw'⌝ := by
  iintro ⟨H1, H2⟩
  iunfold twWrap at H1 H2
  icases H1 with (%H1 | ⟨%twl, %ws, %H1, #Htw⟩) <;>
    icases H2 with (%H2 | ⟨%twl', %ws', %H2, #Htw'⟩)
  · obtain ⟨h1, h2⟩ := H1; obtain ⟨h3, h4⟩ := H2
    subst h1 h2
    ipureintro; exact go.intoVal_inj (V := Loc) h4
  · obtain ⟨h1, -⟩ := H1; obtain ⟨h3, -⟩ := H2
    exact absurd (h1.symm.trans h3) twTy_ne
  · obtain ⟨h1, -⟩ := H1; obtain ⟨h3, -⟩ := H2
    exact absurd (h3.symm.trans h1) twTy_ne
  · obtain ⟨h1, h2⟩ := H1; obtain ⟨h3, h4⟩ := H2
    subst h1 h2
    have e := go.intoVal_inj (V := Loc) h4
    subst e
    icombine Htw Htw' gives %He
    ipureintro
    simp only [watchableStoreTxnWrite.mk.injEq, interface.mkOk, GoInterface.ok.injEq] at He
    obtain ⟨He, -⟩ := He
    injection He with _ h
    exact go.intoVal_inj (V := Loc) h

end defs

section kv
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- A KV over a store is an interface value that is not `nil`. -/
theorem kvOver_ok (kv : GoInterface) (s : Loc) :
    kvOver (GF := GF) kv s ⊢ ⌜∃ (ty : go.GoType) (v : val), kv = interface.mkOk ty v⌝ := by
  iintro H
  iunfold kvOver at H
  icases H with (%H | ⟨%ws, %H, -⟩)
  · ipureintro; exact ⟨_, _, H⟩
  · ipureintro; exact ⟨_, _, H⟩

/-- **`kv.Read(mode, trace)` is the store's `Read`** (a WP transfer): for the watchable store,
the promoted method loads its `store` field. -/
theorem kvOver_read_wp (ty : go.GoType) (v : val) (s : Loc) (mode : w32) (trace : Loc)
    (Φ : val → IProp GF) :
    kvOver (GF := GF) (interface.mkOk ty v) s ∗
      WP (App (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"Read")) (Val #mode))
        (Val #trace)) {{ Φ }} ⊢
      WP (App (App (Val #(methods ty go!"Read" v)) (Val #mode)) (Val #trace)) {{ Φ }} := by
  iintro ⟨Hk, Hwp⟩
  iunfold kvOver at Hk
  icases Hk with (%H | ⟨%ws, %H, #Hst⟩)
  · cases H
    iexact Hwp
  · cases H
    rw [method_unfold (t := go.GoType.PointerType watchableStore.ty) (m := go!"Read")]
    wp_auto
    iexact Hwp

/-- **`kv.Rev()` is the store's `Rev`** (a WP transfer; the watchable store's is promoted from
its embedded `store`). -/
theorem kvOver_rev_wp (ty : go.GoType) (v : val) (s : Loc) (Φ : val → IProp GF) :
    kvOver (GF := GF) (interface.mkOk ty v) s ∗
      WP (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"Rev")) (Val #())) {{ Φ }} ⊢
      WP (App (Val #(methods ty go!"Rev" v)) (Val #())) {{ Φ }} := by
  iintro ⟨Hk, Hwp⟩
  iunfold kvOver at Hk
  icases Hk with (%H | ⟨%ws, %H, #Hst⟩)
  · cases H
    iexact Hwp
  · cases H
    rw [method_unfold (t := go.GoType.PointerType watchableStore.ty) (m := go!"Rev")]
    wp_call
    (try wp_auto)
    iexact Hwp

/-- **`store.Read`'s spec at a KV over the store** (`kvOver_read_wp`). -/
theorem kvOver_Read (hRead : mvcc.store.Read.spec (GF := GF) (hG := hG))
    (ty : go.GoType) (v : val) (s : Loc) (γ : mvcc.StoreNames) (mode : w32) (trace : Loc) (m : Nat)
    (log₀ : mvcc.Log) (te : Bool) (c : Int) (Z : IProp GF) (oa : Option (Qp × mvcc.Log)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
        kvOver (interface.mkOk ty v) s ∗
        mvcc.isStore s γ ∗ mvcc.storeReaderC s γ ∗ □ Z ∗ ownToks γ.revs m ∗ mvcc.idxCert γ.idx log₀ ∗
        mvcc.crevLb γ.idx c ∗ ⌜trace ≠ null⌝ ∗ traceutil.ownTrace trace te ∗
        mvcc.logLent γ.idx oa }}
      (App (App (Val #(methods ty go!"Read" v)) (Val #mode)) (Val #trace))
    {{ (mw : Loc), RET #(interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw);
        ∃ (log : mvcc.Log) (rev : w64) (crev : Int), mvcc.isTxnRead mw s γ trace log rev crev Z ∗
          ownToks γ.revs m ∗ mvcc.crevLb γ.idx crev ∗ mvcc.certOk γ log ∗
          ⌜log₀ <+: log ∧ log.length + m + 3 ≤ 2 ^ 63 ∧ c ≤ crev⌝ ∗ mvcc.logLent γ.idx oa ∗
          ⌜∀ q L, oa = some (q, L) → log = L⌝ }} := by
  iintro %Φ ⟨#Hpkg, #Hk, #Hs, Hrd, #HZ, Hm, #Hc0, #Hlb, %Ht, Htrc, Hla⟩ HΦ
  iapply kvOver_read_wp ty v s mode trace
  iframe Hk
  iapply (hRead s γ mode trace m log₀ te c Z oa) $$ [Hrd Hm Htrc Hla] HΦ
  iframe Hrd Hm Htrc Hla; iframe #; ipureintro; exact Ht

/-! ## The write transaction -/

/-- The promoted methods of the write transaction (those `mw` has, but `End`). -/
def twMethod (M : GoString) : Prop :=
  M = go!"Range" ∨ M = go!"Put" ∨ M = go!"DeleteRange" ∨ M = go!"Rev" ∨ M = go!"FirstRev" ∨
    M = go!"Changes"

/-- **A promoted method of the wrapper is `mw`'s** (one argument, the WP transfer). -/
theorem tw_wp1 (tyX : go.GoType) (vX : val) (mw : Loc) (M : GoString) (hM : twMethod M)
    {A : Type} (a : A) (Φ : val → IProp GF) :
    twWrap (GF := GF) tyX vX mw ∗
      WP (App (Val #(methods (go.GoType.PointerType metricsTxnWrite.ty) M #mw)) (Val #a)) {{ Φ }} ⊢
      WP (App (Val #(methods tyX M vX)) (Val #a)) {{ Φ }} := by
  iintro ⟨Hw, Hwp⟩
  iunfold twWrap at Hw
  icases Hw with (%H | ⟨%twl, %ws, %H, #Htw⟩)
  · obtain ⟨h1, h2⟩ := H; subst h1 h2; iexact Hwp
  · obtain ⟨h1, h2⟩ := H; subst h1 h2
    rcases hM with rfl | rfl | rfl | rfl | rfl | rfl <;>
    · rw [method_unfold (t := go.GoType.PointerType watchableStoreTxnWrite.ty)]
      iStructNamed Htw
      wp_call
      (try wp_auto)
      iexact Hwp

/-- Two arguments. -/
theorem tw_wp2 (tyX : go.GoType) (vX : val) (mw : Loc) (M : GoString) (hM : twMethod M)
    {A B : Type} (a : A) (b : B) (Φ : val → IProp GF) :
    twWrap (GF := GF) tyX vX mw ∗
      WP (App (App (Val #(methods (go.GoType.PointerType metricsTxnWrite.ty) M #mw)) (Val #a))
        (Val #b)) {{ Φ }} ⊢
      WP (App (App (Val #(methods tyX M vX)) (Val #a)) (Val #b)) {{ Φ }} := by
  iintro ⟨Hw, Hwp⟩
  iunfold twWrap at Hw
  icases Hw with (%H | ⟨%twl, %ws, %H, #Htw⟩)
  · obtain ⟨h1, h2⟩ := H; subst h1 h2; iexact Hwp
  · obtain ⟨h1, h2⟩ := H; subst h1 h2
    rcases hM with rfl | rfl | rfl | rfl | rfl | rfl <;>
    · rw [method_unfold (t := go.GoType.PointerType watchableStoreTxnWrite.ty)]
      iStructNamed Htw
      wp_call
      (try wp_auto)
      iexact Hwp

/-- Three arguments. -/
theorem tw_wp3 (tyX : go.GoType) (vX : val) (mw : Loc) (M : GoString) (hM : twMethod M)
    {A B C : Type} (a : A) (b : B) (c : C) (Φ : val → IProp GF) :
    twWrap (GF := GF) tyX vX mw ∗
      WP (App (App (App (Val #(methods (go.GoType.PointerType metricsTxnWrite.ty) M #mw)) (Val #a))
        (Val #b)) (Val #c)) {{ Φ }} ⊢
      WP (App (App (App (Val #(methods tyX M vX)) (Val #a)) (Val #b)) (Val #c)) {{ Φ }} := by
  iintro ⟨Hw, Hwp⟩
  iunfold twWrap at Hw
  icases Hw with (%H | ⟨%twl, %ws, %H, #Htw⟩)
  · obtain ⟨h1, h2⟩ := H; subst h1 h2; iexact Hwp
  · obtain ⟨h1, h2⟩ := H; subst h1 h2
    rcases hM with rfl | rfl | rfl | rfl | rfl | rfl <;>
    · rw [method_unfold (t := go.GoType.PointerType watchableStoreTxnWrite.ty)]
      iStructNamed Htw
      wp_call
      (try wp_auto)
      iexact Hwp

/-- Four arguments. -/
theorem tw_wp4 (tyX : go.GoType) (vX : val) (mw : Loc) (M : GoString) (hM : twMethod M)
    {A B C D : Type} (a : A) (b : B) (c : C) (d : D) (Φ : val → IProp GF) :
    twWrap (GF := GF) tyX vX mw ∗
      WP (App (App (App (App (Val #(methods (go.GoType.PointerType metricsTxnWrite.ty) M #mw))
        (Val #a)) (Val #b)) (Val #c)) (Val #d)) {{ Φ }} ⊢
      WP (App (App (App (App (Val #(methods tyX M vX)) (Val #a)) (Val #b)) (Val #c)) (Val #d))
        {{ Φ }} := by
  iintro ⟨Hw, Hwp⟩
  iunfold twWrap at Hw
  icases Hw with (%H | ⟨%twl, %ws, %H, #Htw⟩)
  · obtain ⟨h1, h2⟩ := H; subst h1 h2; iexact Hwp
  · obtain ⟨h1, h2⟩ := H; subst h1 h2
    rcases hM with rfl | rfl | rfl | rfl | rfl | rfl <;>
    · rw [method_unfold (t := go.GoType.PointerType watchableStoreTxnWrite.ty)]
      iStructNamed Htw
      wp_call
      (try wp_auto)
      iexact Hwp


end kv

end mvcc
end EtcdGrove
end Perennial
