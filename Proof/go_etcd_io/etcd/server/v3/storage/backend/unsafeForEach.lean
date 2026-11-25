/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/unsafeForEach.lean`. Lean-first (no Rocq
counterpart). Over bbolt's canonical `Tx.Bucket` and `Bucket.ForEach` (proved), through private glue
lemmas into the backend's vocabulary at `theFs`, as `baseReadTx__UnsafeRange.lean`'s (auth-schema-srv
port, 2026-11-19; until then A2's `_kv` axioms `Bucket.ForEach_kvr`/`_kvw`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.unsafeForEach
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBbolt
public import Spec.go_etcd_io.bbolt.Tx__Bucket
public import Spec.go_etcd_io.bbolt.Bucket__ForEach

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend backend

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [go_etcd_io.bbolt.Assumptions]

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt backend Fs in
/-- bbolt's canonical `Tx.Bucket` in the backend's vocabulary, at `theFs`, at any view. -/
private theorem bbolt.kvGlue_Tx__Bucket (h : ∀ [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
, bbolt.Tx.Bucket.spec (GF := GF) (hG := hG)) :
  ∀ (tx : Loc) (γ : DBNames) (q : Qp) (T : bbolt.TxView) (name : GoSlice) (n : GoString) (dq : DFrac),
  (T.rw = true → q = 1) →
  {{ txLive (GF := GF) tx γ q T ∗ name ↦*{dq} n }}
    (App (Val (tx @!! go.GoType.PointerType go_etcd_io.bbolt.Tx.ty @!! go!"Bucket")) (Val #name))
  {{ (b : Loc), RET #b; txLive tx γ q T ∗ name ↦*{dq} n ∗
      ((⌜T.cur.lookup n = none ∧ b = Loc.null⌝) ∨
       (⌜T.cur.lookup n ≠ none ∧ b ≠ Loc.null⌝ ∗ wBkt tx γ b n (T.gen n))) }} := by
  intro tx γ q T name n dq hq
  rcases hfs : theFs GF with _ | ⟨Sx, okx, hasx, fax, fsax, nex⟩
  · simp only [backend.txLive, backend.wBkt, onFs_none hfs]
    iintro %Φ ⟨H, -⟩ HΦ
    iexfalso; iexact H
  · simp only [backend.txLive, backend.wBkt, onFs_some hfs]
    iintro %Φ ⟨Hl, Hn⟩ HΦ
    wp_apply (h tx γ q T name n dq) $$ [$Hl $Hn] as %b ⟨Hl, Hn, Hr⟩
    · ipureintro; exact hq
    iapply HΦ; iframe Hl Hn
    iexact Hr

/-- bbolt's canonical `Bucket.ForEach` in the backend's vocabulary, at `theFs`: the visitor's
`curAt` of an entry is its two slices. -/
private theorem bbolt.kvGlue_Bucket__ForEach (h : ∀ [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
, bbolt.Bucket.ForEach.spec (GF := GF) (hG := hG)) :
  ∀ (tx : Loc) (γ : DBNames) (q : Qp) (T : bbolt.TxView) (b : Loc) (n : GoString) (m : backend.BktData)
    (fn : GoFunc) (I : Nat → IProp GF) (E : Nat → GoInterface → IProp GF),
  T.cur.lookup n = some m →
  {{ txLive (GF := GF) tx γ q T ∗ wBkt tx γ b n (T.gen n) ∗ I 0 ∗
      □ (∀ (i : Nat) (e : Ent) (k v : GoSlice), ⌜(backend.bktEnts m)[i]? = some e⌝ →
          {{ I i ∗ txLive tx γ q T ∗ ⌜k ≠ slice.nil⌝ ∗ backend.txBytes tx γ k e.1 ∗ backend.txBytes tx γ v e.2 }}
            (App (App (Val #fn) (Val #k)) (Val #v))
          {{ (err : GoInterface), RET #err; txLive tx γ q T ∗
              ((⌜err = GoInterface.nil⌝ ∗ I (i + 1)) ∨ (⌜err ≠ GoInterface.nil⌝ ∗ E i err)) }}) }}
    (App (Val (b @!! go.GoType.PointerType go_etcd_io.bbolt.Bucket.ty @!! go!"ForEach")) (Val #fn))
  {{ (err : GoInterface), RET #err; txLive tx γ q T ∗
      ((⌜err = GoInterface.nil⌝ ∗ I (backend.bktEnts m).length) ∨
       (∃ i : Nat, ⌜err ≠ GoInterface.nil ∧ i < (backend.bktEnts m).length⌝ ∗ E i err)) }} := by
  intro tx γ q T b n m fn I E hm
  rcases hfs : theFs GF with _ | ⟨Sx, okx, hasx, fax, fsax, nex⟩
  · simp only [backend.txLive, backend.wBkt, onFs_none hfs]
    iintro %Φ ⟨H, -⟩ HΦ
    iexfalso; iexact H
  · simp only [backend.txLive, backend.wBkt, backend.txBytes, backend.bktEnts_eq, onFs_some hfs]
    iintro %Φ ⟨Hl, #Hb, HI, #Hf⟩ HΦ
    wp_apply (h tx γ q T b n m fn I E) $$ [$Hl $Hb $HI] as %err ⟨Hl, Hr⟩
    · isplitr
      · ipureintro; exact hm
      iintro !> %i %k %v !> %Ψ ⟨%Hi, HI, #Hc, Hl⟩ HΨ
      obtain ⟨e, he⟩ : ∃ e, (bbolt.bktEnts m)[i]? = some e :=
        ⟨_, List.getElem?_eq_getElem Hi⟩
      unfold bbolt.curAt
      rw [he]
      icases Hc with ⟨%Hk, #Hk1, #Hv1⟩
      iapply Hf $$ %i %e %k %v %he %Ψ [HI Hl] HΨ
      iframe; iframe #
      ipureintro; exact Hk
    iapply HΦ
    iframe

private theorem bktEnts_bktOf_none {D : Data} {n : GoString} (h : D.lookup n = none) :
    bktEnts (bktOf D n) = [] := by
  unfold bktOf bktEnts; rw [h]; simp [GMap.toList_empty]

theorem backend.unsafeForEach.wp_proof
    (hB : ∀ [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
, bbolt.Tx.Bucket.spec (GF := GF) (hG := hG))
    (hF : ∀ [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
, bbolt.Bucket.ForEach.spec (GF := GF) (hG := hG)) :
    backend.unsafeForEach.spec (GF := GF) (hG := hG) := by
  replace hB := bbolt.kvGlue_Tx__Bucket hB
  replace hF := bbolt.kvGlue_Bucket__ForEach hF
  intro tx γd q T bk bi fn I E hq
  wp_start as ⟨Hown, #Hbk, HI, #Hf⟩
  unfold isBucket
  icases Hbk with ⟨%bo, %Hbo, #-, #HName, #-⟩
  subst Hbo
  wp_auto
  wp_apply HName as %ns #Hns
  wp_apply (hB tx γd q T ns bi.name DFrac.discard hq) $$ [$Hown $Hns] as %b ⟨Hown, -, Hbr⟩
  icases Hbr with (%Hn | ⟨%Hn, #Hwb⟩)
  · obtain ⟨Hn, rfl⟩ := Hn
    wp_auto
    iapply HΦ
    iframe
    ileft
    rw [bktEnts_bktOf_none Hn]
    iframe
    ipureintro; rfl
  obtain ⟨Hn, Hnn⟩ := Hn
  obtain ⟨m, Hm⟩ : ∃ m, T.cur.lookup bi.name = some m := Option.ne_none_iff_exists'.mp Hn
  have hbm : bktOf T.cur bi.name = m := by unfold bktOf; rw [Hm]; rfl
  rw [hbm]
  wp_if_destruct
  · exact absurd rfl Hnn
  wp_apply (hF tx γd q T b bi.name m fn I E Hm) $$ [$Hown $Hwb $HI $Hf] as %err ⟨Hown, Hres⟩
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
