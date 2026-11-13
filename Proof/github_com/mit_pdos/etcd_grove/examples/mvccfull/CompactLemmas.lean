/-
The writer's compaction (`runner.compact`): the model's step and the update at the member's
incarnation invariant. Lean-first (no Rocq counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.WriterLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section model
variable [GooseExts]

/-- **A compaction's model step**: no revision, the leases and the grants unchanged; the
compaction revision and the compactions raised if it compacts (above the last, at most the
current revision). -/
theorem runM_compact (ks : List GoString) (ops : List OpM) (n : Nat) (o : OpM)
    (ho : ops[n]? = some o) (hk : o.kind = kCompact) :
    (runM ks ops (n + 1)).hs = (runM ks ops n).hs ∧
    (runM ks ops (n + 1)).leases = (runM ks ops n).leases ∧
    (runM ks ops (n + 1)).granted = (runM ks ops n).granted ∧
    (runM ks ops (n + 1)).crev =
      (if (runM ks ops n).crev < sint.Z o.rev ∧ sint.Z o.rev ≤ ((runM ks ops n).rev : Int)
        then sint.Z o.rev else (runM ks ops n).crev) ∧
    (runM ks ops (n + 1)).comps =
      (if (runM ks ops n).crev < sint.Z o.rev ∧ sint.Z o.rev ≤ ((runM ks ops n).rev : Int)
        then (runM ks ops n).comps ++ [o.rev] else (runM ks ops n).comps) := by
  rw [runM_succ ks ops n o ho]
  generalize runM ks ops n = s
  have hp : (opPend ks s o).chs = [] := by
    unfold opPend
    simp [hk]
  have hh : histAfter s.hs (opPend ks s o) = s.hs := by unfold histAfter; simp [hp]
  unfold opStep
  simp only [hh, hk]
  refine ⟨trivial, ?_, ?_, ?_, ?_⟩ <;> simp

/-- **The member's state after a compaction**: its state before, compacted if it compacts. -/
theorem σOf_compact (ks : List GoString) (ops : List OpM) (n : Nat) (o : OpM)
    (ho : ops[n]? = some o) (hk : o.kind = kCompact) :
    σOf ks ops (n + 1) =
      (if (σOf ks ops n).crev < sint.Z o.rev ∧ sint.Z o.rev ≤ ((σOf ks ops n).rev : Int)
        then (σOf ks ops n).compactTo (sint.Z o.rev) else σOf ks ops n) ∧
    revAfter ks ops (n + 1) = revAfter ks ops n ∧
    cmpAfter ks ops (n + 1) = (σOf ks ops (n + 1)).crev ∧
    leasesAfter ks ops (n + 1) = leasesAfter ks ops n ∧
    grantedAfter ks ops (n + 1) = grantedAfter ks ops n ∧
    histAt ks ops (n + 1) = histAt ks ops n ∧
    compsAt ks ops (n + 1) =
      (if (σOf ks ops n).crev < sint.Z o.rev ∧ sint.Z o.rev ≤ ((σOf ks ops n).rev : Int)
        then compsAt ks ops n ++ [o.rev] else compsAt ks ops n) := by
  obtain ⟨hh, hl, hg, hc, hcs⟩ := runM_compact ks ops n o ho hk
  have hr : ((σOf ks ops n).rev : Int) = ((runM ks ops n).rev : Int) := by rw [σOf_rev]
  have hcr : (σOf ks ops n).crev = (runM ks ops n).crev := rfl
  refine ⟨?_, ?_, rfl, hl, hg, hh, ?_⟩
  · rw [hcr, hr]
    unfold σOf histAt cmpAfter
    rw [hh, hc]
    split <;> rfl
  · unfold revAfter MSt.rev; rw [hh]
  · unfold compsAt; rw [hcs, hcr, hr]

theorem bndOk_compact (ks : List GoString) (σ : MvccState) (b : Bnd) (Hl : List HRev) (c : Int)
    (hok : bndOk ks σ b Hl) (hc : σ.crev < c) (hcb : c ≤ sint.Z b.2.2.2) :
    bndOk ks (σ.compactTo c) b Hl := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hok
  exact ⟨h1, h2, h3, h4, h5, by show sint.Z b.2.2.1 ≤ c; omega, hcb, by show -1 ≤ c; omega, h9, h10⟩

end model

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- The writer's lessor only sees the store state's log. -/
theorem lessorW_log [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
    (γk : MvccName) (bk : mvcc.KBReal) (f : GoFunc) (lp : Loc) (L U : List w64)
    (σ σ' : MvccState) (h : σ.log = σ'.log) :
    lessorW (GF := GF) γk bk f lp L U σ ⊢ lessorW γk bk f lp L U σ' := by
  unfold lessorW; rw [h]

/-- **The member's part after a compaction** (its count one more, the bounds `b'`): from its parts
at the count before, the compaction revision field and the incarnation's state after. -/
theorem memCore_compact [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
    (ks : List GoString) (γh : HistNames) (ops : List OpM) (i : Nat) (mp : Loc) (m : MemberNames)
    (f : GoFunc) (v : MemS) (qw : Qp) (nw k : Nat) (o : OpM) (b' : Bnd)
    (ho : ops[v.ops]? = some o) (hk : o.kind = kCompact) :
    let n := v.ops
    (mF go!"id" mp ↦□ (W64 (i : Int)) ∗ mF go!"hook" mp ↦□ f ∗ hookOk mp f ∗
      mF go!"path" mp ↦ v.path ∗
      mF go!"be" mp ↦ (interface.mkOk
        (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #v.bk.be :
          GoInterface) ∗
      mF go!"le" mp ↦ lease.lessorIface v.lp ∗ mF go!"kv" mp ↦{DFrac.own qw} v.kv ∗
      mF go!"rev" mp ↦ (W64 (revAfter ks ops n : Int)) ∗
      mF go!"cmp" mp ↦ (W64 (cmpAfter ks ops (n + 1))) ∗
      (∃ sl : GoSlice, mF go!"leases" mp ↦ sl ∗ sl ↦* leasesAfter ks ops n ∗
        ownSliceCap w64 sl (DFrac.own 1)) ∗
      incW ks γh i mp m v.ι v.kv qw (σOf ks ops (n + 1)) b' ∗
      mvccOpen v.ι.kv ∗ mvccBackend v.ι.kv 1 (etcdStorage v.bk) iprop(True) ∗
      hookIs (etcdStorage v.bk) f ∗ mvccReaders v.ι.kv nw ∗
      bkKeep v.bk v.path k ∗ lessorW v.ι.kv v.bk f v.lp (leasesAfter ks ops n) v.U (σOf ks ops n) ∗
      ⌜∀ id ∈ v.U, id ∈ grantedAfter ks ops n⌝ : IProp GF) ⊢
    memCore ks γh ops i mp m f ⟨v.path, v.lp, v.kv, v.ops + 1, v.bk, v.ι, v.U, b'⟩ qw nw k := by
  intro n
  have hvo : v.ops < ops.length := (List.getElem?_eq_some_iff.1 ho).1
  obtain ⟨hS, hR, -, hL, hG, -, -⟩ := σOf_compact ks ops v.ops o ho hk
  have hlog : (σOf ks ops n).log = (σOf ks ops (n + 1)).log := by
    rw [hS]; split <;> rfl
  iintro ⟨Hid, Hhook, Hhok, Hpath, Hbe, Hle, Hkv, Hrev, Hcmp, Hls, Hinc, Hop, Hmb, Hhis, Hrds, Hbk,
    Hlw, %HU⟩
  iunfold memCore
  dsimp only
  rw [hR, hL, hG]
  iframe Hid Hhook Hhok Hpath Hbe Hle Hkv Hrev Hcmp Hls Hinc Hop Hmb Hhis Hrds Hbk
  isplitr
  · ipureintro; omega
  isplitl [Hlw]
  · iapply lessorW_log _ _ _ _ _ _ _ _ hlog; iexact Hlw
  · ipureintro; exact HU

/-- **`Compact`'s update at a live incarnation** (the writer's halves at `σf` and the bounds `b`,
`cmpHi` at least `c` if it compacts): the state compacted to `c` if `c` is above its compaction
revision and at most its revision, else unchanged; the writer's half with it. -/
theorem compact_au (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG)) (ks : List GoString)
    (γh : HistNames) (i : Nat) (mp : Loc) (m : MemberNames) (ι : IncNames) (kv : GoInterface)
    (qw : Qp) (σf : MvccState) (b : Bnd) (c : Int)
    (hb : σf.crev < c ∧ c ≤ (σf.rev : Int) → c ≤ sint.Z b.2.2.2) :
    isInc (GF := GF) ks γh i mp m ι kv ∗ ghostVar ι.ret qw () ∗ ghostVar m.σ (1 : Qp).half σf ∗
        ghostVar m.bnd (1 : Qp).half b ⊢
      AU <{ ∃∃ (σ : MvccState), mvccState ι.kv σ }> @ ⊤ \ ↑mvccN, ∅
        <{ mvccState ι.kv (if σ.crev < c ∧ c ≤ (σ.rev : Int) then σ.compactTo c else σ),
           COMM (fun (σ : MvccState) => iprop(⌜σ = σf⌝ ∗ ghostVar ι.ret qw () ∗
             ghostVar m.σ (1 : Qp).half
               (if σf.crev < c ∧ c ≤ (σf.rev : Int) then σf.compactTo c else σf) ∗
             ghostVar m.bnd (1 : Qp).half b)) σ }> := by
  haveI := memberInv_timeless hpers ks γh mp m ι
  have Hm := memberN_mask i
  unfold isInc
  iintro ⟨⟨#Hinv, -, -⟩, Hret, Hσw, Hbw⟩
  iauintro
  unfold atomic_acc
  iinv Hinv with >Hi Hclose
  iunfold memberInv at Hi
  icases Hi with (Hs | Hr)
  rotate_left
  · icombine Hret Hr gives %Hq0
    obtain ⟨Hq, -⟩ := Hq0
    exfalso
    have h := Qp.le_iff.mp Hq
    simp only [Qp.val_add, Qp.val_one] at h
    have := qw.2
    grind
  iunfold memberState at Hs
  icases Hs with ⟨%σ, %b0, %Hl, Hs, Hσi, Hrl, Hrh, Hcl, Hch, Hbi, Hrev, Hcrev, Hnrev, #Hlb, %Hp⟩
  ihave %Hag := ghostVar_agree m.σ _ _ _ _ $$ Hσi Hσw
  ihave %Hagb := ghostVar_agree m.bnd _ _ _ _ $$ Hbi Hbw
  subst Hag Hagb
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ (⊤ \ ↑mvccN) \ ↑(memberN i) from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists σ
  iframe Hs
  isplit
  · iintro Hs
    imod Hclose2 with -
    imod Hclose $$ [Hs Hσi Hrl Hrh Hcl Hch Hbi Hrev Hcrev Hnrev] with -
    · inext; iunfold memberInv; ileft; iunfold memberState; iexists σ, b0, Hl; iframe; iframe #
      ipureintro; exact Hp
    imodintro
    iframe
  · iintro Hs
    imod Hclose2 with -
    by_cases hcok : σ.crev < c ∧ c ≤ (σ.rev : Int)
    · simp only [hcok, and_self, ↓reduceIte]
      have hok' := bndOk_compact ks σ b0 Hl c Hp hcok.1 (hb hcok)
      imod ghostVar_update_halves (σ.compactTo c) m.σ _ _ $$ Hσi Hσw with ⟨Hσi, Hσw⟩
      imod mono_nat_own_update (Int.toNat ((σ.compactTo c).crev + 1))
        (by show Int.toNat (σ.crev + 1) ≤ Int.toNat (c + 1); omega) $$ Hcrev with ⟨Hcrev, -⟩
      imod Hclose $$ [Hs Hσi Hrl Hrh Hcl Hch Hbi Hrev Hcrev Hnrev] with -
      · inext; iunfold memberInv; ileft; iunfold memberState; iexists σ.compactTo c, b0, Hl
        iframe; iframe #
        ipureintro; exact hok'
      imodintro
      iframe
    · simp only [hcok, ↓reduceIte]
      imod Hclose $$ [Hs Hσi Hrl Hrh Hcl Hch Hbi Hrev Hcrev Hnrev] with -
      · inext; iunfold memberInv; ileft; iunfold memberState; iexists σ, b0, Hl; iframe; iframe #
        ipureintro; exact Hp
      imodintro
      iframe

end lemmas

end mvccfull
end EtcdGrove
end Perennial
