/-
**The apply thread's resources at a restart's start** (R2d' probe, step 4, 2026-11-06; DRAFT:
nothing here is frozen, `notes/restart-plan.md`, "R2d' Scope (approved 2026-11-06)", its probe).
Lean-first (no Rocq counterpart).

At the etcd pin `673da07c8`, `run` (`server.go:808-830`) reads the raft storage's snapshot
(`sn, err := s.r.raftStorage.Snapshot()`, `server.go:808`) and starts `ep` at its metadata: `confState`
its conf state, `appliedi`, `snapi` (disk and memory) its index, `appliedt` its term. At a first start
that snapshot is empty (`memSnapNone`, `rnSnapOnce` at `ai₀ = 0`); at a restart it is the WAL
snapshot `recoverSnapshot` restored into the `MemoryStorage` (`bootstrap.go:449-478`), at Go's start
index `σ.b` with `σ`'s term and conf state, while the backend's ghost log `A₀` runs through its
consistent index (`bootstrap.go:255-273`).

* `rnSnapOnceR`: `Hsnap`'s restart form (DRAFT, not the hub's text): the snapshot at a given index and
  term, with the conf state reporting the voters after the ghost log `A₀` (`epCsAt`) and a lower
  bound of the storage's snapshot (`memSnapLb γs 0`, under an update: a first start's opens
  `memSnapNone`); today's `rnSnapOnce` gives it at `A₀ = []` (`rnSnapOnceR_first`);
* `srvRestartAtR`: `applyStartC`'s restart form (DRAFT): the ghost rows at `A₀` (the applied index
  `ai₀ + |A₀|`, the KV, the rest buckets, `srvApRes`, the consistent index equal to the ghost index),
  Go's rows at Go's start index `ai`; a first start's `applyStartC` gives it (`srvRestartAtR_first`);
* `applyResR_start`: from them and `ep`'s fields, `applyResR` at Go's handed log `P` (`rp = ⟨|P|, A₀⟩`,
  `P <+: A₀`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.RunR

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`Hsnap`'s restart form** (DRAFT; `rnSnapOnce`'s, `InvRunRes.lean:334`): `run`'s one call of
the raft storage's `Snapshot()` (`server.go:808` at `673da07c8`) answers a snapshot at index `i` and
term `t` whose conf state is read-only and reports the voters after the ghost log `A₀` (`epCsAt γ A₀`:
at a restart the WAL snapshot's `ConfState`, `bootstrap.go:449-478`; nothing at `A₀ = []`), with a
lower bound of the storage's snapshot (`memSnapLb γs 0`, the writers' handle; a first start's from
`memSnapNone`) and the storage's invariant. -/
def rnSnapOnceR (rg : GName) (cl : Cluster) (nk : GName) (ms : Loc) (γs : MemStorNames) (i t : w64)
    (γ : ServerRaftNames) (A₀ : List EntryModel) : IProp GF :=
  iprop(∀ Φ : val → IProp GF,
    ▷ (∀ (sn pm cs : Loc) (sv : SnapshotM),
      ⌜sv.Metadata'.Index' = i ∧ sv.Metadata'.Term' = t ∧ pm ≠ null ∧ cs ≠ null⌝ -∗
      ownSnapM sn DFrac.discard sv -∗
      sn.[go_etcd_io.raft.v3.raftpb.Snapshot, go!"Metadata"] ↦□ pm -∗
      pm.[go_etcd_io.raft.v3.raftpb.SnapshotMetadata, go!"ConfState"] ↦□ cs -∗
      epCsOk cs -∗ epCsAt γ A₀ cs -∗ (|==> memSnapLb γs 0) -∗
      (letI : MemStorReg GF := ⟨rg⟩; memStorInv ms γs cl nk) -∗
      Φ (PairV #sn #(GoInterface.nil))) -∗
    WP (App (Val (ms @!! go.GoType.PointerType go_etcd_io.raft.v3.MemoryStorage.ty @!! go!"Snapshot"))
      (Val #())) {{ Φ }})

/-- **A first start's `Hsnap` gives the restart form at `A₀ = []`**. -/
theorem rnSnapOnceR_first (rg : GName) (cl : Cluster) (nk : GName) (ms : Loc) (γs : MemStorNames)
    (i t : w64) (γ : ServerRaftNames) :
    rnSnapOnce (GF := GF) rg cl nk ms γs i t ⊢ rnSnapOnceR rg cl nk ms γs i t γ [] := by
  iintro H
  iunfold rnSnapOnceR
  iintro %Φ HΦ
  iunfold rnSnapOnce at H
  iapply H
  inext
  iintro %sn %pm %cs %sv %h Hsn Hpm Hcs #Hok Hnone Hinv
  ihave #Hca : epCsAt γ [] cs $$ []
  · iunfold epCsAt; ileft; ipureintro; rfl
  ihave Hlb : iprop(|==> memSnapLb γs 0) $$ [Hnone]
  · iapply (memSnapNone_open (GF := GF) γs) $$ Hnone
  iapply HΦ $$ %sn %pm %cs %sv %h Hsn Hpm Hcs Hok Hca Hlb Hinv

/-- **`applyStartC`'s restart form** (DRAFT): the apply thread's resources when `run` starts at Go's
index `ai` (`ep.appliedi`'s first value, the WAL snapshot's index), with the backend's ghost log
`A₀`: the ghost rows at `A₀` (the applied index `g₀ = ai₀ + |A₀|`, `kvRunM`, `srvRest`, `srvApRes`,
the consistent index `ciEff` at `g₀`, `bootstrap.go:255-273`), Go's at `ai` (`loopOk`, the snapshot
resources). -/
def srvRestartAtR (C : AuthC) (s : Loc) (γ : ApplyNames) (ci : Loc) (b : GoInterface)
    (E : apply.AEnv GF) (γr : ReadNames) (ai₀ c₀ : w64) (x₀ : apply.ApplyKV) (γw : GName)
    (A₀ : List EntryModel) (ai : w64) : IProp GF :=
  iprop(∃ (st₀ : ApplyState) (a t : w64) (f : Bool) (g₀ : w64),
    applyThread γ st₀ ∗
    ⌜loopOk γ st₀ ai ∧ g₀ = ciEff γ st₀.k ∧ uint.Z g₀ = uint.Z ai₀ + A₀.length⌝ ∗
    applyBackend γ ci b ∗ ciApplying ci a t ∗ srvLgReader s ∗ srvBemuReaderAt s E.γbe ∗
    srvWgReader s ∗ srvApplyKVC C s E γw x₀ srvAuthSt0 ∗
    srvAppliedOwn γr g₀ ∗ appliedLogAt γr g₀ x₀.log ∗ kvRunM C.isOn γr ai₀ c₀ A₀ x₀ srvAuthSt0 ∗
    srvRest E γr A₀ ∗ srvApRes s γr A₀ ∗ srvForceSnapAddr s ↦ f ∗ acTok C (ciEff γ st₀.k) ∗
    srvSnapOwn s ci E γr γ ai)

/-- **A first start's `applyStartC` is the restart form at `A₀ = []`** (Go's index `ai₀`). -/
theorem srvRestartAtR_first (C : AuthC) (s : Loc) (γ : ApplyNames) (ci : Loc) (b : GoInterface)
    (E : apply.AEnv GF) (γr : ReadNames) (ai₀ c₀ : w64) (x₀ : apply.ApplyKV) (γw : GName) :
    applyStartC (GF := GF) C s γ ci b E γr ai₀ c₀ x₀ γw ∗ ⌜c₀ = ai₀⌝ ⊢
      srvRestartAtR C s γ ci b E γr ai₀ c₀ x₀ γw [] ai₀ := by
  iintro ⟨H, %hc⟩
  iunfold applyStartC at H
  icases H with ⟨%st₀, %a, %t, %f, Hth, %Hok, Hbe, Hca, Hlg, Hbm, Hwg, Hkv, Hao, Hal, Hkr, Hrest,
    Hap, Hfs, Htok, Hso⟩
  iunfold srvRestartAtR
  iexists st₀, a, t, f, ai₀
  iframe Hth Hbe Hca Hlg Hbm Hwg Hkv Hao Hal Hkr Hrest Hap Hfs Htok Hso
  ipureintro
  exact ⟨Hok.1, by rw [← hc]; exact Hok.2, by simp⟩

end defs

section start
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `kvRunM`'s log is committed (`r2d-prime`'s `kvRunM_lb`, `RunWindow.lean:212`). -/
theorem kvRunM_lbR (on : Bool) (γr : ReadNames) (ai₀ c₀ : w64) (A : List EntryModel)
    (x : apply.ApplyKV) (st : auth.AuthState) :
    kvRunM (GF := GF) on γr ai₀ c₀ A x st ⊢ srvRLogLb γr.raft A ∗ kvRunM on γr ai₀ c₀ A x st := by
  refine (persistent_entails_left ?_).trans sep_comm.1
  cases on
  · unfold kvRunM kvRun kvApplied kvAppliedL
    iintro ⟨⟨⟨#H, -⟩, -⟩, -⟩; iexact H
  · unfold kvRunM kvRunAtOn kvAppliedOn kvAppliedLOn
    iintro ⟨⟨⟨#H, -⟩, -⟩, -⟩; iexact H

/-- **The rest buckets at the restart's start**: `srvRest` at the backend's log is `srvRestR` at
Go's handed log `P` (`rp = ⟨|P|, A₀⟩`; inside the window, the replay arm at the model's image). -/
theorem srvRestR_start (E : apply.AEnv GF) (γr : ReadNames) (P A₀ : List EntryModel)
    (hP : P <+: A₀) : srvRest (GF := GF) E γr A₀ = srvRestR E γr ⟨P.length, A₀⟩ P := by
  by_cases h : P.length < A₀.length
  · rw [srvRestR_in _ _ _ _ h]
    unfold restReplay
    simp only [List.drop_length, List.foldl_nil]
    rw [srvRestRp_model]
  · have hl := hP.length_le
    have he : P = A₀ := hP.eq_of_length (by omega)
    subst he
    rw [srvRestR_past _ _ _ _ (Nat.le_refl _)]

/-- **`run`'s loop resources at a restart's start** (R2d' probe, step 4; DRAFT): from the restart
form of `applyStartC` (`srvRestartAtR`, at Go's start index `ai = ai₀ + |P|`), `ep`'s fields as `run`
sets them from the storage's snapshot (`server.go:808-830` at `673da07c8`: `appliedi`, `snapi` and
`diskSnapshotIndex` at `ai`, `appliedt` the handed log's last term, `confState` with what
`rnSnapOnceR` gives: `epCsOk`, `epCsAt` at `A₀`, `memSnapLb γs 0`), and the restart point's facts
(`P <+: A₀`; `A₀`'s entries normal or conf changes; room past `A₀`; `c₀ ≤ ai₀`): `applyResR` at `P`. -/
theorem applyResR_start (K : AuthC) (C : ApplyCtx GF) (TM : MetaCI → IProp GF) (P A₀ : List EntryModel)
    (ai at' : w64) (cs : Loc)
    (hP : P <+: A₀) (hai : uint.Z ai = uint.Z C.ai₀ + P.length) (hlt : lastTermIs P at')
    (hc₀ : uint.Z C.c₀ ≤ uint.Z C.ai₀) (hty : ∀ m ∈ A₀, m.typ = W32 0 ∨ m.typ = W32 1)
    (hbnd : uint.Z C.ai₀ + A₀.length + 1 < 2 ^ 64) (hρ : C.ρ.raft = C.γr.raft) :
    isServerC (GF := GF) K C.s C.γ C.ci TM C.E C.ρ C.γr ∗
      epAppliedIAddr C.ep ↦ ai ∗ epAppliedTAddr C.ep ↦ at' ∗
      epConfStateAddr C.ep ↦ cs ∗ epCsOk cs ∗ epCsAt C.ρ.raft A₀ cs ∗
      epDiskSnapAddr C.ep ↦ ai ∗ epMemSnapAddr C.ep ↦ ai ∗
      rnRaftStorageAddr (srvRAddr C.s) ↦□ C.ms ∗ memSnapLb C.γs 0 ∗
      (∃ kv : GoInterface, srvKVAddr C.s ↦□ kv ∗ txn.isKV kv C.E.s C.E.γ) ∗
      rnWalTokA C.rn (srvRAddr C.s) (1 : Qp).half ∗ (∃ w : Nat, srvWTTaken C.wt.cnt w) ∗
      srvRestartAtR K C.s C.γ C.ci C.b C.E C.γr C.ai₀ C.c₀ C.x₀ C.γw A₀ ai ⊢
    applyResR K C ⟨P.length, A₀⟩ P := by
  iintro ⟨#Hsrv, Hai, Hat, Hcsa, #Hcsok, #Hcsat, Hdsi, Hmsi, #Hms, #Hslb, Hkvf, Hwt, Hwtt, Hrs⟩
  iunfold srvRestartAtR at Hrs
  icases Hrs with ⟨%st₀, %a, %t, %f, %g₀, Hth, %Hok, Hbe, Hca, Hlg, Hbm, Hwg, Hkv, Hao, Hal, Hkr,
    Hrest, Hap, Hfs, Htok, Hso⟩
  obtain ⟨Hloop, Hce, Hg⟩ := Hok
  icases kvRunM_lbR _ _ _ _ _ _ _ $$ Hkr with ⟨#HlbA, Hkr⟩
  have hgh : ghostOf ⟨P.length, A₀⟩ P = A₀ := ghostOf_in ⟨P.length, A₀⟩ P hP
  iunfold applyResR
  iexists ⟨C.γ, TM, C.E, C.b⟩, st₀, ai, at', a, t, cs, C.x₀, srvAuthSt0, g₀
  simp only [hgh]
  rw [← srvRestR_start _ _ P A₀ hP]
  isplitr
  · ipureintro; exact beSucc_refl C.γ C.E
  ihave Hcs : epConfState C.ep cs $$ [Hcsa]
  · iunfold epConfState; iframe Hcsa Hcsok
  ihave Hss : srvSnapState C.s C.ep C.ms C.γs ai (W64 0) $$ [Hdsi Hmsi Hfs]
  · iunfold srvSnapState
    iexists ai, ai, f
    iframe Hdsi Hmsi Hfs Hms
    isplitr
    · ipureintro; exact ⟨Int.le_refl _, Int.le_refl _⟩
    iExactEq Hslb; rfl
  ihave #HlbA' : srvRLogLb C.ρ.raft A₀ $$ []
  · rw [hρ]; iexact HlbA
  iframe Hsrv Hai Hat Hcs Hcsat Hss Hth Hbe Hca Hlg Hbm Hwg Hkv Hao Hal Hkr Hrest Hap HlbA' Hkvf Hwt
  iframe Hwtt Htok Hso
  ipureintro
  have hl := hP.length_le
  refine ⟨Hloop, hai, Or.inr ⟨?_, ?_⟩, ?_, hlt, Hg, Nat.le_refl _, hty, ?_, hbnd⟩
  · omega
  · rw [← Hce]; omega
  · rw [← Hce]; omega
  · rw [← Hce]; omega

end start

end EtcdGrove
end Perennial
