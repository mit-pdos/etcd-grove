/-
**The lessor-window tie at the apply thread** (auth-lease S4 item 7b F4, 2026-11-17): the tie's laws (`WinTie.lean`)
restated over the apply layer's predicates, for the server's wiring.

- `winTieRes E Fr`: what the server's KV invariants hold of the tie (the tie at `E`'s witness, lessor and store names,
  the window token `E.Wt` its `winTok`, and the lessor's reader invariant, which its laws open);
- `envAus_tie`: the store's builders at the environment (`apply.envAus`) at the apply thread's quarter (`E.stq = ¼`),
  the end builder recording the commit in the tie (`au_end_tie`);
- `kvOwn_push`/`applyKV_push`: the apply thread opens an entry's window (`tie_push`), its target the items of the
  committed model log after the entry;
- `kvOwn_free`/`applyKV_free`: the snapshot path's free marker (`tie_free`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.WinTie
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.InvUber

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section
namespace Perennial
namespace EtcdGrove
namespace srvApi
open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc mvcc.api
open go_etcd_io.etcd.server.v3.lease (LeaseItem)
open lease (LWin)

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The tie, as the server's KV invariants hold it** (persistent): the tie at the environment's witness, lessor and
store names, the free markers' fact `Fr`, the apply thread's window token `E.Wt` its `winTok`; and the lessor's reader
invariant (the tie's laws open it). -/
def winTieRes (E : apply.AEnv GF) (Fr : Prop) : IProp GF :=
  iprop(∃ γt : WTNames, ⌜E.Wt = winTok γt⌝ ∗ winTieInv E.Nx Fr (mvccLeases E.γ) E.γs γt ∗
    lease.lessorRdInv (mvccLeases E.γ))

instance winTieRes_persistent (E : apply.AEnv GF) (Fr : Prop) : Persistent (winTieRes (GF := GF) E Fr) := by
  unfold winTieRes; infer_instance

end defs

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **The store's builders at the environment, with the tie** (F4: the server's `envAus`): at the apply thread's
quarter `E.stq = ¼`, the share-generic builders of the store invariant, and the end builder from `au_end_tie`. -/
theorem envAus_tie (Hp : persistent.law (GF := GF)) (Hr : mvccState_reachable.law (GF := GF))
    (E : apply.AEnv GF) (Fr : Prop) (hq : E.stq = (1 : Qp).half.half)
    [hNxP : ∀ l, Persistent (E.Nx l)] [hNxT : ∀ l, Timeless (E.Nx l)]
    [hCpP : ∀ c, Persistent (E.Cp c)] [hCpT : ∀ c, Timeless (E.Cp c)] :
    kvStoreInvG (GF := GF) E.kv E.γ E.Nx E.Cp E.γs ∗ winTieRes E Fr ⊢ apply.envAus E := by
  haveI := kvStoreInvG_persistent Hp E.kv E.γ E.Nx E.Cp E.γs
  iintro ⟨#Hk, #Ht⟩
  iunfold winTieRes at Ht
  icases Ht with ⟨%γt, %HWt, #Hti, -⟩
  iunfold apply.envAus
  rw [hq, HWt]
  isplitr
  · iintro !> %log %c %X Hw HX
    iapply (au_begin E.Nx E.Cp Hp E.kv E.γ E.γs log c X) $$ Hk Hw HX
  isplitr
  · iintro !> %log %c %X Hw HX
    iapply (au_wread E.Nx E.Cp Hp E.kv E.γ E.γs log c X) $$ Hk Hw HX
  isplitr
  · iintro !> %log %c %pend %w Hw Hwt Hnx %HT #Hwit
    iapply (au_end_tie E.Nx E.Cp Hp E.kv E.γ E.γs Fr (mvccLeases E.γ) γt log c pend w) $$ Hk Hti Hw Hwt Hnx [] Hwit
    ipureintro; exact HT
  isplitr
  · iintro !> %log %c %rev %hrev Hw Hc Hcp
    ihave H := (au_compact E.Nx E.Cp Hp E.kv E.γ E.γs log c rev hrev) $$ Hk Hw Hc Hcp
    iExactEq H; rfl
  isplitr
  · iintro !> %log %c Hw
    imod (writer_facts E.Nx E.Cp Hp Hr E.kv E.γ E.γs log c) $$ Hk Hw with ⟨Hw, #Hlb, #Hnx, Hrc, %Hre⟩
    imodintro
    iframe Hw Hlb Hrc
    isplitr
    · imodintro; iexact Hnx
    ipureintro; exact Hre
  iintro !> %log %c %F Hw HF
  iapply (writer_floor E.Nx E.Cp Hp E.kv E.γ E.γs log c F) $$ Hk Hw HF

/-- The applier's chain resource does not read the window. -/
theorem uberOwn_win (E : apply.AEnv GF) (w w' : Option LWin) (p : Loc) (c : apply.Chain) :
    apply.uberOwn { E with win := w } p c ⊣⊢ apply.uberOwn { E with win := w' } p c := .rfl

/-- The compaction right does not read the window. -/
theorem cmpOwn_win (E : apply.AEnv GF) (w w' : Option LWin) (c : Int) :
    apply.cmpOwn { E with win := w } c ⊣⊢ apply.cmpOwn { E with win := w' } c := .rfl

/-- **An entry's window at the apply thread** (F4, per entry; `tie_push`): the apply thread's KV resources at the
window `w` move to a new window `(s, T)`, `T` the items of a committed model log `Lt` extending the store's log. -/
theorem kvOwn_push (Hp : persistent.law (GF := GF)) (Hr : mvccState_reachable.law (GF := GF))
    (E : apply.AEnv GF) (Fr : Prop) (hq : E.stq = (1 : Qp).half.half)
    [hNxP : ∀ l, Persistent (E.Nx l)] [hNxT : ∀ l, Timeless (E.Nx l)]
    [hCpP : ∀ c, Persistent (E.Cp c)] [hCpT : ∀ c, Timeless (E.Cp c)]
    (w : Option LWin) (log Lt : mvcc.Log) (hlt : log <+: Lt) :
    kvStoreInvG (GF := GF) E.kv E.γ E.Nx E.Cp E.γs ∗ winTieRes E Fr ∗ apply.kvOwn { E with win := w } log ∗
      □ E.Nx Lt ={⊤}=∗ ∃ s : Nat, apply.kvOwn { E with win := some (s, itemsOfLog Lt) } log := by
  haveI := kvStoreInvG_persistent Hp E.kv E.γ E.Nx E.Cp E.γs
  iintro ⟨#Hk, #Ht, Hko, #Hnx⟩
  iunfold winTieRes at Ht
  icases Ht with ⟨%γt, %HWt, #Hti, #Hl⟩
  iunfold apply.kvOwn at Hko
  icases Hko with ⟨⟨%c, Hw⟩, Hbk, Hll, HRD⟩
  iunfold apply.leasesLive at Hll
  icases Hll with ⟨%L, Hkn, Hu, Hlt, HWt'⟩
  iunfold lease.lessorUserW at Hu
  icases Hu with ⟨Ho, Hrd, Hrv⟩
  simp only
  rw [hq, HWt]
  imod (writer_facts E.Nx E.Cp Hp Hr E.kv E.γ E.γs log c) $$ Hk Hw with ⟨Hw, -, #Hnl, -, -⟩
  imod (tie_push E.Nx Fr (mvccLeases E.γ) E.γs γt L w log Lt c (itemsOfLog Lt) hlt rfl)
    $$ [Hti Hl Ho HWt' Hw Hnl Hnx] with ⟨%s, Ho, HWt', Hw⟩
  · iframe Hti Hl Ho HWt' Hw Hnl Hnx
  imodintro
  iexists s
  iunfold apply.kvOwn
  isplitl [Hw]
  · iexists c; iexact Hw
  isplitl [Hbk]
  · iExactEq Hbk; rfl
  isplitr [HRD]
  · iunfold apply.leasesLive
    iexists L
    iframe Hkn HWt'
    isplitl [Ho Hrd Hrv]
    · iunfold lease.lessorUserW
      iframe Ho Hrd Hrv
    iExactEq Hlt; rfl
  iExactEq HRD; rfl

/-- **An entry's window, the applier state** (`kvOwn_push` under `applyKV`). -/
theorem applyKV_push (Hp : persistent.law (GF := GF)) (Hr : mvccState_reachable.law (GF := GF))
    (E : apply.AEnv GF) (Fr : Prop) (hq : E.stq = (1 : Qp).half.half)
    [hNxP : ∀ l, Persistent (E.Nx l)] [hNxT : ∀ l, Timeless (E.Nx l)]
    [hCpP : ∀ c, Persistent (E.Cp c)] [hCpT : ∀ c, Timeless (E.Cp c)]
    (w : Option LWin) (ua : GoInterface) (x : apply.ApplyKV) (Lt : mvcc.Log) (hlt : x.log <+: Lt) :
    kvStoreInvG (GF := GF) E.kv E.γ E.Nx E.Cp E.γs ∗ winTieRes E Fr ∗ apply.applyKV { E with win := w } ua x ∗
      □ E.Nx Lt ={⊤}=∗ ∃ s : Nat, apply.applyKV { E with win := some (s, itemsOfLog Lt) } ua x := by
  haveI := kvStoreInvG_persistent Hp E.kv E.γ E.Nx E.Cp E.γs
  iintro ⟨#Hk, #Ht, Ha, #Hnx⟩
  iunfold apply.applyKV at Ha
  icases Ha with ⟨%p, %Hua, Huo, Hko, Hco⟩
  imod (kvOwn_push Hp Hr E Fr hq w x.log Lt hlt) $$ [Hk Ht Hko Hnx] with ⟨%s, Hko⟩
  · iframe Hk Ht Hko Hnx
  imodintro
  iexists s
  iunfold apply.applyKV
  iexists p
  iframe Hko
  isplitr
  · ipureintro; exact Hua
  isplitl [Huo]
  · iapply (uberOwn_win E w _ p x.chain).1; iexact Huo
  iapply (cmpOwn_win E w _ x.crev).1; iexact Hco

/-- **The snapshot path's free marker at the apply thread** (`tie_free`; `Fr` the server's: not in the no-snapshot
mode): the apply thread's KV resources at the window `w` move to no window. -/
theorem kvOwn_free (E : apply.AEnv GF) (Fr : Prop) (hFr : Fr)
    [hNxP : ∀ l, Persistent (E.Nx l)] [hNxT : ∀ l, Timeless (E.Nx l)]
    (w : Option LWin) (log : mvcc.Log) :
    winTieRes E Fr ∗ apply.kvOwn { E with win := w } log ={⊤}=∗ apply.kvOwn { E with win := none } log := by
  iintro ⟨#Ht, Hko⟩
  iunfold winTieRes at Ht
  icases Ht with ⟨%γt, %HWt, #Hti, #Hl⟩
  iunfold apply.kvOwn at Hko
  icases Hko with ⟨Hw, Hbk, Hll, HRD⟩
  iunfold apply.leasesLive at Hll
  icases Hll with ⟨%L, Hkn, Hu, Hlt, HWt'⟩
  iunfold lease.lessorUserW at Hu
  icases Hu with ⟨Ho, Hrd, Hrv⟩
  simp only
  rw [HWt]
  imod (tie_free E.Nx Fr hFr (mvccLeases E.γ) E.γs γt L _ w) $$ [Hti Hl Ho HWt'] with ⟨Ho, HWt'⟩
  · iframe Hti Hl Ho HWt'
  imodintro
  iunfold apply.kvOwn
  isplitl [Hw]
  · iExactEq Hw; rfl
  isplitl [Hbk]
  · iExactEq Hbk; rfl
  isplitr [HRD]
  · iunfold apply.leasesLive
    iexists L
    iframe Hkn HWt'
    isplitl [Ho Hrd Hrv]
    · iunfold lease.lessorUserW
      iframe Ho Hrd Hrv
    iExactEq Hlt; rfl
  iExactEq HRD; rfl

/-- **The snapshot path's free marker, the applier state** (`kvOwn_free` under `applyKV`). -/
theorem applyKV_free (E : apply.AEnv GF) (Fr : Prop) (hFr : Fr)
    [hNxP : ∀ l, Persistent (E.Nx l)] [hNxT : ∀ l, Timeless (E.Nx l)]
    (w : Option LWin) (ua : GoInterface) (x : apply.ApplyKV) :
    winTieRes E Fr ∗ apply.applyKV { E with win := w } ua x ={⊤}=∗ apply.applyKV { E with win := none } ua x := by
  iintro ⟨#Ht, Ha⟩
  iunfold apply.applyKV at Ha
  icases Ha with ⟨%p, %Hua, Huo, Hko, Hco⟩
  imod (kvOwn_free E Fr hFr w x.log) $$ [Ht Hko] with Hko
  · iframe Ht Hko
  imodintro
  iunfold apply.applyKV
  iexists p
  iframe Hko
  isplitr
  · ipureintro; exact Hua
  isplitl [Huo]
  · iapply (uberOwn_win E w _ p x.chain).1; iexact Huo
  iapply (cmpOwn_win E w _ x.crev).1; iexact Hco

end laws

end srvApi
end EtcdGrove
end Perennial
