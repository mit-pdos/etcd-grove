/-
Lean-first (no Rocq counterpart).

# The updates raft's proposals take (2026-10-29, kvreconf-final)

kv's `kv_propAu` and `kv_ccAu` (`Proof/github_com/mit_pdos/etcd_grove/examples/kv/Lemmas.lean`) on
kvreconf's invariant (`rkvInv`, `Defs.lean`). Both are persistent (`isClusterC` records
`γ.dup = true`: raft may commit a duplicated `MsgProp` again), built from the invariant alone (and
the operation's slot):

- `kvr_propAu`, `node.Propose`'s, for an operation's datum `d` with the slot `γp`: when an entry of
  it commits, the history moves by `d`; at its first occurrence (`d` not yet in the history) the
  client's update runs from the slot (the linearization point), and a later occurrence leaves the
  history. The datum is minted (it has a slot), so it decodes and is not empty: its entry carries
  it (`odOf`).
- `kvr_ccAu`, `node.ProposeConfChange`'s (`Reconfigure`), for a change `o` of a defined transition
  (`ccTransOk`): its entry carries no datum, so the history stays; the committed requested conf
  entries stay shaped (`confShaped_proposed`).

`kvr_propAu_dup`/`kvr_ccAu_dup` are the same at `□?γ.dup`, the form the specs take.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.ClientLemmas
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.Rule

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- A conf entry carries no datum: the history stays. -/
theorem logHist_conf (ops : List LogEntry) (o : ConfChangeIM) (t : w64) (bs : List w8) :
    logHist (ops ++ opsOf [⟨t, confChangeEntryType (some o), bs⟩]) = logHist ops := by
  have Hod : odOf (⟨t, confChangeEntryType (some o), bs⟩ : LogEntry) = none := by
    unfold odOf; rw [ite_eq_right_iff]
    rintro ⟨h, -⟩
    exfalso; revert h
    cases o <;> simp only [confChangeEntryType] <;> word
  unfold logHist histOf
  rw [List.map_append, List.foldl_append, foldl_histStep_opsOf]
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, Hod, histStep]

/-- The requested entries of a conf entry carry no datum. -/
theorem odOf_conf_none (o : ConfChangeIM) (t : w64) (bs : List w8) :
    ∀ x ∈ (opsOf [(⟨t, confChangeEntryType (some o), bs⟩ : LogEntry)]).map odOf, x = none := by
  intro x hx
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
  have he' : e = ⟨t, confChangeEntryType (some o), bs⟩ := by
    unfold opsOf at he; simp only [List.filter] at he; split at he <;> simp_all
  subst he'
  unfold odOf; rw [ite_eq_right_iff]
  rintro ⟨h, -⟩
  exfalso; revert h
  cases o <;> simp only [confChangeEntryType] <;> word

end pure

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [StorageModel GF] [AllG GF]

/-- A slot of another datum keeps its state as the history grows by `d`. -/
theorem opSlot_grow (γr : RNames) (d' d : List w8) (γp : GName × GName) (H : List (List w8))
    (Hne : d' ≠ d) :
    ⊢ opSlot (GF := GF) γr d' γp H -∗ opSlot γr d' γp (H ++ [d]) := by
  unfold opSlot
  iintro ⟨%Φ, #Hsp, Hst⟩
  iexists Φ
  iframe Hsp
  icases Hst with (⟨%Hn, Hlc, Hau⟩ | ⟨%H0, %Hp, HQ⟩)
  · ileft
    iframe Hlc Hau
    ipureintro
    simp only [List.mem_append, List.mem_singleton, not_or]
    exact ⟨Hn, Hne⟩
  · iright
    iexists H0
    iframe HQ
    ipureintro
    exact ⟨Hp.1.trans (List.prefix_append _ _), Hp.2⟩

/-- **The update `node.Propose` takes** for the operation's datum `d`, whose slot is `γp` (see the
file header). -/
theorem kvr_propAu (γr : RNames) (d : List w8) (γp : GName × GName) :
    ⊢ rkvInv (GF := GF) γr -∗ d ↪[γr.ops]□ γp -∗
      □ AU <{ ∃∃ (ops : List LogEntry), ownCommittedOps γr.cluster ops }>
          @ ⊤ \ ↑kvrRaftN, ∅
        <{ ∀∀ (t : w64), ownCommittedOps γr.cluster (ops ++ [(⟨t, W32 0, d⟩ : LogEntry)]),
           COMM True }> := by
  iintro #Hinv #Hop
  imodintro
  iauintro
  unfold atomic_acc rkvInv rkvInvBody
  have Hdisj := rkvN_kvrRaftN
  iinv Hinv with ⟨%ops, %n, %Mi, %RS, %RMi, %O, %U, >Hc, Hsl⟩ Hclose
  iunfold kvCore at Hc
  icases Hc with ⟨Hops, Hv, HU, Hn, HMi, HRS, HRMi, HO, %Hok, %Hodm, %Hsh⟩
  icases ghost_map_lookup $$ HO Hop with %HOd
  have HMd : MintedOp Mi d := Hok.2.2.1 d γp HOd
  have Hne : d ≠ [] := mintedOp_ne_nil Mi d HMd
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ (⊤ \ ↑kvrRaftN) \ ↑rkvN from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists ops
  iframe Hops
  isplit
  · -- abort: nothing moved
    iintro Hops
    imod Hclose2 with -
    imod Hclose $$ [Hops Hv HU Hn HMi HRS HRMi HO Hsl] with -
    · inext
      iexists ops, n, Mi, RS, RMi, O, U
      iframe Hsl
      unfold kvCore
      iframe Hops Hv HU Hn HMi HRS HRMi HO
      ipureintro; exact ⟨Hok, Hodm, Hsh⟩
    imodintro
    iempintro
  · -- commit: the requested entries grow by `d`'s
    iintro %t Hops
    imod Hclose2 with -
    have Hod : odOf (⟨t, W32 0, d⟩ : LogEntry) = some d := odOf_normal _ rfl Hne
    have Hhist : logHist (ops ++ [⟨t, W32 0, d⟩]) = histStep (logHist ops) (some d) := by
      rw [logHist_snoc, Hod]
    have Hodm' : ∀ d', some d' ∈ (ops ++ [(⟨t, W32 0, d⟩ : LogEntry)]).map odOf →
        MintedOp Mi d' := by
      intro d' h
      rw [List.map_append, List.map_singleton, Hod] at h
      rcases List.mem_append.mp h with h | h
      · exact Hodm d' h
      · simp only [List.mem_singleton, Option.some.injEq] at h; subst h; exact HMd
    have Hsh' : ∀ e ∈ ops ++ [(⟨t, W32 0, d⟩ : LogEntry)], e.isConfChange → ConfShaped e := by
      intro e he hc
      rcases List.mem_append.mp he with h | h
      · exact Hsh e h hc
      · simp only [List.mem_singleton] at h; subst h
        exfalso; rcases hc with h | h <;> simp only at h <;> word
    by_cases Hm : d ∈ logHist ops
    · -- a later occurrence: the history does not move
      have Hocc : logHist (ops ++ [⟨t, W32 0, d⟩]) = logHist ops := by
        rw [Hhist, histStep_mem _ _ Hm]
      imod Hclose $$ [Hops Hv HU Hn HMi HRS HRMi HO Hsl] with -
      · inext
        iexists ops ++ [⟨t, W32 0, d⟩], n, Mi, RS, RMi, O, U
        rw [Hocc]
        iframe Hsl
        unfold kvCore
        rw [Hocc]
        iframe Hops Hv HU Hn HMi HRS HRMi HO
        ipureintro; exact ⟨Hok, Hodm', Hsh'⟩
      imodintro
      itrivial
    · -- the first occurrence: the client's update runs, from the slot
      have Hocc : logHist (ops ++ [⟨t, W32 0, d⟩]) = logHist ops ++ [d] := by
        rw [Hhist, histStep_nmem _ _ Hm]
      ihave Hsl := (BigSepM.bigSepM_later).1 $$ Hsl
      icases (BigSepM.bigSepM_delete (Φ := fun d γp =>
        iprop(▷ opSlot (GF := GF) γr d γp (logHist ops))) HOd).1 $$ Hsl with ⟨Hsd, Hsl⟩
      iunfold opSlot at Hsd
      icases Hsd with ⟨%Φ, #Hsp, Hst⟩
      icases Hst with (⟨>%Hn', >Hlc, Hau⟩ | ⟨%H0, >%Hp, -⟩)
      · imod lc_fupd_elim_later $$ Hlc Hau with Hau
        iunfold opAu at Hau
        ihave Hau := atomic_update_mask_weaken kvrMask_sub $$ Hau
        ihave Hacc := aupd_aacc $$ Hau
        unfold atomic_acc
        imod Hacc with Hacc
        isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
        icases Hacc with ⟨%x, Hx, Hucl⟩
        ihave %Hxeq := rkvVal_agree γr (logHist ops) x $$ Hv Hx
        subst Hxeq
        have Hf : kvFold (logHist ops ++ [d]) = kvApply (kvFold (logHist ops)) d :=
          kvFold_snoc _ _
        imod rkvVal_update γr (logHist ops) (kvFold (logHist ops)) (logHist ops ++ [d])
          $$ Hv Hx with ⟨Hv, Hx⟩
        icases Hucl with ⟨-, Hcommit⟩
        isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hcommit
        rw [Hf]
        imod Hcommit $$ [Hx] with HΦ
        · rw [← Hf]; iexact Hx
        imod Hclose $$ [Hops Hv HU Hn HMi HRS HRMi HO Hsl HΦ] with -
        · inext
          iexists ops ++ [⟨t, W32 0, d⟩], n, Mi, RS, RMi, O, U
          rw [Hocc]
          isplitl [Hops Hv HU Hn HMi HRS HRMi HO]
          · unfold kvCore
            rw [Hocc]
            iframe Hops Hv HU Hn HMi HRS HRMi HO
            ipureintro; exact ⟨Hok, Hodm', Hsh'⟩
          iapply (BigSepM.bigSepM_delete (Φ := fun d' γp' =>
            opSlot (GF := GF) γr d' γp' (logHist ops ++ [d])) HOd).2
          isplitl [HΦ]
          · unfold opSlot
            iexists Φ
            iframe Hsp
            iright
            iexists logHist ops
            isplitr
            · ipureintro; exact ⟨List.prefix_refl _, Hm⟩
            ileft
            rw [Hf]
            iexact HΦ
          iapply BigSepM.bigSepM_impl $$ Hsl
          imodintro
          iintro %k %v %Hkv Hs
          have Hne' : k ≠ d := (Iris.Std.LawfulPartialMap.get?_delete_some_iff.mp Hkv).1.symm
          iapply opSlot_grow γr k d v (logHist ops) Hne' $$ Hs
        imodintro
        itrivial
      · exact absurd (Hp.1.subset (List.mem_append_right _ (List.mem_singleton_self d))) Hm

/-- `kvr_propAu` in the form `node.Propose` takes it. -/
theorem kvr_propAu_dup (γr : RNames) (d : List w8) (γp : GName × GName) :
    ⊢ rkvInv (GF := GF) γr -∗ d ↪[γr.ops]□ γp -∗
      □?γr.cluster.dup AU <{ ∃∃ (ops : List LogEntry), ownCommittedOps γr.cluster ops }>
          @ ⊤ \ ↑kvrRaftN, ∅
        <{ ∀∀ (t : w64), ownCommittedOps γr.cluster (ops ++ [(⟨t, W32 0, d⟩ : LogEntry)]),
           COMM True }> := by
  iintro #Hinv #Hop
  iapply intuitionisticallyIf_of_intuitionistically
  iapply kvr_propAu γr d γp $$ Hinv Hop

/-- **The update `node.ProposeConfChange` takes** for a change `o` of a defined transition (see
the file header). -/
theorem kvr_ccAu (γr : RNames) (o : ConfChangeIM) : ccTransOk o →
    rkvInv (GF := GF) γr ⊢
      □ AU <{ ∃∃ (ops : List LogEntry), ownCommittedOps γr.cluster ops }>
          @ ⊤ \ ↑kvrRaftN, ∅
        <{ ∀∀ (t : w64) (bs : List w8), ⌜MarshalsConfChange (some o) bs⌝ ∗
             ownCommittedOps γr.cluster
               (ops ++ opsOf [(⟨t, confChangeEntryType (some o), bs⟩ : LogEntry)]),
           COMM True }> := by
  intro Hto
  iintro #Hinv
  imodintro
  iauintro
  unfold atomic_acc rkvInv rkvInvBody
  have Hdisj := rkvN_kvrRaftN
  iinv Hinv with ⟨%ops, %n, %Mi, %RS, %RMi, %O, %U, >Hc, Hsl⟩ Hclose
  iunfold kvCore at Hc
  icases Hc with ⟨Hops, Hv, HU, Hn, HMi, HRS, HRMi, HO, %Hok, %Hodm, %Hsh⟩
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ (⊤ \ ↑kvrRaftN) \ ↑rkvN from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists ops
  iframe Hops
  isplit
  · iintro Hops
    imod Hclose2 with -
    imod Hclose $$ [Hops Hv HU Hn HMi HRS HRMi HO Hsl] with -
    · inext
      iexists ops, n, Mi, RS, RMi, O, U
      iframe Hsl
      unfold kvCore
      iframe Hops Hv HU Hn HMi HRS HRMi HO
      ipureintro; exact ⟨Hok, Hodm, Hsh⟩
    imodintro
    iempintro
  · iintro %t %bs ⟨%Hbs, Hops⟩
    imod Hclose2 with -
    have Hocc := logHist_conf ops o t bs
    imod Hclose $$ [Hops Hv HU Hn HMi HRS HRMi HO Hsl] with -
    · inext
      iexists ops ++ opsOf [⟨t, confChangeEntryType (some o), bs⟩], n, Mi, RS, RMi, O, U
      rw [Hocc]
      iframe Hsl
      unfold kvCore
      rw [Hocc]
      iframe Hops Hv HU Hn HMi HRS HRMi HO
      ipureintro
      refine ⟨Hok, fun d' h => ?_, ?_⟩
      · rw [List.map_append] at h
        rcases List.mem_append.mp h with h | h
        · exact Hodm d' h
        · cases odOf_conf_none o t bs _ h
      · intro e he hc
        rcases List.mem_append.mp he with h | h
        · exact Hsh e h hc
        · exact confShaped_proposed o t bs Hbs Hto e h hc
    imodintro
    itrivial

/-- `kvr_ccAu` in the form `node.ProposeConfChange` takes it. -/
theorem kvr_ccAu_dup (γr : RNames) (o : ConfChangeIM) : ccTransOk o →
    rkvInv (GF := GF) γr ⊢
      □?γr.cluster.dup AU <{ ∃∃ (ops : List LogEntry), ownCommittedOps γr.cluster ops }>
          @ ⊤ \ ↑kvrRaftN, ∅
        <{ ∀∀ (t : w64) (bs : List w8), ⌜MarshalsConfChange (some o) bs⌝ ∗
             ownCommittedOps γr.cluster
               (ops ++ opsOf [(⟨t, confChangeEntryType (some o), bs⟩ : LogEntry)]),
           COMM True }> := by
  intro Hto
  iintro #Hinv
  iapply intuitionisticallyIf_of_intuitionistically
  iapply kvr_ccAu γr o Hto $$ Hinv

end lemmas

end kvreconf
end EtcdGrove
end Perennial
