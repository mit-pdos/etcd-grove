/- Lean-first (no Rocq counterpart).

# `etcd/dist/server`: the cluster's start at the members' shares (`notes/etcd-dist-plan.md` §21.1, step 2)

`clusterStartD`: the start of a well-formed deployment's cluster over the global ghost state (no heap), giving every
member its share `memberShareD` (N5's, what `member_boot_dist` takes) and the client machines the members' client
address facts. It is `etcdClusterStart` (`ClusterStart.lean`) with the peer addresses set **after** the allocation:
`memberShareD`'s peer facts are `S5Interim.lean`'s `httpAddrAt`, indexed by the cluster's raft names `c.γ`
(`peerAddrFactsAt`, §19), which exist only once `clusterAllocN` has chosen them. In order:
- `clusterAllocN` over the members' ids, at `bootstrap`'s peers and contexts (`distPs d`, `distCtxs d`: `BootFacts`'s
  `BootCore`; the peers a permutation of the ids by `BootGoD.of_wf`), lease mode `none`, and the compaction mode and
  retention the deployment's compactor is configured for (`compactorCfg_of_wf`);
- every member's peer address set to the cluster's peer protocols (`http_addr_set` at `c.γ`, `peersAt_start`);
- every member's client address set to serve etcd's table for its id at the cluster's view (`etcdAddr_set` at
  `c.view`, `clientsAt_start`);
- member `i`'s share from its slice and the persistent facts (`memberShares_of`).
It also returns the client's `etcdKV` at the boot state (the lease mode `none`) and that the KV names' start log is
the empty one, for the kv instance's store (`kvremote/MembersStart.lean`).

No axiom, no `sorry`, no hypothesis beyond a bound on the receipt budget.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.BootGoD

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI Iris.ProofMode Net go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver etcdstart

attribute [local instance] GooseGlobalGS.gooseInvGS

/-! ## The deployment's members as the start's (pure) -/

section pure
variable [GooseExts]

theorem map_zip_map_self {α β γ : Type _} (l : List α) (f : α → β) (g : α × β → γ) :
    (l.zip (l.map f)).map g = l.map (fun a => g (a, f a)) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.zip_cons_cons, ih]

/-- **The start's members are the deployment's**, each with its id. -/
theorem cmsD_eq (d : Deployment) :
    cmsD d = d.members.map (fun m => (⟨m.peer, m.client, memberId (go!"http://" ++ m.peer) d.token⟩ :
      ClusterMember)) := by
  unfold cmsD Deployment.ids
  rw [map_zip_map_self]

theorem cmsD_ids (d : Deployment) : (cmsD d).map (·.id) = d.ids := by
  rw [cmsD_eq, List.map_map]
  rfl

/-- Member `k`'s id and client address, as `memberShareD` reads them. -/
theorem members_getD_ids (d : Deployment) (k : Nat) (m : Member) (hk : d.members[k]? = some m) :
    d.ids.getD k (W64 0) = memberId (go!"http://" ++ m.peer) d.token ∧
      (d.members.getD k ⟨go!"", go!"", go!""⟩).client = m.client := by
  constructor
  · simp [Deployment.ids, List.getD_eq_getElem?_getD, hk]
  · simp [List.getD_eq_getElem?_getD, hk]

theorem le_sum_map_of_mem {α : Type _} (l : List α) (f : α → Nat) (a : α) (h : a ∈ l) :
    f a ≤ (l.map f).sum := by
  induction l with
  | nil => cases h
  | cons b l ih =>
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := ih h; omega

/-- **The members' lessor names, padded to all of `w64`** (#50 F7, L4): `f` on the members `ids`, and above every
member's name, one apart, off them. -/
def lsPad (ids : List w64) (f : w64 → GName) : w64 → GName :=
  fun x => if x ∈ ids then f x else (ids.map f).sum + 1 + uint.nat x

/-- **The members' auth names, padded to all of `w64`**: `g` on the members `ids`, and off them a record whose
fields are all one name above every member's history name. -/
def auPad (ids : List w64) (g : w64 → EtcdGrove.auth.AuthNames) : w64 → EtcdGrove.auth.AuthNames :=
  fun x => if x ∈ ids then g x else
    let n := (ids.map (fun y => (g y).hist)).sum + 1 + uint.nat x
    ⟨n, n, n, n, n, n, n, n, n, n, n, n⟩

theorem lsPad_inj (ids : List w64) (f : w64 → GName)
    (hf : ∀ a ∈ ids, ∀ b ∈ ids, f a = f b → a = b) : ∀ a b, lsPad ids f a = lsPad ids f b → a = b := by
  intro a b h
  unfold lsPad at h
  by_cases ha : a ∈ ids <;> by_cases hb : b ∈ ids
  · rw [if_pos ha, if_pos hb] at h; exact hf a ha b hb h
  · rw [if_pos ha, if_neg hb] at h
    have h2 : (f a : Nat) = (ids.map f).sum + 1 + uint.nat b := h
    have := le_sum_map_of_mem ids f a ha; omega
  · rw [if_neg ha, if_pos hb] at h
    have h2 : ((ids.map f).sum + 1 + uint.nat a : Nat) = f b := h
    have := le_sum_map_of_mem ids f b hb; omega
  · rw [if_neg ha, if_neg hb] at h
    have h2 : ((ids.map f).sum + 1 + uint.nat a : Nat) = (ids.map f).sum + 1 + uint.nat b := h
    exact uint_nat_inj (by omega)

theorem auPad_inj (ids : List w64) (g : w64 → EtcdGrove.auth.AuthNames)
    (hg : ∀ a ∈ ids, ∀ b ∈ ids, (g a).hist = (g b).hist → a = b) :
    ∀ a b, auPad ids g a = auPad ids g b → a = b := by
  intro a b h
  have h' := congrArg EtcdGrove.auth.AuthNames.hist h
  unfold auPad at h'
  by_cases ha : a ∈ ids <;> by_cases hb : b ∈ ids
  · rw [if_pos ha, if_pos hb] at h'; exact hg a ha b hb h'
  · rw [if_pos ha, if_neg hb] at h'
    have h2 : ((g a).hist : Nat) = (ids.map (fun y => (g y).hist)).sum + 1 + uint.nat b := h'
    have := le_sum_map_of_mem ids (fun y => (g y).hist) a ha; simp only at this; omega
  · rw [if_neg ha, if_pos hb] at h'
    have h2 : ((ids.map (fun y => (g y).hist)).sum + 1 + uint.nat a : Nat) = (g b).hist := h'
    have := le_sum_map_of_mem ids (fun y => (g y).hist) b hb; simp only at this; omega
  · rw [if_neg ha, if_neg hb] at h'
    have h2 : ((ids.map (fun y => (g y).hist)).sum + 1 + uint.nat a : Nat) =
      (ids.map (fun y => (g y).hist)).sum + 1 + uint.nat b := h'
    exact uint_nat_inj (by omega)

end pure

section compactor
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]

/-- **The compactor's slot at the deployment's configuration**: a well-formed deployment's compactor is off, in
revision mode at a positive retention, or in periodic mode at a period of at least 10ns (`ServerCfg.Supported`), so
some compaction mode and cluster retention meet `v3compactor.bootCfg` (off: no compaction; revision: the retention;
periodic: retention `0`). -/
theorem compactorCfg_of_wf {d : Deployment} (Hd : d.WellFormed) :
    ∃ (cmp : Bool) (cret : Nat), v3compactor.bootCfg d.cfg.compactorMode d.cfg.retention cmp cret := by
  obtain ⟨t, ⟨-, -, ⟨hc, -⟩, -, -⟩, hw⟩ := Hd
  -- `WellFormed`'s conjuncts by their statements, not their positions
  have hs' : t.cfg.Supported := by grind [typed.Deployment.WellFormed]
  obtain ⟨hs, -⟩ := hs'
  revert hc hs
  cases t.cfg.compactor with
  | off =>
    intro hc _
    refine ⟨false, 0, v3compactor.bootCfg_off _ _ _ _ ?_⟩
    first
      | (apply BitVec.eq_of_toInt_eq; simp only [sint.Z] at hc; rw [hc]; try (first | rfl | decide); done)
      | word
  | revision r =>
    intro hc hs
    obtain ⟨hm, hr, -⟩ := hc
    obtain ⟨h1, -⟩ := hs
    refine ⟨true, r, ?_⟩
    rw [hm]
    exact v3compactor.bootCfg_revision _ _ (by omega) (by omega)
  | periodic p =>
    intro hc hs
    obtain ⟨hm, hr, -⟩ := hc
    obtain ⟨h1, -⟩ := hs
    refine ⟨true, 0, ?_⟩
    rw [hm]
    exact v3compactor.bootCfg_periodic _ _ (by omega) rfl

end compactor

/-! ## The start -/

section start
variable {GF : BundledGFunctors} [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
  [GoGlobalContext] [GoLocalContext] [go.Semantics] [go_etcd_io.etcd.client.v3.Assumptions]
  [go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
  [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
  [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

/-- A list of members' two addresses each, as a per-member conjunction. -/
theorem addrs_members (l : List Member) :
    ([∗list] a ∈ l.flatMap (fun m => [m.peer, m.client]), addrUnset (Gg := G) a) ⊢
      [∗list] m ∈ l, addrUnset (Gg := G) m.peer ∗ addrUnset (Gg := G) m.client := by
  induction l with
  | nil =>
    iintro -
    iapply BigSepL.bigSepL_nil.2
    iempintro
  | cons m l ih =>
    rw [show (m :: l).flatMap (fun m => [m.peer, m.client]) =
      [m.peer, m.client] ++ l.flatMap (fun m => [m.peer, m.client]) from rfl]
    iintro H
    icases BigSepL.bigSepL_append.1 $$ H with ⟨H0, H⟩
    icases BigSepL.bigSepL_cons.1 $$ H0 with ⟨Hp, H0⟩
    icases BigSepL.bigSepL_cons.1 $$ H0 with ⟨Hc, -⟩
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hp Hc]
    · isplitl [Hp]
      · iexact Hp
      · iexact Hc
    · iapply ih
      iexact H

theorem peers_cms (d : Deployment) :
    ([∗list] m ∈ d.members, addrUnset (Gg := G) m.peer) ⊢ [∗list] m ∈ cmsD d, addrUnset (Gg := G) m.peer := by
  rw [cmsD_eq, BigSepL.bigSepL_map] <;> exact .rfl

theorem clients_cms (d : Deployment) :
    ([∗list] m ∈ d.members, addrUnset (Gg := G) m.client) ⊢
      [∗list] m ∈ cmsD d, addrUnset (Gg := G) m.client := by
  rw [cmsD_eq, BigSepL.bigSepL_map] <;> exact .rfl

/-- **Every member's peer address set to the cluster's peer protocols** (`http_addr_set` at `γ`, per member). -/
theorem peersAt_start (γ : SrvRaft) (ns : List ClusterMember) :
    ⊢ regCtx (Gg := G) -∗ ([∗list] m ∈ ns, addrUnset (Gg := G) m.peer) ={⊤}=∗
      peerAddrFactsAt (GF := GF) γ ns := by
  induction ns with
  | nil =>
    iintro #_ _
    imodintro
    iunfold peerAddrFactsAt
    iempintro
  | cons m ns ih =>
    iintro #Hreg Hs
    ihave Hs := BigSepL.bigSepL_cons.1 $$ Hs
    icases Hs with ⟨Ha, Hs⟩
    imod (http_addr_set ⊤ γ m.id m.peer) $$ Hreg Ha with #Hp
    imod ih $$ Hreg Hs with #Hps
    imodintro
    iunfold peerAddrFactsAt
    iunfold peerAddrFactsAt at Hps
    iapply BigSepL.bigSepL_cons.2
    iframe #

/-- **Every member's client address set to serve etcd's table for its id at the view `Γ`** (`etcdAddr_set`, per
member). -/
theorem clientsAt_start (Γ : DistView) (ns : List ClusterMember) :
    ⊢ regCtx (Gg := G) -∗ ([∗list] m ∈ ns, addrUnset (Gg := G) m.client) ={⊤}=∗
      clientSvcFacts (GF := GF) ns Γ := by
  induction ns with
  | nil =>
    iintro #_ _
    imodintro
    iunfold clientSvcFacts
    iempintro
  | cons m ns ih =>
    iintro #Hreg Hs
    ihave Hs := BigSepL.bigSepL_cons.1 $$ Hs
    icases Hs with ⟨Ha, Hs⟩
    imod (etcdAddr_set ⊤ m.client Γ m.id) $$ Hreg Ha with #Hat
    imod ih $$ Hreg Hs with #Hcs
    imodintro
    iunfold clientSvcFacts
    iunfold clientSvcFacts at Hcs
    iapply BigSepL.bigSepL_cons.2
    iframe #

theorem slices_members (c : ClusterNames) (d : Deployment) (ps : List w64) (ctxs : List (List w8))
    (bl : List EntryM) :
    ([∗list] id ∈ d.ids, memberSliceOf (GF := GF) c d.ids ps ctxs bl id) ⊢
      [∗list] m ∈ d.members, memberSliceOf (GF := GF) c d.ids ps ctxs bl
        (memberId (go!"http://" ++ m.peer) d.token) := by
  rw [show d.ids = d.members.map (fun m => memberId (go!"http://" ++ m.peer) d.token) from rfl,
    BigSepL.bigSepL_map] <;> exact .rfl

theorem clientSvc_members (d : Deployment) (Γ : DistView) :
    clientSvcFacts (GF := GF) (cmsD d) Γ ⊢
      [∗list] m ∈ d.members, etcdAddrAt (GF := GF) m.client Γ (memberId (go!"http://" ++ m.peer) d.token) := by
  unfold clientSvcFacts
  rw [cmsD_eq, BigSepL.bigSepL_map] <;> exact .rfl

/-- **The member's names exclude a full history authority at the same name** (kept: the resources come back). -/
theorem hists_ne (γ : GName) (l : List EtcdGrove.auth.AuthState) (ids : List w64) (f : w64 → GName)
    (g : w64 → EtcdGrove.auth.AuthNames) :
    ⊢ monoListAuthOwn γ 1 l -∗ ([∗list] id ∈ ids, memberNamesShare (GF := GF) (f id) (g id)) -∗
      ⌜∀ a ∈ ids, (g a).hist ≠ γ⌝ ∗ monoListAuthOwn γ 1 l ∗
        [∗list] id ∈ ids, memberNamesShare (GF := GF) (f id) (g id) := by
  induction ids with
  | nil =>
    iintro Hγ _
    isplitr
    · ipureintro; intro a h; cases h
    iframe Hγ
    iapply BigSepL.bigSepL_nil.2
    iempintro
  | cons x ids ih =>
    iintro Hγ Hs
    icases BigSepL.bigSepL_cons.1 $$ Hs with ⟨Hx, Hs⟩
    by_cases hx : (g x).hist = γ
    · iexfalso
      iunfold memberNamesShare at Hx
      icases Hx with ⟨-, -, Hx⟩
      iunfold authNamesFreshG at Hx
      icases Hx with ⟨Hh, -⟩
      subst hx
      iapply (monoListAuthOwn_exclusive γ [EtcdGrove.auth.bootState] l) $$ Hh Hγ
    · icases ih $$ Hγ Hs with ⟨%Hne, Hγ, Hs⟩
      isplitr
      · ipureintro
        intro a ha
        rcases List.mem_cons.1 ha with rfl | ha
        · exact hx
        · exact Hne a ha
      iframe Hγ
      iapply BigSepL.bigSepL_cons.2
      iframe Hx Hs

/-- **The start's allocation of the members' lessor and auth names** (#50 F7, L4), by induction over the members'
ids (distinct): per member, `lease.lessorSlot_alloc` outside the names so far and `authNamesFreshG_alloc`, whose
history names differ from the others' by exclusivity. -/
theorem memberNames_alloc_list (ids : List w64) (hnd : ids.Nodup) :
    ⊢ |={⊤}=> ∃ (f : w64 → GName) (g : w64 → EtcdGrove.auth.AuthNames),
      ⌜(∀ a ∈ ids, ∀ b ∈ ids, f a = f b → a = b) ∧
        (∀ a ∈ ids, ∀ b ∈ ids, (g a).hist = (g b).hist → a = b)⌝ ∗
      [∗list] id ∈ ids, memberNamesShare (GF := GF) (f id) (g id) := by
  induction ids with
  | nil =>
    iintro
    imodintro
    iexists ClusterNames.lsNone, ClusterNames.auNone
    isplitr
    · ipureintro
      exact ⟨fun a h => (by cases h), fun a h => (by cases h)⟩
    iapply BigSepL.bigSepL_nil.2
    iempintro
  | cons x ids ih =>
    obtain ⟨hx, hnd'⟩ := List.nodup_cons.1 hnd
    iintro
    imod (ih hnd') with ⟨%f, %g, %Hfg, Hs⟩
    imod (lease.lessorSlot_alloc (GF := GF) ⊤ (ids.map f)) with ⟨%γl, %Hγl, Hl, #Hslot⟩
    imod (authNamesFreshG_alloc (GF := GF)) with Ha
    icases Ha with ⟨%γa, Ha⟩
    iunfold authNamesFreshG at Ha
    icases Ha with ⟨Hh, Ha⟩
    icases hists_ne γa.hist [EtcdGrove.auth.bootState] ids f g $$ Hh Hs with ⟨%Hne, Hh, Hs⟩
    imodintro
    iexists (fun y => if y = x then γl else f y), (fun y => if y = x then γa else g y)
    isplitr
    · ipureintro
      obtain ⟨Hf, Hg⟩ := Hfg
      have hfm : ∀ a ∈ ids, f a ≠ γl := fun a ha e => Hγl (e ▸ List.mem_map_of_mem ha)
      constructor
      · intro a ha b hb e
        have ha2 := List.mem_cons.1 ha
        have hb2 := List.mem_cons.1 hb
        beta_reduce at e
        by_cases hax : a = x <;> by_cases hbx : b = x
        · rw [hax, hbx]
        · rw [if_pos hax, if_neg hbx] at e
          exact absurd e.symm (hfm b (hb2.resolve_left hbx))
        · rw [if_neg hax, if_pos hbx] at e
          exact absurd e (hfm a (ha2.resolve_left hax))
        · rw [if_neg hax, if_neg hbx] at e
          exact Hf a (ha2.resolve_left hax) b (hb2.resolve_left hbx) e
      · intro a ha b hb e
        have ha2 := List.mem_cons.1 ha
        have hb2 := List.mem_cons.1 hb
        beta_reduce at e
        by_cases hax : a = x <;> by_cases hbx : b = x
        · rw [hax, hbx]
        · rw [if_pos hax, if_neg hbx] at e
          exact absurd e.symm (Hne b (hb2.resolve_left hbx))
        · rw [if_neg hax, if_pos hbx] at e
          exact absurd e (Hne a (ha2.resolve_left hax))
        · rw [if_neg hax, if_neg hbx] at e
          exact Hg a (ha2.resolve_left hax) b (hb2.resolve_left hbx) e
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hl Hh Ha]
    · simp only [ite_true]
      iunfold memberNamesShare
      iframe Hl Hslot
      iunfold authNamesFreshG
      iframe Hh Ha
    · iapply (BigSepL.bigSepL_mono (fun {k y} (hk : ids[k]? = some y) => by
        have hy : y ≠ x := fun e => hx (e ▸ List.mem_of_getElem? hk)
        simp only [hy, ite_false]
        exact .rfl)) $$ Hs

/-- **The members' names, padded** (#50 F7, L4): `lsPad`/`auPad` of `memberNames_alloc_list`'s, injective over all
of `w64`, with every member's `memberNamesShare`. -/
theorem memberNames_alloc (ids : List w64) (hnd : ids.Nodup) :
    ⊢ |={⊤}=> ∃ (ls : w64 → GName) (au : w64 → EtcdGrove.auth.AuthNames),
      ⌜(∀ a b, ls a = ls b → a = b) ∧ (∀ a b, au a = au b → a = b)⌝ ∗
      [∗list] id ∈ ids, memberNamesShare (GF := GF) (ls id) (au id) := by
  iintro
  imod (memberNames_alloc_list ids hnd) with ⟨%f, %g, %Hfg, Hs⟩
  imodintro
  iexists lsPad ids f, auPad ids g
  isplitr
  · ipureintro
    exact ⟨lsPad_inj ids f Hfg.1, auPad_inj ids g Hfg.2⟩
  iapply (BigSepL.bigSepL_mono (fun {k y} (hk : ids[k]? = some y) => by
    have hy : y ∈ ids := List.mem_of_getElem? hk
    simp only [lsPad, auPad, hy, ite_true]
    exact .rfl)) $$ Hs

theorem names_members (c : ClusterNames) (d : Deployment) :
    ([∗list] id ∈ d.ids, memberNamesShare (GF := GF) (c.ls id) (c.au id)) ⊢
      [∗list] m ∈ d.members, memberNamesShare (GF := GF) (c.ls (memberId (go!"http://" ++ m.peer) d.token))
        (c.au (memberId (go!"http://" ++ m.peer) d.token)) := by
  rw [show d.ids = d.members.map (fun m => memberId (go!"http://" ++ m.peer) d.token) from rfl,
    BigSepL.bigSepL_map] <;> exact .rfl

/-- **Every member's share** (`memberShareD`) from the cluster's facts, the peer facts, the members' slices and their
client address facts, at names `c` the allocation made true (`ClusterOk`) and a compactor slot the deployment's
configuration meets. -/
theorem memberShares_of (d : Deployment) (boot : List LogEntry) (c : ClusterNames) (cmp : Bool) (cret : Nat)
    (Hok : ClusterOk c (distPs d) boot .none cmp cret d.ids)
    (Hcmp : v3compactor.bootCfg d.cfg.compactorMode d.cfg.retention cmp cret) (Hinj : c.NamesInj) :
    ⊢ clusterFactsOf (GF := GF) c -∗ peerAddrFactsAt (GF := GF) c.γ (cmsD d) -∗
      ([∗list] id ∈ d.ids, memberSliceOf (GF := GF) c d.ids (distPs d) (distCtxs d) (LogEntry.toEntries boot 0) id) -∗
      clientSvcFacts (GF := GF) (cmsD d) c.view -∗
      ([∗list] id ∈ d.ids, memberNamesShare (GF := GF) (c.ls id) (c.au id)) -∗
      [∗list] i ↦ _m ∈ d.members, memberShareD (GF := GF) c d (distPs d) (distCtxs d) boot i := by
  iintro #Hcf #Hpf Hsl #Hcs Hnm
  ihave Hsl := slices_members c d (distPs d) (distCtxs d) (LogEntry.toEntries boot 0) $$ Hsl
  ihave Hnm := names_members c d $$ Hnm
  ihave #Hcs' := clientSvc_members d c.view $$ Hcs
  ihave Hb : [∗list] m ∈ d.members,
      (memberSliceOf (GF := GF) c d.ids (distPs d) (distCtxs d) (LogEntry.toEntries boot 0)
          (memberId (go!"http://" ++ m.peer) d.token) ∗
        etcdAddrAt (GF := GF) m.client c.view (memberId (go!"http://" ++ m.peer) d.token)) $$ [Hsl]
  · iapply BigSepL.bigSepL_sep_eqv.2
    isplitl [Hsl]
    · iexact Hsl
    · iexact Hcs'
  ihave Hb := BigSepL.bigSepL_sep_eqv.2 $$ [Hb Hnm]
  · isplitl [Hb]
    · iexact Hb
    · iexact Hnm
  iapply (BigSepL.bigSepL_impl (Ψ := fun k _ => memberShareD (GF := GF) c d (distPs d) (distCtxs d) boot k)) $$ Hb
  imodintro
  iintro %k %m %hk Hx
  icases Hx with ⟨⟨Hs, #Ha⟩, Hn⟩
  obtain ⟨hid, hcl⟩ := members_getD_ids d k m hk
  iunfold memberShareD
  rw [hid, hcl]
  iexists cmp, cret
  isplitr
  · ipureintro
    exact ⟨Hok, Hcmp, Hinj⟩
  iframe Hs Hn
  iframe #

/-- **The cluster's start at the members' shares** (see the file header): for a well-formed deployment `d` at the
bootstrap log `boot` (`BootFacts`), from the protocol registry and every member's peer and client addresses unset,
the cluster's names `c` (their KV start log the empty one), the client's `etcdKV` at the boot state, every member's
client address fact at the view `c.view`, and every member's share. -/
theorem clusterStartD (d : Deployment) (Hd : d.WellFormed) (boot : List LogEntry) (Hbf : BootFacts d boot)
    (Hrb : receiptBound GF ≤ 2 ^ 60) :
    ⊢ regCtx -∗ ([∗list] a ∈ d.members.flatMap (fun m => [m.peer, m.client]), addrUnset a) ={⊤}=∗
      ∃ c : ClusterNames, ⌜c.γk.log0 = [[], []]⌝ ∗
        etcdKV c.γk (kvModelSt c.γk (bootEntries (LogEntry.toEntries boot 0))) ∗
        clientSvcFacts (cmsD d) c.view ∗
        [∗list] i ↦ _m ∈ d.members, memberShareD (GF := GF) c d (distPs d) (distCtxs d) boot i := by
  have Hbc : BootCore (distPs d) (distCtxs d) boot := Hbf
  obtain ⟨cmp, cret, Hcmp⟩ := compactorCfg_of_wf Hd
  obtain ⟨hne, -, -, hlen, -⟩ := Hd.members
  have hperm : (distPs d).Perm d.ids := (BootGoD.of_wf Hd).perm
  obtain ⟨m0, ms, hm0⟩ : ∃ m0 ms, d.members = m0 :: ms := by
    cases h : d.members with
    | nil => exact absurd h hne
    | cons m0 ms => exact ⟨m0, ms, rfl⟩
  have hid0 : memberId (go!"http://" ++ m0.peer) d.token ∈ d.ids := by
    simp [Deployment.ids, hm0]
  have hbl : boot.length ≤ 64 := by
    rw [Hbc.boot.1, hperm.length_eq]
    simp only [Deployment.ids, List.length_map]
    unfold typed.maxMembers at hlen
    exact hlen
  iintro #Hreg Hs
  ihave Hs := addrs_members d.members $$ Hs
  ihave Hs := BigSepL.bigSepL_sep_eqv.1 $$ Hs
  icases Hs with ⟨Hp, Hc⟩
  ihave Hp := peers_cms d $$ Hp
  ihave Hc := clients_cms d $$ Hc
  imod (clusterAllocN (GF := GF) d.ids (distPs d) hperm _ hid0 (distCtxs d) boot Hbc (by omega) (by omega)
      .none (fun h => nomatch h) cmp cret)
    with ⟨%γ, %γk, %issued, %cnt, %wn, %fs, %gen, %idx, %cok, %rev, %reg, %Hγ, #Hf, Hsl, Hetcd⟩
  isimp only [ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte] at Hetcd
  imod (memberNames_alloc (GF := GF) d.ids Hd.idsNodup.1) with ⟨%ls, %au, %Hinj, Hnm⟩
  imod (peersAt_start γ (cmsD d)) $$ Hreg Hp with #Hpf
  imod (clientsAt_start (ClusterNames.view ⟨γ, γk, issued, cnt, wn, fs, gen, idx, cok, rev, reg, ls, au⟩) (cmsD d))
    $$ Hreg Hc with #Hcs
  imodintro
  iexists ⟨γ, γk, issued, cnt, wn, fs, gen, idx, cok, rev, reg, ls, au⟩
  isplitr
  · ipureintro
    exact Hγ.2.2.2.2.2.1
  isplitl [Hetcd]
  · iexact Hetcd
  isplitr
  · iexact Hcs
  iapply (memberShares_of d boot ⟨γ, γk, issued, cnt, wn, fs, gen, idx, cok, rev, reg, ls, au⟩ cmp cret Hγ Hcmp
    Hinj) $$ Hf Hpf Hsl Hcs Hnm

end start

end etcd_dist
end EtcdGrove
end Perennial

end
