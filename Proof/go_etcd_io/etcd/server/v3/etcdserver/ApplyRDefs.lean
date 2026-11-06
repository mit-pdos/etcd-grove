/-
**The restart window's vocabulary and the replay's hypothesized specs** (R2d' probe, A3–A5,
2026-11-06; DRAFT: nothing here is frozen, `notes/restart-plan.md`, "R2d' Scope (approved
2026-11-06)", its probe). Lean-first (no Rocq counterpart).

At the etcd pin `673da07c8`, a restarted member's `apply` (`server.go:1922-1972`) sees the committed
entries from Go's start index `σ.b + 1` on; those at or below the backend's consistent index `i`
(`shouldApplyV3 = e.Index > ConsistentIndex()`, `server.go:1940`) are replayed v2-only:
`applyEntryNormal(e, false)` returns after `apply.Apply` without `Trigger` (`server.go:2002-2005`),
`applyConfChange(cc, ep, false)` skips the validation (`membership/cluster.go:306-309`), raft
(`server.go:2053-2059`) and the membership's writes (`AddMember`, `membership/cluster.go:402-424`).
The apply thread's ghost rows (the KV model, the applied index, the rest buckets, the view) stay at
the ghost log `ghostOf rp G` (`RestReplay.lean`) while Go's rows walk `G`.

* `srvRestRp`: the rest buckets during the replay (the ghost table's leases, an image `r` that the
  replays change in memory only); `srvRestR`: the replay arm while Go is inside the window, else
  `srvRest` (a first start's: `srvRestR_first`).
* `kvBatchR`: `kvBatch` over Go's log, with the backend's log `A₀` committed and the batch's `v3`
  the model's past the window.
* the hypothesized per-entry specs (theorem arguments of the probe, not proved):
  `applyEntryNormal.specRepOff` and `applyConfChange.specRep`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.RestReplay
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvGoAttach
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApRes
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ApplyNormalOn

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.cindex
  go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The rest buckets during the replay** (R2d' A4, DRAFT): `srvRest`'s rows at the backend's
ghost log `A₀` (in a cluster that grants leases, its table's records, the lessor's half, the ids
ever), at an image `r` in place of `restModel` of `A₀`: the replayed entries change only the
in-memory members (`restEntryV2`; `apply/uber_applier.go:93-127` and `membership/cluster.go:467-496`
at the pin `673da07c8`, `UpdateAttributes(…, false)`). -/
def srvRestRp (E : apply.AEnv GF) (γr : ReadNames) (A₀ : List EntryModel) (r : apply.RestM) :
    IProp GF :=
  if E.lg then iprop(srvRestAt E (appliedTable γr A₀) r ∗ srvEver E A₀) else E.RO r

/-- **The image after Go's log `G` inside the window** (R2d' A4, DRAFT): the rest model of the
backend's log `A₀` (`cluster.Recover`'s members, `bootstrap.go:255-273` at the pin `673da07c8`),
the entries Go replayed since its start index (`G.drop rp.b`) replayed v2-only on it. -/
def restReplay (γr : ReadNames) (rp : RestartPt) (G : List EntryModel) : apply.RestM :=
  (G.drop rp.b).foldl (fun r m => restEntryV2 m r)
    (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ rp.A₀))

/-- **The apply thread's rest buckets after Go's log `G`** (R2d' A4, DRAFT): inside the window
(`|G| < |A₀|`), the replay arm at the backend's log; past it, `srvRest` at Go's log (the ghost log,
`ghostOf_past`). -/
def srvRestR (E : apply.AEnv GF) (γr : ReadNames) (rp : RestartPt) (G : List EntryModel) :
    IProp GF :=
  if G.length < rp.A₀.length then srvRestRp E γr rp.A₀ (restReplay γr rp G) else srvRest E γr G

/-- **The batch over Go's log** (R2d' A5, DRAFT; `kvBatch`'s window form): Go's log through the batch
and the backend's log committed, Go's start index at most `|G|` and Go's index `ai` at `G`; the
batch's `v3` (`c`, the effective consistent index) the model's (`c0`) past the window, the window's
entries at or below `c` (`bootstrap.go:255-273` restores `ci` to the backend's, at least its applied
index), the start's `c0` at most raft's first index (a fresh backend's `0`), and the backend's log's
entries normal or v1 conf changes (the shapes of the batches that applied them, `logShape`). -/
def kvBatchR (γr : ReadNames) (c ai : w64) (rp : RestartPt) (G ms : List EntryModel) : IProp GF :=
  iprop(srvRLogLb γr.raft (G ++ ms) ∗ srvRLogLb γr.raft rp.A₀ ∗
    ⌜uint.Z ai = uint.Z γr.raft.ai0 + G.length ∧ rp.b ≤ G.length ∧
      uint.Z γr.raft.ai0 + rp.A₀.length ≤ uint.Z c ∧ uint.Z γr.kv.c0 ≤ uint.Z γr.raft.ai0 ∧
      (∀ m ∈ rp.A₀, m.typ = W32 0 ∨ m.typ = W32 1) ∧
      ∀ m ∈ ms, uint.Z γr.raft.ai0 + rp.A₀.length < uint.Z m.index →
        (uint.Z c < uint.Z m.index ↔ uint.Z γr.kv.c0 < uint.Z m.index)⌝)

instance kvBatchR_persistent (γr : ReadNames) (c ai : w64) (rp : RestartPt) (G ms : List EntryModel) :
    Persistent (kvBatchR (GF := GF) γr c ai rp G ms) := by
  unfold kvBatchR; infer_instance

end defs

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **A first start's** rest buckets are lean's. -/
theorem srvRestR_first (E : apply.AEnv GF) (γr : ReadNames) (G : List EntryModel) :
    srvRestR E γr RestartPt.first G = srvRest E γr G := by
  unfold srvRestR; simp [RestartPt.first]

/-- Past the window, `srvRest` at Go's log. -/
theorem srvRestR_past (E : apply.AEnv GF) (γr : ReadNames) (rp : RestartPt) (G : List EntryModel)
    (h : rp.A₀.length ≤ G.length) : srvRestR E γr rp G = srvRest E γr G := by
  unfold srvRestR; rw [if_neg (by omega)]

/-- Inside the window, the replay arm. -/
theorem srvRestR_in (E : apply.AEnv GF) (γr : ReadNames) (rp : RestartPt) (G : List EntryModel)
    (h : G.length < rp.A₀.length) :
    srvRestR E γr rp G = srvRestRp E γr rp.A₀ (restReplay γr rp G) := by
  unfold srvRestR; rw [if_pos h]

/-- The replay arm at the model's image is `srvRest`. -/
theorem srvRestRp_model (E : apply.AEnv GF) (γr : ReadNames) (A : List EntryModel) :
    srvRestRp E γr A (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A)) = srvRest E γr A := by
  unfold srvRestRp srvRest; rfl

/-- One more replayed entry (Go's log one longer, past the start index). -/
theorem restReplay_snoc (γr : ReadNames) (rp : RestartPt) (G : List EntryModel) (m : EntryModel)
    (hb : rp.b ≤ G.length) :
    restReplay γr rp (G ++ [m]) = restEntryV2 m (restReplay γr rp G) := by
  unfold restReplay
  rw [List.drop_append_of_le_length hb, List.foldl_append]
  rfl

/-- A conf entry's replay is the identity (`ccRest false`). -/
theorem restEntryV2_conf (m : EntryModel) (r : apply.RestM) (h : m.typ ≠ W32 0) :
    restEntryV2 m r = r := by
  unfold restEntryV2
  rw [if_neg h]
  split <;> rfl

/-- The replay keeps the members' ids. -/
theorem restReplay_memKeys (γr : ReadNames) (rp : RestartPt) (G : List EntryModel) (k : w64) :
    ((restReplay γr rp G).mem !! k).isSome =
      ((restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ rp.A₀)).mem !! k).isSome := by
  unfold restReplay
  rw [fold_restEntryV2]
  show ((foldMem _ _).lookup k).isSome = (GMap.lookup _ k).isSome
  rw [foldMem_lookup]
  cases (GMap.lookup _ k) <;> rfl

/-- **The window closes on the model** (R2d' A2, DRAFT; `restReplay_close` over the server's facts):
once Go's log reaches the backend's (`G = A₀`), the replayed image is the rest model of `A₀`. The
facts: the server's log invariant (the bootstrap log, its peers distinct, the start at index `0`),
the boot members' URLs (`srvClusterOk`), the committed conf entries the server's
(`srv_committed_ccBoot`), the start's `c0` at most raft's first index, and the backend's log's
entries normal or v1 conf changes (`apply`'s `logShape` of the batches that applied them). -/
theorem restReplay_closeI (γr : ReadNames) (rp : RestartPt) (Em : CoPset) (hL : ↑srvLogN ⊆ Em)
    (hc0 : uint.Z γr.kv.c0 ≤ uint.Z γr.raft.ai0)
    (hty : ∀ m ∈ rp.A₀, m.typ = W32 0 ∨ m.typ = W32 1) :
    srvRaftLogInv (GF := GF) γr.raft ∗ srvRLogLb γr.raft rp.A₀ ⊢ |={Em}=>
      ⌜restReplay γr rp rp.A₀ = restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ rp.A₀)⌝ := by
  iintro ⟨#Hinv, #HA⟩
  ihave #Hinv2 := Hinv
  iunfold srvRaftLogInv at Hinv2
  icases Hinv2 with ⟨-, #Hcl, -, %Hai, %Hpre, #Hb, %Hok⟩
  iunfold srvClusterOk at Hcl
  icases Hcl with ⟨-, -, -, -, -, -, -, -, -, %Hurl⟩
  ihave %Hp := srvRLogLb_prefix γr.raft (γr.raft.raft.boot.map EntryModel.ofM) rp.A₀ $$ [Hb HA]
  · iframe Hb HA
  ihave #HA2 := HA
  iunfold srvRLogLb at HA2
  icases HA2 with ⟨#Hcl2, -⟩
  imod srv_committed_ccBoot γr.raft _ Em hL $$ [$Hinv $Hcl2] with %Hcc
  imodintro
  ipureintro
  have hai0 : uint.Z γr.raft.ai0 = 0 := by rw [Hai, Hpre]; rfl
  have hc00 : γr.kv.c0 = W64 0 := by word
  -- each entry of `A₀`'s conf changes the server's
  have hccA : ∀ m ∈ rp.A₀, m.typ ≠ W32 0 → ∀ cc, ccDecodeV1 m.data = some cc →
      ccApplyOk (GMap.listToSet γr.raft.raft.vs) cc := by
    intro m hm ht cc hd
    have h1 : m.typ = W32 1 := (hty m hm).resolve_left ht
    have hin : m.toLE ∈ srvLE γr.raft rp.A₀ := by
      unfold srvLE; rw [Hpre, List.nil_append]; exact List.mem_map_of_mem hm
    exact Hcc _ hin h1 cc hd
  unfold restReplay
  rw [Hpre, List.nil_append, hc00]
  rcases Hp with ⟨R, hR⟩ | hpb
  · -- past the bootstrap log
    rw [← hR]
    obtain ⟨hne, hnd, hbo⟩ := Hok
    refine restReplay_close γr.raft.raft.vs γr.raft.raft.boot R rp.b hbo hnd Hurl ?_ ?_
    · intro e he cc hd
      have hm : EntryModel.ofM e ∈ rp.A₀ := by
        rw [← hR]; exact List.mem_append_left _ (List.mem_map_of_mem he)
      obtain ⟨k, hk⟩ := List.getElem?_of_mem he
      have hty1 := (hbo.2.2 k e hk).2.2.1
      exact hccA _ hm (by simp only [EntryModel.ofM, hty1]; decide) cc hd
    · intro m hm ht cc hd
      exact hccA m (by rw [← hR]; exact List.mem_append_right _ hm) ht cc hd
  · -- inside the bootstrap log: every entry a conf change, whose replay is the identity
    obtain ⟨-, -, hbo⟩ := Hok
    have hall : ∀ m ∈ rp.A₀.drop rp.b, m.typ ≠ W32 0 := by
      intro m hm
      have hm' : m ∈ γr.raft.raft.boot.map EntryModel.ofM :=
        hpb.subset (List.mem_of_mem_drop hm)
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hm'
      obtain ⟨k, hk⟩ := List.getElem?_of_mem he
      have hty1 := (hbo.2.2 k e hk).2.2.1
      simp only [EntryModel.ofM, hty1]; decide
    generalize rp.A₀.drop rp.b = S at hall
    induction S with
    | nil => rfl
    | cons m S ih =>
      rw [List.foldl_cons, restEntryV2_conf m _ (hall m (List.mem_cons_self ..))]
      exact ih (fun m' hm' => hall m' (List.mem_cons_of_mem _ hm'))

/-- **The apply thread's membership resource at a replayed `AddNode`** (R2d' A4, DRAFT): the fields
`applyConfChange(cc, ep, false)` reads (`server.go:2037-2083` at the pin `673da07c8`: `beHooks`,
the cluster, the transport, the member id), the node a peer unless the local member (it is a voter:
`ccApplyOk`, `srvPeersCover`), and the resource back at the same log (a replay does not move the
ghost log, and `AddPeer` of a known peer keeps the peers). -/
theorem srvApRes_ccRep (s : Loc) (γr : ReadNames) (A : List EntryModel) (cm : ConfChangeM)
    (hok : ccApplyOkM γr.raft cm) :
    srvApRes (GF := GF) s γr A ⊢
      ∃ (bh : Loc) (ix : GoInterfaceOk) (lgh tl : Loc) (lid : w64) (cl lgc : Loc) (cid : w64)
        (prs : trIds),
        srvBeHooksAddr s ↦□ bh ∗ storage.isBackendHooks bh ix lgh ∗
        srvTransportAddr s ↦□ srvTrIface tl ∗ srvMemberIDAddr s ↦□ lid ∗
        srvClusterAddr s ↦□ cl ∗ membership.rcLgAddr cl ↦□ lgc ∗ ⌜lgc ≠ null⌝ ∗
        membership.rcCidAddr cl ↦□ cid ∗ ccMembRes γr.raft cl tl lid prs ∗
        ⌜cm.nodeId ≠ lid → cm.nodeId ∈ prs⌝ ∗
        (ccMembRes γr.raft cl tl lid prs -∗ srvApRes s γr A) := by
  unfold srvApRes
  iintro ⟨%bh, %ix, %lgh, %tl, %lid, %cl, %lgc, %cid, %prs, #H1, #H2, #H3, #H4, #H5, #H6,
    %H7, #H8, Hmr, %Hp, #Hd⟩
  iexists bh, ix, lgh, tl, lid, cl, lgc, cid, prs
  iframe H1 H2 H3 H4 H5 H6 H8 Hmr
  isplitr
  · ipureintro; exact H7
  isplitr
  · ipureintro
    intro hne
    exact Hp.1 _ hok.2.1 hne
  iintro Hmr
  iexists bh, ix, lgh, tl, lid, cl, lgc, cid, prs
  iframe H1 H2 H3 H4 H5 H6 H8 Hmr Hd
  ipureintro; exact ⟨H7, Hp⟩

end laws

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`s.applyEntryNormal(e, false)`, a replay** (R2d' A5, DRAFT, HYPOTHESIZED: the probe takes it
as an argument; with auth off). At the pin `673da07c8` (`server.go:1975-2005`): no deferred
`SetConsistentIndex` (`shouldApplyV3` false); an empty entry notifies `firstCommitInTerm` and may
promote the lessor; otherwise `apply.Apply(…, false)` dispatches v2-only (`apply/uber_applier.go:93-
127`) and the function returns before `Trigger`. So the KV and the applied index are untouched
(`entryStep m false`, which keeps the state, `apply.apply_no_v3_no_write`), and the rest buckets'
image goes to `restEntryV2 m r` (the attribute write in memory); the attribute's member is a voter
(`entryWaitOk`'s `attrEntryOk`), which the image's members include (Go's `UpdateAttributes` panics on
an unknown, unremoved member, `membership/cluster.go:467-496`). The entry at or below the effective
consistent index; the store's write token spent (`apply.Apply`'s). -/
abbrev EtcdServer.applyEntryNormal.specRepOff : Prop :=
  ∀ (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF) (ρ : ReqNames)
    (b : GoInterface) (e : Loc) (m : EntryModel) (st : ApplyState) (x : apply.ApplyKV)
    (γr : ReadNames) (A₀ : List EntryModel) (r : apply.RestM),
  E.authOn = false →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServer s γ ci TM E ρ γr ∗ entryWaitOk ρ E m ∗ entryAt e m ∗ applyThread γ st ∗
      applyBackend γ ci b ∗ srvLgReader s ∗ srvGoRes s ∗ srvApplyKV s E ρ.wait x ∗
      mvcc.storeWT E.γ ∗ srvFS s ∗ committedAtLeast γr m.index ∗ srvRestRp E γr A₀ r ∗
      ⌜st.pending = false ∧ entryOk E.lm x m ∧ m.typ = W32 0 ∧
        uint.Z m.index ≤ uint.Z (ciEff γ st.k) ∧
        ∀ k, k ∈ γr.raft.raft.cfg → (r.mem !! k).isSome = true⌝ }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"applyEntryNormal"))
      (Val #e)) (Val #false))
  {{ RET #(); applyBackend γ ci b ∗ srvLgReader s ∗ srvGoRes s ∗ srvFS s ∗
      (∃ (x' : apply.ApplyKV) (out : apply.ApplyOut), srvApplyKV s E ρ.wait x' ∗
        ⌜entryStep m false x x' out⌝) ∗
      srvRestRp E γr A₀ (restEntryV2 m r) ∗ applyThread γ st }}

/-- **`s.applyConfChange(cc, ep, false)`, a replayed `AddNode`** (R2d' A5, DRAFT, HYPOTHESIZED: the
probe takes it as an argument). At the pin `673da07c8` (`server.go:2037-2083`): the validation passes
without reading (`membership/cluster.go:306-309`), raft is not called and `ep.confState` is kept
(`server.go:2053-2059`), `beHooks.SetConfState(ep.confState)`, the context unmarshalled and checked
against the node (`ccApplyOkM`: it unmarshals to the node's member), `AddMember(…, false)` only logs
(`membership/cluster.go:416-424`), and `AddPeer` of the node unless it is the local member (a known
peer: `AddPeer_known`). It returns `removed = false`; it writes no backend bucket and no member in
memory (`ccRest false` is the identity). -/
abbrev EtcdServer.applyConfChange.specRep : Prop :=
  ∀ (s cc ep : Loc) (m : ConfChangeM) (cs : Loc) (γs : ServerRaftNames) (cl lg bh : Loc)
    (ix : GoInterfaceOk) (lgh tl : Loc) (lid : w64) (prs : trIds) (lgc : Loc) (cid : w64),
  ccApplyOkM γs m → (m.nodeId ≠ lid → m.nodeId ∈ prs) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvLgAddr s ↦□ lg ∗ ⌜lg ≠ null⌝ ∗ srvLgReader s ∗
      srvClusterAddr s ↦□ cl ∗ membership.rcLgAddr cl ↦□ lgc ∗ ⌜lgc ≠ null⌝ ∗
      membership.rcCidAddr cl ↦□ cid ∗
      ownConfChange cc (DFrac.own 1) m ∗ epConfState ep cs ∗
      srvBeHooksAddr s ↦□ bh ∗ storage.isBackendHooks bh ix lgh ∗
      srvTransportAddr s ↦□ srvTrIface tl ∗ srvMemberIDAddr s ↦□ lid ∗
      ccMembRes γs cl tl lid prs }}
    (App (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"applyConfChange"))
      (Val #cc)) (Val #ep)) (Val #false))
  {{ (removed : Bool) (err : GoInterface), RET (PairV #removed #err);
      ⌜removed = false⌝ ∗ srvLgReader s ∗
      (∃ m' : ConfChangeM, ownConfChange cc DFrac.discard m' ∗ ⌜m'.id = m.id⌝) ∗
      epConfState ep cs ∗ ccMembRes γs cl tl lid prs }}

end spec

end EtcdGrove
end Perennial
